#include "cfg.h"
#include "product.h"
#include "s-expr.h"
#include "solver.h"
#include "symbolic-execution.h"

#include <chrono>
#include <deque>
#include <fstream>
#include <iostream>
#include <map>
#include <set>
#include <sstream>

struct solver_feasibility_checker : public feasibility_checker {
  bool is_feasible(const std::vector<std::string>& definitions, const std::vector<std::string>& constraints) override {
    std::stringstream ss;
    for (const auto& def : definitions) {
      ss << "(define " << def << ")" << std::endl;
    }
    for (const auto& constraint : constraints) {
      ss << "(assert " << constraint << ")" << std::endl;
    }
    ss << "(check)" << std::endl;
    ss << "(exit)" << std::endl;
    //std::cout << *s_expr::parse("(" + ss.str() + ")") << std::endl;
    auto output = solve(*s_expr::parse_multiple(ss.str()), false);
    if (const auto model = destructure<"sat", rest>(output)) {
      //std::cout << "feasible!" << std::endl;
      return true;
    } else if (destructure<"unsat">(output)) {
      //std::cout << "not feasible!" << std::endl;
      return false;
    } else {
      std::cerr << "Unexpected output: " << std::move(output) << std::endl;
      assert(false);
    }
  }
};

int main(int argc, char** argv) {
  if (argc != 2) {
    return 1;
  }

  std::ifstream stream(argv[1]);
  if (!stream) {
    std::cerr << "Failed to open " << argv[1] << std::endl;
    return 1;
  }
  std::string input(std::istreambuf_iterator<char>(stream), {});

  auto exprs = s_expr::parse_multiple(input);
  if (!exprs) {
    std::cerr << "Syntax error" << std::endl;
    return 1;
  }

  struct algo_stats {
    bool outcome = 0;
    size_t max_obs = 0;
    size_t n_total_univ_paths = 0;
    size_t n_last_exist_paths = 0;
    size_t n_total_exist_paths = 0;
    std::chrono::high_resolution_clock::duration duration;
  };
  std::optional<algo_stats> last_outcome;
  size_t min_obs = 1;
  std::optional<size_t> max_obs;
  std::map<std::string_view, std::shared_ptr<program>> programs;
  for (const auto& expr : *exprs) {
    //std::cout << expr << std::endl;
    if (expr.is_atom()) {
      std::cerr << "Unexpected atom: " << expr << std::endl;
      return 1;
    }
    const auto& list = expr.as_list();
    if (list.size() == 0) {
      std::cerr << "Unexpected empty list" << std::endl;
      return 1;
    }
    if (const auto strategy = destructure<"strategy", const s_expr_list&>(list)) {
      const auto& [obs] = *strategy;
      if (const auto obs_spec = destructure<"observations", rest>(obs)) {
        const auto& [params] = *obs_spec;
        bool min_set = false, max_set = false;
        min_obs = 1;
        max_obs.reset();
        for (auto it = params.begin(); it != params.end(); it++) {
          bool setting_min = false, setting_max = false;
          std::string value;
          if (it->is_atom()) {
            setting_min = setting_max = true;
            value = it->as_atom();
          } else if (const auto m = destructure<"min", const atom&>(it->as_list())) {
            setting_min = true;
            value = std::get<0>(*m);
          } else if (const auto m = destructure<"max", const atom&>(it->as_list())) {
            setting_max = true;
            value = std::get<0>(*m);
          } else {
            std::cerr << "Invalid strategy specification: " << expr << std::endl;
            return 1;
          }
          if (setting_min) {
            if (min_set) {
              std::cerr << "Invalid strategy specification: " << expr << std::endl;
              return 1;
            }
            min_set = true;
            min_obs = std::stoul(value);
          }
          if (setting_max) {
            if (max_set) {
              std::cerr << "Invalid strategy specification: " << expr << std::endl;
              return 1;
            }
            max_set = true;
            max_obs = std::stoul(value);
          }
        }
      } else {
        std::cerr << "Invalid strategy specification: " << expr << std::endl;
        return 1;
      }
      if (min_obs == 0 || (max_obs.has_value() && max_obs < min_obs)) {
        std::cerr << "Invalid strategy: number of observations cannot be 0" << std::endl;
        return 1;
      } else if (max_obs.has_value() && max_obs < min_obs) {
        std::cerr << "Invalid strategy: maximum " << max_obs.value() << " exceeds minimum " << min_obs << std::endl;
        return 1;
      }
    } else if (const auto fc = destructure<"find-counterexample", const s_expr&>(list)) {
      std::vector<std::pair<std::shared_ptr<program>, std::string_view>> forall_traces;
      std::vector<std::pair<std::shared_ptr<program>, std::string_view>> exists_traces;

      const auto& [full_spec] = *fc;
      const s_expr* spec_inner = &full_spec;

      while (spec_inner->is_list()) {
        if (const auto forall = destructure<"forall", const s_expr_list&, const s_expr&>(spec_inner->as_list())) {
          const auto& [trace_spec, next_inner] = *forall;
          const auto traces = destructure<"traces", const atom&, optional_atom_ref>(trace_spec);
          if (!traces) {
            std::cerr << "Unexpected input: " << *spec_inner << std::endl;
            return 1;
          }
          const auto& [program_name, maybe_traces_name] = *traces;
          const auto& program = programs.at(program_name);
          const auto& traces_name = maybe_traces_name ? maybe_traces_name->get() : program_name;
          forall_traces.push_back({program, traces_name});
          spec_inner = &next_inner;
        } else {
          break;
        }
      }

      while (spec_inner->is_list()) {
        if (const auto exists = destructure<"exists", const s_expr_list&, const s_expr&>(spec_inner->as_list())) {
          const auto& [trace_spec, next_inner] = *exists;
          const auto traces = destructure<"traces", const atom&, optional_atom_ref>(trace_spec);
          if (!traces) {
            std::cerr << "Unexpected input: " << *spec_inner << std::endl;
            return 1;
          }
          const auto& [program_name, maybe_traces_name] = *traces;
          const auto& program = programs.at(program_name);
          const auto& traces_name = maybe_traces_name ? maybe_traces_name->get() : program_name;
          exists_traces.push_back({program, traces_name});
          spec_inner = &next_inner;
        } else {
          break;
        }
      }

      const s_expr& spec = *spec_inner;

      std::set<std::string_view> forall_trace_names;
      std::transform(forall_traces.begin(), forall_traces.end(), std::inserter(forall_trace_names, forall_trace_names.begin()), [](const auto& p) { return p.second; });

      std::set<std::string_view> exists_trace_names;
      std::transform(exists_traces.begin(), exists_traces.end(), std::inserter(exists_trace_names, exists_trace_names.begin()), [](const auto& p) { return p.second; });

      for (const auto& name : forall_trace_names) {
        if (exists_trace_names.contains(name)) {
          std::cerr << "Duplicate trace name: " << name << std::endl;
          return 1;
        }
      }

      std::vector<std::shared_ptr<program>> forall_programs;
      std::transform(forall_traces.begin(), forall_traces.end(), std::back_inserter(forall_programs), [](const auto& p) { return p.first; });

      std::shared_ptr<program> forall_program = compute_product(forall_programs);

      std::vector<std::shared_ptr<program>> exists_programs;
      std::transform(exists_traces.begin(), exists_traces.end(), std::back_inserter(exists_programs), [](const auto& p) { return p.first; });

      std::shared_ptr<program> exists_program = compute_product(exists_programs);

      var_scopes program_vars;
      extend_var_mapping(program_vars, forall_traces, forall_program);
      extend_var_mapping(program_vars, exists_traces, exists_program);
      program_vars.add_shortcuts();

      // We want to build the following input:
      //
      //     (define existentially quantified variables...)
      //     (existential constraints...)
      //     (assert (forall (universally quantified variables...)
      //       (for each universal path
      //         (universal constraints...) -> (property))))

      algo_stats result;
      const auto start_time = std::chrono::high_resolution_clock::now();
      solver_feasibility_checker feasibility;
      bool terminated = false;
      for (size_t n_obs = min_obs; !terminated && !result.outcome && (max_obs.has_value() ? n_obs <= max_obs.value() : true); n_obs++) {
        terminated = true;
        result.max_obs = n_obs;
        unwind_one_by_one(*forall_program, n_obs, "exist", feasibility, [&](const std::vector<std::string>& definitions, const std::vector<std::string>& constraints, auto obs_value_exist) {
          if (terminated) terminated = false;
          result.n_total_univ_paths++;

          std::stringstream ss;
          for (const auto& def : definitions) {
            ss << "(define " << def << ")" << std::endl;
          }
          for (const auto& constraint : constraints) {
            ss << "(assert " << constraint << ")" << std::endl;
          }

          std::set<std::string> universal_defs;
          std::vector<std::string> path_formulas;
          result.n_last_exist_paths = 0;
          unwind_one_by_one(*exists_program, n_obs, "univ", feasibility, [&](const std::vector<std::string>& definitions, const std::vector<std::string>& constraints, auto obs_value_univ) {
            result.n_last_exist_paths++;
            for (const auto& def : definitions) {
              universal_defs.insert(def);
            }
            std::string formula = "(=> ";
            if (constraints.empty()) {
              formula += "true";
            } else {
              formula += "(and";
              for (const auto& constraint : constraints) {
                formula += " " + constraint;
              }
              formula += ")";
            }
            formula += " (or";
            for (size_t obs_index = 0; obs_index < n_obs; obs_index++) {
              std::function<std::string(const s_expr&)> instantiate_formula = [&](const s_expr& formula_or_trivial) -> std::string {
                if (formula_or_trivial.is_atom()) {
                  const atom& trivial = formula_or_trivial.as_atom();
                  if (trivial == "true") return "true";
                  if (trivial == "false") return "false";
                  std::cerr << "Unexpected formula: " << formula_or_trivial << std::endl;
                  return "???";
                }

                const s_expr_list& formula = formula_or_trivial.as_list();
                std::function<std::string(const s_expr&)> value = [&](const s_expr& expr) -> std::string {
                  if (expr.is_atom()) {
                    std::string_view name = expr.as_atom();
                    // Simplistic support for integer constants.
                    if (name.find_first_not_of("0123456789") == std::string::npos) {
                      return std::string(name);
                    }
                    const auto scope = program_vars.shortcuts().find(name);
                    if (scope == program_vars.shortcuts().end()) {
                      std::cerr << "Unknown or ambiguous variable: " << expr << std::endl;
                      return "???";
                    }
                    const auto entry = program_vars.entries().find({scope->second, name});
                    assert(entry != program_vars.entries().end());
                    if (entry->second.first == forall_program) {
                      return obs_value_exist(entry->second.second.name(), obs_index).value_or("???");
                    } else {
                      assert(entry->second.first == exists_program);
                      return obs_value_univ(entry->second.second.name(), obs_index).value_or("???");
                    }
                  } else if (const auto trace_val = destructure<"trace-value", const atom&, const atom&>(expr.as_list())) {
                    const auto& [trace_ref, var_name] = *trace_val;
                    const auto entry = program_vars.entries().find({trace_ref, var_name});
                    if (entry == program_vars.entries().end()) {
                      std::cerr << "Unknown or ambiguous variable: " << expr << std::endl;
                      return "???";
                    }
                    assert(entry->first.first == trace_ref);
                    assert(entry->first.second == var_name);
                    if (forall_trace_names.contains(entry->first.first)) {
                      return obs_value_exist(entry->second.second.name(), obs_index).value_or("???");
                    } else {
                      assert(exists_trace_names.contains(entry->first.first));
                      return obs_value_univ(entry->second.second.name(), obs_index).value_or("???");
                    }
                  } else if (const auto add = destructure<"+", const s_expr&, const s_expr&>(expr.as_list())) {
                    const auto& [left, right] = *add;
                    return "(+ " + value(left) + " " + value(right) + ")";
                  } else if (const auto sub = destructure<"-", const s_expr&, const s_expr&>(expr.as_list())) {
                    const auto& [left, right] = *sub;
                    return "(- " + value(left) + " " + value(right) + ")";
                  } else if (const auto neg = destructure<"-", const s_expr&>(expr.as_list())) {
                    const auto& [operand] = *neg;
                    return "(- " + value(operand) + ")";
                  } else {
                    std::cerr << "Unexpected expression: " << expr << std::endl;
                    return "???";
                  }
                };
                if (const auto eq = destructure<"=", const s_expr&, const s_expr&>(formula)) {
                  const auto& [a, b] = *eq;
                  return "(= " + value(a) + " " + value(b) + ")";
                } else if (const auto neq = destructure<"/=", const s_expr&, const s_expr&>(formula)) {
                  const auto& [a, b] = *neq;
                  return "(/= " + value(a) + " " + value(b) + ")";
                } else if (const auto lt = destructure<"<", const s_expr&, const s_expr&>(formula)) {
                  const auto& [a, b] = *lt;
                  return "(< " + value(a) + " " + value(b) + ")";
                } else if (const auto le = destructure<"<=", const s_expr&, const s_expr&>(formula)) {
                  const auto& [a, b] = *le;
                  return "(<= " + value(a) + " " + value(b) + ")";
                } else if (const auto gt = destructure<">", const s_expr&, const s_expr&>(formula)) {
                  const auto& [a, b] = *gt;
                  return "(> " + value(a) + " " + value(b) + ")";
                } else if (const auto ge = destructure<">=", const s_expr&, const s_expr&>(formula)) {
                  const auto& [a, b] = *ge;
                  return "(>= " + value(a) + " " + value(b) + ")";
                } else if (const auto divided = destructure<"divided-by", const s_expr&, const s_expr&>(formula)) {
                  const auto& [a, b] = *divided;
                  return "(divides " + value(b) + " " + value(a) + ")";
                } else if (const auto conj = destructure<"and", rest>(formula)) {
                  const auto& [operands] = *conj;
                  std::string ret = "(and";
                  for (auto it = operands.begin(); it != operands.end(); it++) {
                    ret += " " + instantiate_formula(*it);
                  }
                  return ret + ")";
                } else if (const auto disj = destructure<"or", rest>(formula)) {
                  const auto& [operands] = *disj;
                  std::string ret = "(or";
                  for (auto it = operands.begin(); it != operands.end(); it++) {
                    ret += " " + instantiate_formula(*it);
                  }
                  return ret + ")";
                } else if (const auto impl = destructure<"=>", const s_expr&, const s_expr&>(formula)) {
                  const auto& [a, b] = *impl;
                  return "(=> " + instantiate_formula(a) + " " + instantiate_formula(b) + ")";
                } else if (const auto impl = destructure<"<=>", const s_expr&, const s_expr&>(formula)) {
                  const auto& [a, b] = *impl;
                  return "(<=> " + instantiate_formula(a) + " " + instantiate_formula(b) + ")";
                } else {
                  std::cerr << "Unexpected formula: " << formula_or_trivial << std::endl;
                  return "???";
                }
              };
              formula += " (not " + instantiate_formula(spec) + ")";
            }
            formula += "))";
            path_formulas.push_back(std::move(formula));
            return true;
          });
          result.n_total_exist_paths += result.n_last_exist_paths;

          ss << "(assert (forall (";
          for (const auto& def : universal_defs) {
            if (def != *universal_defs.begin()) ss << " ";
            ss << def;
          }
          if (universal_defs.empty()) {
            ss << "dummy_var::int";
          }
          ss << ")" << std::endl;
          if (path_formulas.empty()) {
            ss << "    true";
          } else {
            ss << "    (and";
            for (const auto& path_formula : path_formulas) {
              ss << std::endl << "      " << path_formula;
            }
            ss << ")";
          }
          ss << "))" << std::endl;
          ss << "(ef-solve)" << std::endl;
          ss << "(show-model)" << std::endl;
          ss << "(exit)" << std::endl;
          //std::cout << ss.str() << std::endl;
          auto output = solve(*s_expr::parse_multiple(ss.str()), true);
          if (const auto model = destructure<"sat", rest>(output)) {
            //std::cout << "Counterexample found" << std::endl;
            //std::cout << s_expr(s_expr_list {output}) << std::endl;
            result.outcome = true;
            return false;
          } else if (const auto unsat = destructure<"unsat">(output)) {
            //std::cout << "No counterexample found" << std::endl;
            return true;
          } else {
            std::cerr << "Unexpected output: " << std::move(output) << std::endl;
            return false;
          }
        });
      }
      const auto end_time = std::chrono::high_resolution_clock::now();
      result.duration = end_time - start_time;
      last_outcome = std::move(result);
    } else if (const auto dp = destructure<"define-program", const atom&, rest>(list)) {
      const auto& [name, body] = *dp;
      auto p = program::parse(body.begin(), body.end());
      if (programs.contains(name)) {
        std::cerr << "Duplicate program identifier: " << name << std::endl;
        return 1;
      }
      programs.insert({std::string_view(name), std::make_shared<program>(std::move(p))});
    } else if (const auto expect = destructure<"expect", const s_expr_list&>(list)) {
      const auto& [spec] = *expect;
      if (const auto outcome = destructure<"outcome", const atom&>(spec)) {
        const auto& [expected_outcome] = *outcome;
        if (!last_outcome) {
          std::cerr << "Cannot expect outcome without running algorithm first" << std::endl;
          return 1;
        }
        const char* actual_outcome = last_outcome->outcome ? "counterexample" : "no-counterexample";
        if (expected_outcome != actual_outcome) {
          std::cerr << "Expected: " << list[1] << std::endl;
          std::cerr << "Computed: (outcome " << actual_outcome << ")" << std::endl;
          return 1;
        }
      } else if (const auto cfg = destructure<"control-flow-graph", const s_expr&, rest>(spec)) {
        const auto& prog_ref = std::get<0>(*cfg);
        std::function<std::shared_ptr<program>(const s_expr&)> resolve_prog_ref = [&](const s_expr& ref) -> std::shared_ptr<program> {
          if (ref.is_atom()) {
            return programs.at(ref.as_atom());
          } else if (const auto product = destructure<"product", rest>(ref.as_list())) {
            std::vector<std::shared_ptr<program>> args;
            const auto& refs = std::get<0>(*product);
            for (auto it = refs.begin(); it != refs.end(); it++) {
              args.push_back(resolve_prog_ref(*it));
            }
            return compute_product(args);
          } else {
            std::cerr << "Unknown program reference: " << ref << std::endl;
            assert(false);
          }
        };
        s_expr actual = resolve_prog_ref(prog_ref)->to_s_expr(prog_ref);
        if (list[1] != actual) {
          std::cerr << "Expected: " << list[1] << std::endl;
          std::cerr << "Computed: " << actual << std::endl;
          return 1;
        }
      } else {
        std::cerr << "Unknown test assertion: " << expr << std::endl;
        return 1;
      }
    } else if (destructure<"print-stats">(list)) {
      if (!last_outcome) {
        std::cerr << "Cannot print stats without running algorithm first" << std::endl;
        return 1;
      }
      const auto& last = *last_outcome;
      std::cout << "{\"counterexample\":" << (last.outcome ? "true" : "false") << ",\"max_obs\":" << last.max_obs << ",\"total_univ_paths\":" << last.n_total_univ_paths << ",\"total_exist_paths\":" << last.n_total_exist_paths << ",\"last_exist_paths\":" << last.n_last_exist_paths << ",\"duration_us\":" << std::chrono::duration_cast<std::chrono::microseconds>(last.duration).count() << "}" << std::endl;
    } else {
      std::cerr << "Unknown command: " << expr << std::endl;
      return 1;
    }
  }

  return 0;
}
