#pragma once

#include "cfg.h"

#include <cassert>
#include <functional>

class stack_entry {
public:
  stack_entry(const stack_entry& other) = default;
  stack_entry& operator=(const stack_entry& other) = default;

  const outgoing_edge& edge() const { return *edge_; }

  bool& taken() { return taken_; }
  bool taken() const { return taken_; }

  size_t& n_prev_obs() { return n_prev_obs_; }
  size_t n_prev_obs() const { return n_prev_obs_; }

  size_t& n_prev_defs() { return n_prev_defs_; }
  size_t n_prev_defs() const { return n_prev_defs_; }

  size_t& n_prev_constraints() { return n_prev_constraints_; }
  size_t n_prev_constraints() const { return n_prev_constraints_; }

  static stack_entry init(const program& program) {
    return {&program.init()};
  }

  stack_entry next(const outgoing_edge* edge) {
    stack_entry entry = *this;
    entry.edge_ = edge;
    entry.taken_ = true;
    return entry;
  }

private:
  stack_entry(const outgoing_edge* edge) : edge_(edge) {}

  const outgoing_edge* edge_;
  bool taken_ = true;
  size_t n_prev_obs_ = 0;
  size_t n_prev_defs_ = 0;
  size_t n_prev_constraints_ = 0;
};

struct feasibility_checker {
  virtual bool is_feasible(const std::vector<std::string>& definitions, const std::vector<std::string>& constraints) = 0;
};

template <typename F>
static void unwind_one_by_one(const program& program, size_t n_obs_needed, const std::string& prefix, feasibility_checker& c, F&& f) {
  // This stack tracks branching decisions as well as how many definitions,
  // assignments, constraints, and observation points occurred before each
  // conditional branch.
  std::deque<stack_entry> stack;

  // Variable values and non-deterministic values. Every time a value is
  // assigned to a variable, we create a new definition.
  std::vector<std::string> definitions;
  // For each definition, we track which variable is being assigned. If the
  // definition is for a non-deterministic value and not a variable assignment,
  // the assignment will be a nullptr.
  std::vector<const var_decl*> assignments;
  // Path constraints and variable equations.
  std::vector<std::string> constraints;
  // Observation points are tracked using the number of definitions prior to the
  // respective observation point. This is sufficient for identifying relevant
  // constraints and variable assignments.
  std::vector<size_t> observation_points;

  auto count_assignments = [&](const var_decl* var) -> size_t {
    size_t index = 0;
    for (size_t i = 0; i < definitions.size(); i++) {
      if (assignments[i] == var) {
        index++;
      }
    }
    return index;
  };

  auto instantiate_var_value = [&](const var_decl& var) -> std::string {
    return prefix + "_" + var.name() + "_" + std::to_string(count_assignments(&var) - 1);
  };

  auto instantiate_atomic = [&](const atomic& atomic) -> std::string {
    return std::holds_alternative<constant>(atomic) ? std::to_string(std::get<constant>(atomic).value()) : instantiate_var_value(std::get<std::reference_wrapper<const var_decl>>(atomic).get());
  };

  auto instantiate_condition = [&](const comparison& cond, bool taken) -> std::string {
    std::string op1 = instantiate_var_value(cond.op1());
    std::string op2 = instantiate_atomic(cond.op2());
    std::string op;
    switch (cond.kind()) {
      case comparison::kind::EQ:
        op = taken ? "=" : "/=";
        break;
      case comparison::kind::NEQ:
        op = taken ? "/=" : "=";
        break;
      case comparison::kind::LT:
        op = taken ? "<" : ">=";
        break;
      case comparison::kind::LE:
        op = taken ? "<=" : ">";
        break;
      case comparison::kind::GT:
        op = taken ? ">" : "<=";
        break;
      case comparison::kind::GE:
        op = taken ? ">=" : "<";
        break;
      case comparison::kind::DIVIDED_BY:
        {
          std::string divides = "(divides " + op2 + " " + op1 + ")";
          return taken ? divides : "(not " + divides + ")";
        }
      default:
        __builtin_unreachable();
    }

    return "(" + op + " " + op1 + " " + op2 + ")";
  };

  std::function<std::string(const arith_expr&, size_t&, size_t&)> instantiate_arith_expr = [&](const arith_expr& expr, size_t& n_nondet, size_t& n_constraints) -> std::string {
    if (const auto* nd = std::get_if<nondet_value>(&expr)) {
      std::string name = "nondet_" + prefix + "_" + std::to_string(n_nondet);
      definitions.push_back(name + "::int");
      assignments.push_back(nullptr);
      if (nd->min().has_value()) {
        constraints.push_back("(>= " + name + " " + std::to_string(nd->min().value()) + ")");
        n_constraints++;
      }
      if (nd->max().has_value()) {
        constraints.push_back("(<= " + name + " " + std::to_string(nd->max().value()) + ")");
        n_constraints++;
      }
      return "nondet_" + prefix + "_" + std::to_string(n_nondet++);
    } else if (std::holds_alternative<atomic>(expr)) {
      return instantiate_atomic(std::get<atomic>(expr));
    } else if (std::holds_alternative<std::unique_ptr<bin_arith_expr>>(expr)) {
      const auto& bin = std::get<std::unique_ptr<bin_arith_expr>>(expr);
      std::string op;
      switch (bin->kind()) {
        case bin_arith_expr::kind::ADD:
          op = "+";
          break;
        case bin_arith_expr::kind::SUB:
          op = "-";
          break;
        case bin_arith_expr::kind::MUL:
          op = "*";
          break;
        default:
          __builtin_unreachable();
      }
      return "(" + op + " " + instantiate_arith_expr(bin->left_operand(), n_nondet, n_constraints) + " " + instantiate_arith_expr(bin->right_operand(), n_nondet, n_constraints) + ")";
    } else if (std::holds_alternative<std::unique_ptr<unary_arith_expr>>(expr)) {
      const auto& unary = std::get<std::unique_ptr<unary_arith_expr>>(expr);
      return "(- " + instantiate_arith_expr(unary->operand(), n_nondet, n_constraints) + ")";
    } else {
      assert(false);
    }
  };

  stack.push_back(stack_entry::init(program));
  while (!stack.empty()) {
    size_t n_constraints = stack.back().n_prev_constraints();
    assert(constraints.size() == n_constraints);

    // Expand any conditional branches until we reach another block.
    while (!std::holds_alternative<unconditional_edge>(stack.back().edge())) {
      const auto& cond = std::get<std::unique_ptr<conditional_branch>>(stack.back().edge());
      if (!std::holds_alternative<nondet_condition>(cond->condition())) {
        constraints.push_back(instantiate_condition(std::get<comparison>(cond->condition()), stack.back().taken()));
        n_constraints++;
        assert(n_constraints == constraints.size());

        // We have added a new constraint, which might have made the path infeasible.
        if (!c.is_feasible(definitions, constraints)) {
          if (stack.back().taken()) {
            // If the additional constraint made the path infeasible, then its negation should keep
            // the path feasible, so we don't need to check feasibility again.
            stack.back().taken() = false;
            constraints[constraints.size() - 1] = instantiate_condition(std::get<comparison>(cond->condition()), stack.back().taken());
          } else {
            // We cannot invert the condition anymore to construct a new path, so we need to pop the stack.
            while (!stack.empty() && (std::holds_alternative<unconditional_edge>(stack.back().edge()) || !stack.back().taken())) {
              stack.pop_back();
            }
            if (stack.empty()) return; // TODO: this control flow is really not great
            assert(stack.back().n_prev_constraints() < n_constraints);
            definitions.resize(stack.back().n_prev_defs());
            assignments.resize(stack.back().n_prev_defs());
            constraints.resize(stack.back().n_prev_constraints());
            observation_points.resize(stack.back().n_prev_obs());
            stack.back().taken() = false;
            n_constraints = stack.back().n_prev_constraints();
            continue;
          }
        }
      }
      const outgoing_edge* branch = stack.back().taken() ? &cond->then_branch() : &cond->else_branch();
      stack.push_back(stack.back().next(branch));
      stack.back().n_prev_constraints() = n_constraints;
      assert(n_constraints == constraints.size());
    }

    // Process one block.
    const control_flow_block* block = std::get<unconditional_edge>(stack.back().edge()).get();
    if (block == nullptr) {
      // The program terminated on this path.
      // Pop stack.
      while (!stack.empty() && (std::holds_alternative<unconditional_edge>(stack.back().edge()) || !stack.back().taken())) {
        stack.pop_back();
      }
      if (stack.empty()) break;
      definitions.resize(stack.back().n_prev_defs());
      assignments.resize(stack.back().n_prev_defs());
      constraints.resize(stack.back().n_prev_constraints());
      observation_points.resize(stack.back().n_prev_obs());
      stack.back().taken() = false;
      continue;
    }

    size_t n_defs = stack.back().n_prev_defs();
    size_t n_obs_found = stack.back().n_prev_obs();
    for (const auto& step : block->steps()) {
      if (std::holds_alternative<observation>(step)) {
        observation_points.push_back(n_defs);
        n_obs_found++;
      } else {
        const auto& a = std::get<assignment>(step);
        size_t new_index = count_assignments(&a.var());
        size_t n_prev_nondet = count_assignments(nullptr);
        size_t n_nondet = n_prev_nondet;
        constraints.push_back("(= " + prefix + "_" + a.var().name() + "_" + std::to_string(new_index) + " " + instantiate_arith_expr(a.value(), n_nondet, n_constraints) + ")");
        n_constraints++;
        definitions.push_back(prefix + "_" + a.var().name() + "_" + std::to_string(new_index) + "::int");
        assignments.push_back(&a.var());
        n_defs += 1 + n_nondet - n_prev_nondet;
      }
    }

    if (n_obs_found >= n_obs_needed) {
      // Let the caller do whatever they want to do.
      if (!f(std::cref(definitions), std::cref(constraints), [&](std::string_view var_name, size_t obs_index) -> std::optional<std::string> {
        const auto* decl = program.var(var_name);
        assert(decl != nullptr);
        assert(obs_index < n_obs_found);
        size_t max_defs = observation_points[obs_index];
        size_t index = 0;
        for (size_t i = 0; i < max_defs; i++) {
          if (assignments[i] == decl) {
            index++;
          }
        }
        return prefix + "_" + std::string(var_name) + "_" + std::to_string(index - 1);
      })) {
        return;
      }

      // Pop stack.
      while (!stack.empty() && (std::holds_alternative<unconditional_edge>(stack.back().edge()) || !stack.back().taken())) {
        stack.pop_back();
      }
      if (stack.empty()) break;
      definitions.resize(stack.back().n_prev_defs());
      assignments.resize(stack.back().n_prev_defs());
      constraints.resize(stack.back().n_prev_constraints());
      observation_points.resize(stack.back().n_prev_obs());
      stack.back().taken() = false;
    } else {
      // Push stack.
      stack.push_back(stack.back().next(&block->next()));
      stack.back().n_prev_obs() = n_obs_found;
      stack.back().n_prev_defs() = n_defs;
      stack.back().n_prev_constraints() = n_constraints;
    }
  }
}
