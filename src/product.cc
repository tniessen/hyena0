#include "product.h"

#include <cassert>
#include <functional>
#include <map>
#include <set>

arith_expr clone(const arith_expr& value) {
  if (const auto* nd = std::get_if<nondet_value>(&value)) {
    return *nd;
  } else if (const auto* a = std::get_if<atomic>(&value)) {
    return *a;
  } else if (const auto* binary = std::get_if<std::unique_ptr<bin_arith_expr>>(&value)) {
    return std::make_unique<bin_arith_expr>((*binary)->kind(), clone((*binary)->left_operand()), clone((*binary)->right_operand()));
  } else if (const auto* unary = std::get_if<std::unique_ptr<unary_arith_expr>>(&value)) {
    return std::make_unique<unary_arith_expr>((*unary)->kind(), clone((*unary)->operand()));
  } else {
    assert(false);
  }
}

step clone_step(const step& s) {
  if (const auto* assign = std::get_if<assignment>(&s)) {
    return assignment(assign->var(), clone(assign->value()));
  } else {
    assert(std::holds_alternative<observation>(s));
    return std::get<observation>(s);
  }
}

std::vector<step> clone_steps(const std::vector<step>& steps) {
  std::vector<step> out;
  out.reserve(steps.size());
  std::transform(steps.begin(), steps.end(), std::back_inserter(out), clone_step);
  return out;
}

class var_map {
public:
  struct pair { const var_decl& original_decl; const var_decl& new_decl; };

  template <typename F>
  explicit var_map(const std::deque<var_decl>& in, std::deque<var_decl>& out, F&& rename) {
    size_t offset = out.size();
    for (const auto& v : in) {
      out.emplace_back(rename(v.name()), v.type());
    }
    assert(in.size() == out.size() - offset);
    for (size_t i = 0; i < in.size(); i++) {
      assert(!vars_.contains(in[i].name()));
      vars_.insert({in[i].name(), pair {in[i], out[offset + i]}});
      assert(!reverse_.contains(out[offset + i].name()));
      reverse_.insert({out[offset + i].name(), pair {in[i], out[offset + i]}});
    }
  }

  const std::map<std::string_view, pair>& vars() const { return vars_; }

  const var_decl& rename(const var_decl& original) const {
    auto it = vars_.find(original.name());
    assert(it != vars_.end());
    assert(&it->second.original_decl == &original);
    return it->second.new_decl;
  }

  atomic rename(const atomic& original) const {
    if (const auto* c = std::get_if<constant>(&original)) {
      return *c;
    } else {
      const auto& v = std::get<std::reference_wrapper<const var_decl>>(original);
      return atomic {rename(v.get())};
    }
  }

  const var_decl& unrename(const var_decl& new_decl) const {
    auto it = reverse_.find(new_decl.name());
    assert(it != reverse_.end());
    assert(&it->second.new_decl == &new_decl);
    return it->second.original_decl;
  }

private:
  std::map<std::string_view, pair> vars_;
  std::map<std::string_view, pair> reverse_;
};

arith_expr fix_value(const arith_expr& expr, const var_map& vars) {
  if (const auto* nd = std::get_if<nondet_value>(&expr)) {
    return *nd;
  } else if (const auto* a = std::get_if<atomic>(&expr)) {
    return vars.rename(*a);
  } else if (const auto* bin_ptr = std::get_if<std::unique_ptr<bin_arith_expr>>(&expr)) {
    const auto& bin = *bin_ptr;
    return std::make_unique<bin_arith_expr>(
        bin->kind(),
        fix_value(bin->left_operand(), vars),
        fix_value(bin->right_operand(), vars));
  } else if (const auto* unary_ptr = std::get_if<std::unique_ptr<unary_arith_expr>>(&expr)) {
    const auto& unary = *unary_ptr;
    return std::make_unique<unary_arith_expr>(
        unary->kind(), fix_value(unary->operand(), vars));
  } else {
    assert(false);
  }
}


class program_template {
public:
  using block_template = std::vector<std::vector<step>>;

  explicit program_template(const program& prog, const var_map& vars, bool keep_obs) : original_program_(prog), vars_(vars) {
    n_entry_points_ = 0;
    for (const auto& block : prog.blocks()) {
      assert(blocks_.size() == block->index());
      block_template steps;
      steps.emplace_back();
      for (size_t i = 0; i < block->steps().size(); i++) {
        const step& s = block->steps()[i];
        if (std::holds_alternative<observation>(s)) {
          // If we are keeping the observation point, we need to switch to the
          // other program afterwards. Otherwise, we remove the observation
          // point and switch to the other program immediately.
          if (keep_obs) {
            steps.back().emplace_back(observation {});
          }
          // Mark a re-entry point here.
          steps.emplace_back();
          n_entry_points_++;
        } else {
          const auto& assign = std::get<assignment>(s);
          if (steps.size() == 0) steps.emplace_back();
          steps.back().emplace_back(assignment(vars.rename(assign.var()), fix_value(assign.value(), vars)));
        }
      }
      blocks_.push_back(std::move(steps));
    }
  }

  inline const program& original_program() const { return original_program_; }

  inline const var_map& vars() const { return vars_; }

  inline const std::vector<block_template>& blocks() const { return blocks_; }

  inline size_t count_entry_points() const { return n_entry_points_; }

private:
  const program& original_program_;
  const var_map& vars_;

  std::vector<block_template> blocks_;
  size_t n_entry_points_;
};

std::function<std::string(std::string_view)> rename_with_prefix(const char* p) {
  return [p](const std::string_view& a) -> std::string {
    return p + std::string(a);
  };
}

struct entry_point_location {
  size_t which_copy;
  size_t which_entry_point;
};

// Make std::map<entry_point_location, T> work.
namespace std {
template <>
struct less<entry_point_location> {
  bool operator()(const entry_point_location& a, const entry_point_location& b) const {
    if (a.which_copy != b.which_copy) return a.which_copy < b.which_copy;
    return a.which_entry_point < b.which_entry_point;
  }
};
}

struct pending_transition {
  outgoing_edge& edge;
  entry_point_location target;
};

condition fix_condition(const condition& cond, const var_map& vars) {
  if (const auto* comp = std::get_if<comparison>(&cond)) {
    return comparison(comp->kind(), vars.rename(comp->op1()), vars.rename(comp->op2()));
  } else {
    return std::get<nondet_condition>(cond);
  }
};

outgoing_edge fix_edge(const outgoing_edge& edge, const var_map& vars, const std::vector<std::shared_ptr<control_flow_block>>& blocks, const std::vector<size_t>& first_block_indices) {
  if (const auto* uncond = std::get_if<unconditional_edge>(&edge)) {
    const std::shared_ptr<control_flow_block>& orig_target = *uncond;
    if (orig_target == nullptr) {
      // The program terminates here.
      // TODO: what should we do?
      return unconditional_edge {nullptr};
    }
    size_t orig_index = orig_target->index();
    size_t new_index = first_block_indices[orig_index];
    return blocks[new_index];
  } else {
    const auto& cond = std::get<std::unique_ptr<conditional_branch>>(edge);
    return std::make_unique<conditional_branch>(
        fix_condition(cond->condition(), vars),
        fix_edge(cond->then_branch(), vars, blocks, first_block_indices),
        fix_edge(cond->else_branch(), vars, blocks, first_block_indices));
  }
};

void instantiate_template(std::vector<std::shared_ptr<control_flow_block>>& blocks, size_t& block_index, const program_template& tmpl, bool add_init, size_t copy_index, std::vector<pending_transition>& pending_transitions, std::map<entry_point_location, std::shared_ptr<control_flow_block>>& entry_points) {
  size_t entry_point_index = 0;

  control_flow_block* added_init = nullptr;
  if (add_init) {
    blocks.push_back(std::make_shared<control_flow_block>(block_index, std::vector<step>(), outgoing_edge {}));
    added_init = blocks.back().get();
    size_t i = copy_index;
    size_t l = entry_point_index++;
    entry_points.insert({{i, l}, blocks.back()});
    block_index++;
  }

  std::vector<size_t> first_block_indices;
  for (size_t j = 0; j < tmpl.blocks().size(); j++) {
    const auto& block_template = tmpl.blocks()[j];
    // Even if the original block was empty, we should have produced a
    // non-empty list containing an empty block.
    assert(!block_template.empty());
    for (size_t k = 0; k < block_template.size(); k++) {
      const auto& sub_template = block_template[k];
      assert(block_index == blocks.size());
      blocks.push_back(std::make_shared<control_flow_block>(block_index, clone_steps(sub_template), outgoing_edge {}));
      if (k == 0) {
        first_block_indices.push_back(block_index);
      } else {
        // This is the l-th re-entry point in the i-th copy of this program.
        size_t i = copy_index;
        size_t l = entry_point_index++;
        entry_points.insert({{i, l}, blocks.back()});
        // Jump to the i-th entry point of b in the l-th copy of b.
        pending_transitions.push_back({std::next(blocks.rbegin())->get()->next(), {l, i}});
      }
      block_index++;
    }
  }

  // Reconstruct all edges from the original program. Where we have split
  // blocks into multiple blocks, we reconstruct incoming edges to point to
  // the first fragment and outgoing edges to exit from the last fragment.
  const auto& orig_blocks = tmpl.original_program().blocks();
  assert(first_block_indices.size() == orig_blocks.size());
  for (size_t orig_block_index = 0; orig_block_index < orig_blocks.size(); orig_block_index++) {
    const outgoing_edge& out_edge = orig_blocks[orig_block_index]->next();
    size_t last_block_index = ((orig_block_index + 1 < orig_blocks.size()) ? first_block_indices[orig_block_index + 1] : block_index) - 1;
    outgoing_edge& edge_to_patch = blocks[last_block_index]->next();
    assert(std::get<unconditional_edge>(edge_to_patch) == nullptr);
    edge_to_patch = fix_edge(out_edge, tmpl.vars(), blocks, first_block_indices);
  }

  if (add_init) {
    assert(added_init != nullptr);
    added_init->next() = fix_edge(tmpl.original_program().init(), tmpl.vars(), blocks, first_block_indices);
  }
}

static program compute_product(const program& a, const program& b) {
  std::deque<var_decl> vars;
  var_map a_vars(a.vars(), vars, rename_with_prefix("_"));
  var_map b_vars(b.vars(), vars, rename_with_prefix("'_"));
  assert(vars.size() == a.vars().size() + b.vars().size());

  // We first create "templates" for both programs. These do not contain any
  // edges, but they do contain information about transitions between the two
  // programs in the form of re-entry points.
  program_template a_template(a, a_vars, false);
  program_template b_template(b, b_vars, true);

  std::vector<std::shared_ptr<control_flow_block>> blocks;
  size_t block_index = 0;

  std::vector<pending_transition> a_transitions_to_b;
  std::map<entry_point_location, std::shared_ptr<control_flow_block>> a_entry_points;

  for (size_t i = 0; i < b_template.count_entry_points() + 1; i++) {
    // Instantiate template for a.
    instantiate_template(blocks, block_index, a_template, false, i, a_transitions_to_b, a_entry_points);
  }

  assert(a_entry_points.size() == (1 + b_template.count_entry_points()) * a_template.count_entry_points());

  std::vector<pending_transition> b_transitions_to_a;
  std::map<entry_point_location, std::shared_ptr<control_flow_block>> b_entry_points;

  for (size_t i = 0; i < a_template.count_entry_points(); i++) {
    // Instantiate template for b.
    instantiate_template(blocks, block_index, b_template, true, i, b_transitions_to_a, b_entry_points);
  }

  assert(b_entry_points.size() == a_template.count_entry_points() * (1 + b_template.count_entry_points()));

  // Now fill in the transitions between the two programs.
  for (const auto& t : a_transitions_to_b) {
    t.edge = b_entry_points.at(t.target);
    assert(std::get<unconditional_edge>(t.edge) != nullptr);
  }
  for (const auto& t : b_transitions_to_a) {
    t.edge = a_entry_points.at(t.target);
    assert(std::get<unconditional_edge>(t.edge) != nullptr);
  }

  // TODO: blocks[0] is not correct
  return program(std::move(vars), blocks[0], std::move(blocks));
}

std::shared_ptr<program> compute_product(const std::vector<std::shared_ptr<program>>& programs) {
  assert(programs.size() != 0);

  std::vector<std::shared_ptr<program>> queue = programs;
  while (queue.size() > 1) {
    queue[0] = std::make_shared<program>(compute_product(*queue[0], *queue[1]));
    queue.erase(std::next(queue.begin()));
  }

  return queue[0];
}

void extend_var_mapping(var_scopes& scopes, const std::vector<std::pair<std::shared_ptr<program>, std::string_view>>& named_programs, const std::shared_ptr<program>& product_program) {
  std::vector<std::string> prefixes;
  for (size_t i = 0; i < named_programs.size(); i++) {
    prefixes.push_back("");
  }
  for (size_t i = 1; i < named_programs.size(); i++) {
    for (size_t j = 0; j < i; j++) {
      prefixes[j] = "_" + prefixes[j];
    }
    prefixes[i] = "'_" + prefixes[i];
  }

  for (size_t i = 0; i < named_programs.size(); i++) {
    const auto& scope_name = named_programs[i].second;
    for (const auto& var_decl : named_programs[i].first->vars()) {
      auto it = std::find_if(product_program->vars().begin(), product_program->vars().end(), [&](const auto& decl) -> bool {
        return decl.name() == prefixes[i] + var_decl.name();
      });
      assert(it != product_program->vars().end());
      scopes.add(scope_name, var_decl.name(), product_program, *it);
    }
  }
}
