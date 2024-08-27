#include "cfg.h"

#include <cassert>
#include <functional>

// Example:
//
// (set foo 1)
// (repeat
//   (observe)
//   (set foo (+ foo 1)))
//
// becomes
//
// +-----------+
// | set foo 1 |
// +-----------+
//      |          +-----------+
//      |          |           |
//      v          v           |
// +-------------------+       |
// | observe           |       |
// +-------------------+       |
// | set foo (+ foo 1) |       |
// +-------------------+       |
//          |                  |
//          +------------------+
//
// (set foo 1)
// (if (< foo bar)
//   (then (set foo (+ foo 1)))
//   (else (set bar (+ bar 1))))
// (set baz 1)
//
// +-----------+
// | set foo 1 |
// +-----------+
//    |     |
//    |     |
//    |     +--------------------+
//    |                          |
//    | (< foo bar)              | (not (< foo bar))
//    v                          v
// +-------------------+  +-------------------+
// | set foo (+ foo 1) |  | set bar (+ bar 1) |
// +-------------------+  +-------------------+
//          |                    |
//          |                    |
//          +-----+     +--------+
//                |     |
//                |     |
//                v     v
//             +-----------+
//             | set bar 1 |
//             +-----------+
//
// There are some tricky inputs, for which we need to introduce pseudo-blocks:
//
// (set x (nondet))
// (repeat
//   (if (> x 0) (then (set x (- x)))))
//
//      +----------------+
//      | set x (nondet) |-----------------+
//      +----------------+                 |
//              |                          |
//              | (> x 0)    (not (> x 0)) |
//              v                          |
//      +----------------+                 |
// +--->|  set x (- x)   |                 |
// |    +----------------+                 |
// |         |          |                  |
// |         | (> x 0)  |                  |
// |         |          | (not (> x 0))    |
// +---------+          |                  |
// |                    v                  |
// |   (> x 0) +----------------+          |
// +-----------| <pseudo block> |<---------+
//             +----------------+          |
//                      |                  |
//                      | (not (> x 0))    |
//                      |                  |
//                      +------------------+

static inline std::string comparison_op(enum comparison::kind k) {
  switch (k) {
    case comparison::kind::EQ: return "=";
    case comparison::kind::NEQ: return "/=";
    case comparison::kind::LT: return "<";
    case comparison::kind::LE: return "<=";
    case comparison::kind::GT: return ">";
    case comparison::kind::GE: return ">=";
    case comparison::kind::DIVIDED_BY: return "divided-by";
  }
  __builtin_unreachable();
}

static atom atomic_to_atom(const atomic& atomic) {
  if (const auto* decl = std::get_if<std::reference_wrapper<const var_decl>>(&atomic)) {
    return atom(decl->get().name());
  } else {
    return atom(std::to_string(std::get<constant>(atomic).value()));
  }
}

static s_expr condition_to_s_expr(const condition& cond) {
  if (std::holds_alternative<nondet_condition>(cond)) {
    return s_expr_list({atom("nondet")});
  } else {
    const auto& comp = std::get<comparison>(cond);
    return s_expr_list({
      atom(comparison_op(comp.kind())),
      atom(comp.op1().name()),
      atom(atomic_to_atom(comp.op2()))
    });
  }
}

s_expr to_s_expr(const outgoing_edge& edge) {
  if (std::holds_alternative<unconditional_edge>(edge)) {
    const auto& next = std::get<unconditional_edge>(edge);
    if (next) {
      return atom(std::to_string(next->index()));
    } else {
      return s_expr_list({atom("halt")});
    }
  } else {
    const auto& cond = std::get<std::unique_ptr<conditional_branch>>(edge);
    return s_expr_list({
      condition_to_s_expr(cond->condition()),
      to_s_expr(cond->then_branch()),
      to_s_expr(cond->else_branch())
    });
  }
}

std::string stringify(const outgoing_edge& edge) {
  if (std::holds_alternative<unconditional_edge>(edge)) {
    return "unconditional edge to " + (std::get<unconditional_edge>(edge) ? "block " + std::to_string(std::get<unconditional_edge>(edge)->index()) : "(none)");
  } else {
    return "conditional edge either to " + stringify(std::get<std::unique_ptr<conditional_branch>>(edge)->then_branch()) + " or to " + stringify(std::get<std::unique_ptr<conditional_branch>>(edge)->else_branch());
  }
}

struct mutable_outgoing_edge_group {
  std::vector<outgoing_edge*> edges;

  mutable_outgoing_edge_group expand_join(const std::shared_ptr<control_flow_block>& target) {
    assert(!edges.empty());
    for (auto edge : edges) *edge = target;
    return {{&target->next()}};
  }

  void expand_join(const outgoing_edge& target) {
    assert(!edges.empty());
    for (auto edge : edges) {
      //assert(nullptr == std::get<unconditional_edge>(*edge));
      *edge = clone(target);
    }
  }

  std::pair<mutable_outgoing_edge_group, mutable_outgoing_edge_group> expand_conditional(const condition& cond) {
    assert(!edges.empty());
    mutable_outgoing_edge_group then_group, else_group;
    for (auto& edge : edges) {
      auto ptr = std::make_unique<conditional_branch>(condition(cond), outgoing_edge{}, outgoing_edge{});
      then_group.edges.push_back(&ptr->then_branch());
      else_group.edges.push_back(&ptr->else_branch());
      *edge = std::move(ptr);
    }
    return {then_group, else_group};
  }

  void expand_null_pointers(std::function<std::shared_ptr<control_flow_block>()>& f, outgoing_edge* edge, std::shared_ptr<control_flow_block>& target) {
    if (auto* uncond = std::get_if<unconditional_edge>(edge)) {
      if (uncond->get() == nullptr) {
        if (target == nullptr) target = f();
        (*uncond) = target;
      }
    } else {
      auto& cond = std::get<std::unique_ptr<conditional_branch>>(*edge);
      expand_null_pointers(f, &cond->then_branch(), target);
      expand_null_pointers(f, &cond->else_branch(), target);
    }
  }

  void expand_null_pointers(std::function<std::shared_ptr<control_flow_block>()>&& f) {
    std::shared_ptr<control_flow_block> target = nullptr;
    for (auto& edge : edges) {
      expand_null_pointers(f, edge, target);
    }
  }

  void expand_null_pointers(outgoing_edge* edge, const outgoing_edge& target) {
    if (auto* uncond = std::get_if<unconditional_edge>(edge)) {
      if (uncond->get() == nullptr) {
        *edge = clone(target);
      }
    } else {
      auto& cond = std::get<std::unique_ptr<conditional_branch>>(*edge);
      expand_null_pointers(&cond->then_branch(), target);
      expand_null_pointers(&cond->else_branch(), target);
    }
  }

  void expand_null_pointers(const outgoing_edge& target) {
    for (auto& edge : edges) {
      expand_null_pointers(edge, target);
    }
  }

  void null_pointers_rec(outgoing_edge* edge, mutable_outgoing_edge_group& out) {
    if (auto* uncond = std::get_if<unconditional_edge>(edge)) {
      if (uncond->get() == nullptr) {
        out.edges.push_back(edge);
      }
    } else {
      auto& cond = std::get<std::unique_ptr<conditional_branch>>(*edge);
      null_pointers_rec(&cond->then_branch(), out);
      null_pointers_rec(&cond->else_branch(), out);
    }
  }

  mutable_outgoing_edge_group null_pointers_rec() {
    mutable_outgoing_edge_group ret;
    for (auto& edge : edges) {
      null_pointers_rec(edge, ret);
    }
    return ret;
  }

  mutable_outgoing_edge_group&& merge(mutable_outgoing_edge_group&& other) && {
    // TODO: assert(current_target() == other.current_target());
    for (auto& edge : other.edges) {
      edges.push_back(edge);
    }
    return std::move(*this);
  }

  const outgoing_edge& current_target() const {
    assert(!edges.empty());
    const outgoing_edge* ret = edges[0];
    for (auto& edge : edges) assert(*edge == *ret);
    return *ret;
  }
};

program program::parse(s_expr_list::const_iterator begin, s_expr_list::const_iterator end) {
  std::deque<var_decl> defined_vars;
  std::vector<std::shared_ptr<control_flow_block>> blocks;

  auto find_var = [&](const atom& name) -> const var_decl& {
    std::string_view var_name(name);
    auto it = std::find_if(defined_vars.begin(), defined_vars.end(), [&](const auto& var) {
      return var.name() == var_name;
    });
    if (it == defined_vars.end()) assert(!"Unknown variable");
    return std::ref(*it);
  };

  auto parse_atomic = [&](const atom& atom) -> atomic {
    if (isdigit(std::string_view(atom)[0])) {
      return constant {std::stoi(std::string(atom))};
    } else {
      const auto& var = find_var(atom);
      return std::ref(var);
    }
  };

  std::function<arith_expr(const s_expr&)> parse_arith_expr = [&](const s_expr& expr) -> arith_expr {
    if (expr.is_atom()) {
      return parse_atomic(expr.as_atom());
    } else if (const auto add = destructure<"+", const s_expr&, const s_expr&>(expr.as_list())) {
      return std::make_unique<bin_arith_expr>(bin_arith_expr::kind::ADD, parse_arith_expr(std::get<0>(*add)), parse_arith_expr(std::get<1>(*add)));
    } else if (const auto sub = destructure<"-", const s_expr&, const s_expr&>(expr.as_list())) {
      return std::make_unique<bin_arith_expr>(bin_arith_expr::kind::SUB, parse_arith_expr(std::get<0>(*sub)), parse_arith_expr(std::get<1>(*sub)));
    } else if (const auto mul = destructure<"*", const s_expr&, const s_expr&>(expr.as_list())) {
      return std::make_unique<bin_arith_expr>(bin_arith_expr::kind::MUL, parse_arith_expr(std::get<0>(*mul)), parse_arith_expr(std::get<1>(*mul)));
    } else if (const auto neg = destructure<"-", const s_expr&>(expr.as_list())) {
      return std::make_unique<unary_arith_expr>(unary_arith_expr::kind::NEG, parse_arith_expr(std::get<0>(*neg)));
    } else if (const auto nondet = destructure<"nondet", rest>(expr.as_list())) {
      const auto& [constraints] = *nondet;
      std::optional<int> min, max;
      if (constraints.end() - constraints.begin() > 2) {
        assert(!"Too many constraints for nondet");
      }
      for (auto it = constraints.begin(); it != constraints.end(); it++) {
        const auto& constraint = *it;
        assert(constraint.is_list());
        if (const auto v = destructure<"min", const atom&>(constraint.as_list())) {
          const auto& [vstr] = *v;
          min = std::stoi(std::string(vstr));
        } else if (const auto v = destructure<"max", const atom&>(constraint.as_list())) {
          const auto& [vstr] = *v;
          max = std::stoi(std::string(vstr));
        } else {
          assert(!"Unknown constraint for nondet");
        }
      }
      return nondet_value(min, max);
    } else {
      assert(false);
    }
  };

  auto parse_condition = [&](const s_expr& expr) -> condition {
    if (destructure<"nondet">(expr.as_list())) {
      return nondet_condition();
    } else if (const auto eq = destructure<"=", const s_expr&, const s_expr&>(expr.as_list())) {
      const auto& [op1, op2] = *eq;
      return comparison(comparison::kind::EQ, find_var(op1.as_atom()), parse_atomic(op2.as_atom()));
    } else if (const auto neq = destructure<"/=", const s_expr&, const s_expr&>(expr.as_list())) {
      const auto& [op1, op2] = *neq;
      return comparison(comparison::kind::NEQ, find_var(op1.as_atom()), parse_atomic(op2.as_atom()));
    } else if (const auto gt = destructure<"<", const s_expr&, const s_expr&>(expr.as_list())) {
      const auto& [op1, op2] = *gt;
      return comparison(comparison::kind::LT, find_var(op1.as_atom()), parse_atomic(op2.as_atom()));
    } else if (const auto gt = destructure<"<=", const s_expr&, const s_expr&>(expr.as_list())) {
      const auto& [op1, op2] = *gt;
      return comparison(comparison::kind::LE, find_var(op1.as_atom()), parse_atomic(op2.as_atom()));
    } else if (const auto gt = destructure<">", const s_expr&, const s_expr&>(expr.as_list())) {
      const auto& [op1, op2] = *gt;
      return comparison(comparison::kind::GT, find_var(op1.as_atom()), parse_atomic(op2.as_atom()));
    } else if (const auto gt = destructure<">=", const s_expr&, const s_expr&>(expr.as_list())) {
      const auto& [op1, op2] = *gt;
      return comparison(comparison::kind::GE, find_var(op1.as_atom()), parse_atomic(op2.as_atom()));
    } else if (const auto div = destructure<"divided-by", const s_expr&, const s_expr&>(expr.as_list())) {
      const auto& [op1, op2] = *div;
      return comparison(comparison::kind::DIVIDED_BY, find_var(op1.as_atom()), parse_atomic(op2.as_atom()));
    } else {
      assert(false);
    }
  };

  std::function<mutable_outgoing_edge_group(mutable_outgoing_edge_group&, s_expr_list::const_iterator, s_expr_list::const_iterator, std::string)> expand_edges = [&](mutable_outgoing_edge_group& incoming, s_expr_list::const_iterator begin, s_expr_list::const_iterator end, std::string indent) {
    mutable_outgoing_edge_group outgoing = incoming;
    control_flow_block* current_block = nullptr;
    for (auto it = begin; it != end; it++) {
      const auto& expr = *it;
      if (const auto let = destructure<"let", const atom&, const s_expr&, const s_expr&>(expr.as_list())) {
        const auto& [name, type, value] = *let;
        assert(type.is_atom() && type.as_atom() == "int");
        const var_decl& var = defined_vars.emplace_back(std::string(name), var_type::INT);
        if (current_block == nullptr) {
          auto new_block = std::make_shared<control_flow_block>(blocks.size());
          blocks.push_back(new_block);
          outgoing = outgoing.expand_join(new_block);
          current_block = &*new_block;
        }
        current_block->steps().emplace_back(assignment {var, parse_arith_expr(value)});
      } else if (const auto let = destructure<"let", const atom&, const s_expr&>(expr.as_list())) {
        const auto& [name, type] = *let;
        assert(type.is_atom() && type.as_atom() == "int");
        defined_vars.emplace_back(std::string(name), var_type::INT);
      } else if (const auto set = destructure<"set", const atom&, const s_expr&>(expr.as_list())) {
        const auto& [name, value] = *set;
        std::string_view var_name(name);
        const auto& var = *std::find_if(defined_vars.begin(), defined_vars.end(), [&](const auto& var) {
          return var.name() == var_name;
        });
        if (current_block == nullptr) {
          auto new_block = std::make_shared<control_flow_block>(blocks.size());
          blocks.push_back(new_block);
          outgoing = outgoing.expand_join(new_block);
          current_block = &*new_block;
        }
        current_block->steps().emplace_back(assignment {var, parse_arith_expr(value)});
      } else if (destructure<"observe">(expr.as_list())) {
        if (current_block == nullptr) {
          auto new_block = std::make_shared<control_flow_block>(blocks.size());
          blocks.push_back(new_block);
          outgoing = outgoing.expand_join(new_block);
          current_block = &*new_block;
        }
        current_block->steps().emplace_back(observation {});
      } else if (const auto repeat = destructure<"repeat", rest>(expr.as_list())) {
        const auto& list = std::get<0>(*repeat).list();
        // The loop may have multiple first blocks, e.g., because it begins with
        // an if-then-else expression. It also may have multiple exit blocks for
        // the same reason.
        auto loop_body_exits = expand_edges(outgoing, list.cbegin() + std::get<0>(*repeat).offset(), list.cend(), indent + "    ");
        std::shared_ptr<control_flow_block> pseudo_block;
        auto make_pseudo_block = [&]() -> std::shared_ptr<control_flow_block> {
          if (!pseudo_block) {
            pseudo_block = std::make_shared<control_flow_block>(blocks.size());
            blocks.push_back(pseudo_block);
          }
          return pseudo_block;
        };
        outgoing.expand_null_pointers(make_pseudo_block);
        if (pseudo_block) {
          (mutable_outgoing_edge_group {{&pseudo_block->next()}}).expand_join(outgoing.current_target());
        }
        loop_body_exits.expand_null_pointers(outgoing.current_target());
        outgoing = mutable_outgoing_edge_group {};
        current_block = nullptr;
      } else if (const auto cond = destructure<"if", const s_expr&, const s_expr_list&, rest>(expr.as_list())) {
        const auto& [condition, then, maybe_else] = *cond;
        bool has_else = std::ranges::size(maybe_else) == 1 && maybe_else.begin()->is_list();
        assert(has_else || std::ranges::size(maybe_else) == 0);
        const auto then_ = destructure<"then", rest>(then);
        const auto& [then_body] = *then_;
        auto [then_outgoing, else_outgoing] = outgoing.expand_conditional(parse_condition(condition));
        then_outgoing = expand_edges(then_outgoing, then_body.begin(), then_body.end(), indent + "    ");
        if (has_else) {
          const auto else_ = destructure<"else", rest>(maybe_else.begin()->as_list());
          const auto& [else_body] = *else_;
          else_outgoing = expand_edges(else_outgoing, else_body.begin(), else_body.end(), indent + "    ");
        }
        outgoing = std::move(then_outgoing).merge(std::move(else_outgoing));
        current_block = nullptr;
      } else if (const auto while_loop = destructure<"while", const s_expr&, rest>(expr.as_list())) {
        const auto& [cond_expr, body] = *while_loop;
        condition cond = parse_condition(cond_expr);
        auto [then_outgoing, else_outgoing] = outgoing.expand_conditional(cond);
        auto loop_exits = expand_edges(then_outgoing, body.begin(), body.end(), indent + "    ");

        std::shared_ptr<control_flow_block> pseudo_block;
        auto make_pseudo_block = [&]() -> std::shared_ptr<control_flow_block> {
          assert(!pseudo_block);
          pseudo_block = std::make_shared<control_flow_block>(blocks.size());
          blocks.push_back(pseudo_block);
          return pseudo_block;
        };
        then_outgoing.expand_null_pointers(make_pseudo_block);
        mutable_outgoing_edge_group pseudo_block_next;
        if (pseudo_block) {
          pseudo_block_next.edges.push_back(&pseudo_block->next());
          pseudo_block_next.expand_join(outgoing.current_target());
        }
        loop_exits.expand_null_pointers(outgoing.current_target());
        outgoing = std::move(else_outgoing).merge(pseudo_block_next.null_pointers_rec()).merge(loop_exits.null_pointers_rec());
        current_block = nullptr;
      } else {
        assert(!"Unknown expression");
      }
    }
    return outgoing;
  };

  outgoing_edge first_block;
  mutable_outgoing_edge_group init {{&first_block}};
  auto exits = expand_edges(init, begin, end, "");

  return program(std::move(defined_vars), std::move(first_block), std::move(blocks));
}

static inline std::string bin_arith_op(enum bin_arith_expr::kind k) {
  switch (k) {
    case bin_arith_expr::kind::ADD: return "+";
    case bin_arith_expr::kind::SUB: return "-";
    case bin_arith_expr::kind::MUL: return "*";
  }
  __builtin_unreachable();
}

static inline std::string unary_arith_op(enum unary_arith_expr::kind k) {
  switch (k) {
    case unary_arith_expr::kind::NEG: return "-";
  }
  __builtin_unreachable();
}

static inline s_expr arith_expr_to_s_expr(const arith_expr& expr) {
  if (const auto* nd = std::get_if<nondet_value>(&expr)) {
    s_expr_list ret({atom("nondet")});
    if (nd->min().has_value()) {
      ret.push_back(s_expr_list {atom("min"), atom(std::to_string(nd->min().value()))});
    }
    if (nd->max().has_value()) {
      ret.push_back(s_expr_list {atom("max"), atom(std::to_string(nd->max().value()))});
    }
    return ret;
  } else if (std::holds_alternative<atomic>(expr)) {
    return atomic_to_atom(std::get<atomic>(expr));
  } else if (std::holds_alternative<std::unique_ptr<bin_arith_expr>>(expr)) {
    const auto& bin = std::get<std::unique_ptr<bin_arith_expr>>(expr);
    return s_expr_list({
      atom(bin_arith_op(bin->kind())),
      arith_expr_to_s_expr(bin->left_operand()),
      arith_expr_to_s_expr(bin->right_operand())
    });
  } else if (std::holds_alternative<std::unique_ptr<unary_arith_expr>>(expr)) {
    const auto& unary = std::get<std::unique_ptr<unary_arith_expr>>(expr);
    return s_expr_list({
      atom(unary_arith_op(unary->kind())),
      arith_expr_to_s_expr(unary->operand())
    });
  } else {
    assert(false);
  }
}

static inline s_expr step_to_s_expr(const step& step) {
  if (std::holds_alternative<assignment>(step)) {
    const auto& assign = std::get<assignment>(step);
    return s_expr_list({atom("set"), atom(assign.var().name()), arith_expr_to_s_expr(assign.value())});
  } else {
    assert(std::holds_alternative<observation>(step));
    return s_expr_list({atom("observe")});
  }
}

static inline s_expr steps_to_s_expr(const std::vector<step>& steps) {
  s_expr_list ret({atom("steps")});
  for (const auto& step : steps) {
    ret.push_back(step_to_s_expr(step));
  }
  return ret;
}

s_expr program::to_s_expr(const s_expr& name) const {
  s_expr_list ret({atom("control-flow-graph"), name});
  for (const auto& var : vars_) {
    ret.push_back(s_expr_list({atom("declare"), atom(var.name()), atom("int")}));
  }
  ret.push_back(s_expr_list({atom("init"), ::to_s_expr(init_)}));
  for (const auto& block : blocks_) {
    ret.push_back(block->to_s_expr());
  }
  return ret;
}

program::program(std::deque<var_decl>&& vars, outgoing_edge&& init, std::vector<std::shared_ptr<control_flow_block>>&& blocks)
    : vars_(std::move(vars)), init_(std::move(init)), blocks_(std::move(blocks)) {
  if (std::holds_alternative<unconditional_edge>(init_)) {
    assert(std::get<unconditional_edge>(init_)->index() == 0);
  }
}

s_expr control_flow_block::to_s_expr() const {
  return s_expr_list({
    atom("block"),
    atom(std::to_string(index_)),
    steps_to_s_expr(steps_),
    s_expr_list({atom("next"), ::to_s_expr(next_)})
  });
}
