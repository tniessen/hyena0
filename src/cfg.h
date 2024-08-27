#pragma once

#include "s-expr.h"

#include <cassert>
#include <climits>
#include <deque>
#include <memory>
#include <ranges>
#include <string>
#include <string_view>
#include <variant>
#include <vector>

class nondet_value {
public:
  nondet_value(std::optional<int> min, std::optional<int> max)
      : min_(min), max_(max) {
    assert(min_.value_or(INT_MIN) <= max_.value_or(INT_MAX));
  }

  const std::optional<int>& min() const { return min_; }
  const std::optional<int>& max() const { return max_; }

private:
  std::optional<int> min_;
  std::optional<int> max_;
};
struct nondet_condition {};

class control_flow_block;

// TODO: this creates memory leaks due to circular references in loops. We should use weak links for back edges.
using unconditional_edge = std::shared_ptr<control_flow_block>;

class conditional_branch;

using outgoing_edge = std::variant<unconditional_edge, std::unique_ptr<conditional_branch>>;

// TODO: make outgoing_edge a proper class and this an instance function:
s_expr to_s_expr(const outgoing_edge& edge);

enum class var_type {
  INT
};

class var_decl {
public:
  explicit var_decl(std::string&& name, var_type type)
      : name_(name), type_(type) {}

  var_decl(const var_decl& other) = delete;
  var_decl& operator=(const var_decl&) = delete;

  const std::string& name() const { return name_; }
  var_type type() const { return type_; }

private:
  std::string name_;
  var_type type_;
};

class constant {
public:
  explicit constant(int value) : value_(value) {}

  int value() const { return value_; }

private:
  int value_;
};

using atomic = std::variant<std::reference_wrapper<const var_decl>, constant>;

struct observation {};

class bin_arith_expr;
class unary_arith_expr;

using arith_expr = std::variant<nondet_value, atomic, std::unique_ptr<bin_arith_expr>, std::unique_ptr<unary_arith_expr>>;

class bin_arith_expr {
public:
  enum class kind {
    ADD, SUB, MUL
  };

  bin_arith_expr(enum kind k, arith_expr&& left, arith_expr&& right)
      : kind_(k), left_operand_(std::move(left)), right_operand_(std::move(right)) {}

  enum kind kind() const { return kind_; }
  const arith_expr& left_operand() const { return left_operand_; }
  const arith_expr& right_operand() const { return right_operand_; }

private:
  enum kind kind_;
  arith_expr left_operand_;
  arith_expr right_operand_;
};

class unary_arith_expr {
public:
  enum class kind {
    NEG
  };

  unary_arith_expr(enum kind k, arith_expr&& operand)
      : kind_(k), operand_(std::move(operand)) {}

  enum kind kind() const { return kind_; }
  const arith_expr& operand() const { return operand_; }

private:
  enum kind kind_;
  arith_expr operand_;
};

class assignment {
public:
  explicit assignment(const var_decl& var, arith_expr&& value)
      : var_(var), value_(std::move(value)) {}

  const var_decl& var() const { return var_; }
  const arith_expr& value() const { return value_; }

private:
  const var_decl& var_;
  arith_expr value_;
};

using step = std::variant<assignment, observation>;

class program {
public:
  static program parse(s_expr_list::const_iterator begin, s_expr_list::const_iterator end);

  const std::deque<var_decl>& vars() const { return vars_; }

  const var_decl* var(std::string_view name) const {
    auto it = std::ranges::find_if(vars_, [name](const var_decl& var) { return var.name() == name; });
    return it == vars_.end() ? nullptr : &*it;
  }

  const outgoing_edge& init() const { return init_; }

  const std::vector<std::shared_ptr<control_flow_block>>& blocks() const { return blocks_; }

  s_expr to_s_expr(const s_expr& name) const;

// TODO: private:
  program(std::deque<var_decl>&& vars, outgoing_edge&& init, std::vector<std::shared_ptr<control_flow_block>>&& blocks);

  std::deque<var_decl> vars_;
  outgoing_edge init_;
  std::vector<std::shared_ptr<control_flow_block>> blocks_;
};

class comparison {
public:
  enum class kind {
    // TODO: we should really have DIVIDES instead of DIVIDED_BY, but this
    // class currently requires the first operand to be a variable.
    EQ, NEQ, LT, LE, GT, GE, DIVIDED_BY
  };

  explicit comparison(kind k, const var_decl& op1, atomic&& op2)
      : kind_(k), op1_(&op1), op2_(std::move(op2)) {
    if (kind_ == kind::DIVIDED_BY) {
      // Yices' (divides c n) only supports integer constants for c.
      assert(std::holds_alternative<constant>(op2_));
    }
  }

  comparison(const comparison& other) : kind_(other.kind_), op1_(other.op1_), op2_(other.op2_) {}
  comparison& operator=(const comparison& other) {
    kind_ = other.kind_;
    op1_ = other.op1_;
    op2_ = other.op2_;
    return *this;
  }

  enum kind kind() const { return kind_; }

  const var_decl& op1() const { return *op1_; }
  const atomic& op2() const { return op2_; }

private:
  enum kind kind_;
  const var_decl* op1_;
  atomic op2_;
};

using condition = std::variant<nondet_condition, comparison>;

class conditional_branch {
public:
  conditional_branch(::condition&& cond, outgoing_edge&& then_branch, outgoing_edge&& else_branch)
      : condition_(std::move(cond)), then_branch_(std::move(then_branch)), else_branch_(std::move(else_branch)) {}

  conditional_branch& operator=(conditional_branch&& other) {
    condition_ = std::move(other.condition_);
    then_branch_ = std::move(other.then_branch_);
    else_branch_ = std::move(other.else_branch_);
    return *this;
  }

  const ::condition& condition() const { return condition_; }

  const outgoing_edge& then_branch() const { return then_branch_; }
  const outgoing_edge& else_branch() const { return else_branch_; }

  outgoing_edge& then_branch() { return then_branch_; }
  outgoing_edge& else_branch() { return else_branch_; }

private:
  ::condition condition_;
  outgoing_edge then_branch_;
  outgoing_edge else_branch_;
};

inline outgoing_edge clone(const outgoing_edge& edge) {
  if (std::holds_alternative<unconditional_edge>(edge)) {
    return std::get<unconditional_edge>(edge);
  } else {
    auto& cond_edge = *std::get<std::unique_ptr<conditional_branch>>(edge);
    return std::make_unique<conditional_branch>(condition(cond_edge.condition()), clone(cond_edge.then_branch()), clone(cond_edge.else_branch()));
  }
}

class control_flow_block {
public:
  control_flow_block(unsigned int index, std::vector<step>&& steps, outgoing_edge&& next)
      : index_(index), steps_(std::move(steps)), next_(std::move(next)) {}

  unsigned int index() const { return index_; }

  std::vector<step>& steps() { return steps_; }
  const std::vector<step>& steps() const { return steps_; }

  outgoing_edge& next() { return next_; }
  const outgoing_edge& next() const { return next_; }

  s_expr to_s_expr() const;

// TODO: private:
  control_flow_block(unsigned int index) : index_(index) {}

  unsigned int index_;
  std::vector<step> steps_;
  outgoing_edge next_;

  friend class program;
};
