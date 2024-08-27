#include "s-expr.h"

#define SPACES " \t\n\r"

static inline bool remove_comment(std::string_view& input) {
  if (!input.starts_with(';')) return false;
  size_t end_of_line = input.find('\n');
  size_t skip = (end_of_line == std::string_view::npos) ? input.size() : end_of_line + 1;
  input.remove_prefix(skip);
  return true;
}

static inline bool skip_whitespace(std::string_view& input) {
  do {
    size_t skip = input.find_first_not_of(SPACES);
    if (skip == std::string_view::npos) return false;
    input.remove_prefix(skip);
  } while (remove_comment(input));
  return true;
}

std::optional<s_expr> s_expr::parse(std::string_view input) {
  auto ret = read(input);
  if (skip_whitespace(input)) return std::nullopt;
  return ret;
}

std::optional<s_expr> s_expr::read(std::string_view& input) {
  if (!skip_whitespace(input)) return std::nullopt;

  if (input[0] == '(') {
    input.remove_prefix(1);
    if (!skip_whitespace(input)) return std::nullopt;

    std::vector<s_expr> children;
    while (input[0] != ')') {
      auto child = read(input);
      if (!child) return std::nullopt;
      children.push_back(*child);
      if (!skip_whitespace(input)) return std::nullopt;
    }
    input.remove_prefix(1);
    return s_expr(std::move(children));
  } else {
    size_t end = input.find_first_of(SPACES "()");
    if (end == std::string_view::npos) {
      end = input.size();
    } else if (end == 0) {
      return std::nullopt;
    }
    std::string atom(input.substr(0, end));
    input.remove_prefix(end);
    return s_expr(std::move(atom));
  }
}

std::optional<std::vector<s_expr>> s_expr::parse_multiple(std::string_view input) {
  std::vector<s_expr> ret;
  while (skip_whitespace(input)) {
    auto expr = s_expr::read(input);
    if (!expr) return std::nullopt;
    ret.push_back(*expr);
  }
  return ret;
}

std::ostream &operator<<(std::ostream& os, const atom& a) { 
  return os << std::string_view(a);
}

std::ostream &operator<<(std::ostream& os, const s_expr& e) { 
  if (e.is_atom()) {
    return os << e.as_atom();
  } else {
    os << '(';
    bool first = true;
    for (const auto& child : e.as_list()) {
      if (first) {
        first = false;
      } else {
        os << ' ';
      }
      os << child;
    }
    return os << ')';
  }
}
