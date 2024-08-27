#pragma once

#include <algorithm>
#include <optional>
#include <ostream>
#include <ranges>
#include <string>
#include <variant>
#include <vector>

class atom {
public:
  atom(std::string&& s) : value(std::move(s)) {}
  atom(const std::string& s) : value(s) {}

  inline operator std::string_view() const { return value; }

  inline bool operator==(const atom& other) const { return value == other.value; }
  inline bool operator==(const std::string_view& sv) const { return value == sv; }

private:
  std::string value;
};

class s_expr;
using s_expr_list = std::vector<s_expr>;

class s_expr {
public:
  static std::optional<s_expr_list> parse_multiple(std::string_view input);
  static std::optional<s_expr> parse(std::string_view input);
  static std::optional<s_expr> read(std::string_view& input);

  inline s_expr(atom&& a) : value(std::move(a)) {}
  inline s_expr(s_expr_list&& l) : value(std::move(l)) {}

  inline bool is_atom() const { return std::holds_alternative<atom>(value); }
  inline bool is_list() const { return std::holds_alternative<s_expr_list>(value); }

  inline const atom& as_atom() const { return std::get<atom>(value); }
  inline const s_expr_list& as_list() const { return std::get<s_expr_list>(value); }

  inline bool operator==(const s_expr& other) const {
    return value == other.value;
  }

private:
  std::variant<atom, s_expr_list> value;
};

std::ostream &operator<<(std::ostream& os, const atom& a);
std::ostream &operator<<(std::ostream& os, const s_expr& e);

template <size_t N>
struct string_literal {
  constexpr string_literal(const char (&str)[N]) {
    std::copy_n(str, N, value);
  }

  char value[N];
};

// TODO: replace with more modern C++20 ranges
class rest {
public:
  rest(const s_expr_list& list, size_t offset) : list_(list), offset_(offset) {}

  const s_expr_list& list() const { return list_; }
  size_t offset() const { return offset_; }

  s_expr_list::const_iterator begin() const { return list_.begin() + offset_; }
  s_expr_list::const_iterator end() const { return list_.end(); }

private:
  const s_expr_list& list_;
  size_t offset_;
};
static_assert(std::ranges::range<rest>);

template <typename T>
std::optional<std::tuple<T>> destructure_inner(const s_expr_list& list, size_t offset) {
  static_assert(!std::is_same_v<T, T>, "Unsupported type");
}

template <>
inline std::optional<std::tuple<const s_expr&>> destructure_inner(const s_expr_list& list, size_t offset) {
  if (list.size() <= offset) return std::nullopt;
  return std::tuple<const s_expr&>(list[offset]);
}

template <>
inline std::optional<std::tuple<const atom&>> destructure_inner<const atom&>(const s_expr_list& list, size_t offset) {
  if (list.size() <= offset) return std::nullopt;
  if (!list[offset].is_atom()) return std::nullopt;
  return std::tuple<const atom&>(list[offset].as_atom());
}

template <>
inline std::optional<std::tuple<const s_expr_list&>> destructure_inner<const s_expr_list&>(const s_expr_list& list, size_t offset) {
  if (list.size() <= offset) return std::nullopt;
  if (!list[offset].is_list()) return std::nullopt;
  return std::tuple<const s_expr_list&>(list[offset].as_list());
}

using optional_atom_ref = std::optional<std::reference_wrapper<const atom>>;

template <>
inline std::optional<std::tuple<optional_atom_ref>> destructure_inner<optional_atom_ref>(const s_expr_list& list, size_t offset) {
  if (list.size() <= offset) return std::tuple<optional_atom_ref>(std::nullopt);
  auto ret = destructure_inner<const atom&>(list, offset);
  if (!ret) return std::nullopt;
  return std::tuple<optional_atom_ref>(std::get<0>(std::move(*ret)));
}

template <>
inline std::optional<std::tuple<rest>> destructure_inner<rest>(const s_expr_list& list, size_t offset) {
  return std::make_tuple<rest>({list, offset});
}

template <typename S, typename T, typename... Ts>
std::optional<std::tuple<S, T, Ts...>> destructure_inner(const s_expr_list& list, size_t offset) {
  //if (list.size() - offset < 2 + sizeof...(Ts)) return std::nullopt;
  auto head = destructure_inner<S>(list, offset);
  if (!head) return std::nullopt;
  auto tail = destructure_inner<T, Ts...>(list, offset + 1);
  if (!tail) return std::nullopt;
  return std::tuple_cat(*head, *tail);
}

// TODO: destructure should not have an offset argument. Instead, all destructuring functions should
// accept arbitrary C++20 ranges.
template <typename T>
std::optional<std::tuple<T>> destructure(const s_expr_list& list, size_t offset = 0) {
  if constexpr (!std::is_same_v<T, rest>) {
    if constexpr (std::is_same_v<T, std::optional<std::reference_wrapper<const atom>>>) {
      if (list.size() - offset > 1) return std::nullopt;
    } else {
      if (list.size() - offset != 1) return std::nullopt;
    }
  }
  return destructure_inner<T>(list, offset);
}

template <typename S, typename T, typename... Ts>
std::optional<std::tuple<S, T, Ts...>> destructure(const s_expr_list& list, size_t offset = 0) {
  const size_t n = list.size() - offset;
  if constexpr (std::is_same_v<rest, S> || std::is_same_v<rest, T> ||
                (std::is_same_v<rest, Ts> || ...)) {
    static_assert(!std::is_same_v<optional_atom_ref, S> &&
                  !std::is_same_v<optional_atom_ref, T> &&
                  !(std::is_same_v<optional_atom_ref, Ts> || ...),
                  "optional and rest cannot be combined");
    if (n < 1 + sizeof...(Ts)) return std::nullopt;
  } else if constexpr (std::is_same_v<optional_atom_ref, S> ||
                       std::is_same_v<optional_atom_ref, T> ||
                       (std::is_same_v<optional_atom_ref, Ts> || ...)) {
    // TODO: check that only one type is optional
    if (n != 2 + sizeof...(Ts) && n != 1 + sizeof...(Ts)) {
      return std::nullopt;
    }
  } else {
    if (n != 2 + sizeof...(Ts)) return std::nullopt;
  }
  return destructure_inner<S, T, Ts...>(list, offset);
}

template <string_literal keyword, typename T, typename... Ts>
std::optional<std::tuple<T, Ts...>> destructure(const s_expr_list& list) {
  if (list.empty() || !list[0].is_atom() || list[0].as_atom() != keyword.value) {
    return std::nullopt;
  }
  return destructure<T, Ts...>(list, 1);
}

template <string_literal keyword>
bool destructure(const s_expr_list& list) {
  return list.size() == 1 && list[0].is_atom() && list[0].as_atom() == keyword.value;
}
