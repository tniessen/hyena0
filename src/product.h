#pragma once

#include "cfg.h"

#include <map>
#include <set>

// We use a very simple product construction: we execute the first program until
// we have executed a block that contains an observation point, then we switch
// to the next program, etc. Only when the last program reaches an observation
// point, then the product program does, too, and control returns to the first
// program.
//
// All variables are renamed to avoid conflicts.
//
// Potential re-entry points of each program are immediately after every
// (original) observation point and at the beginning of the program.

std::shared_ptr<program> compute_product(
    const std::vector<std::shared_ptr<program>>& programs);

class var_scopes {
public:
  explicit var_scopes() {}

  var_scopes(const var_scopes&) = delete;
  var_scopes& operator=(const var_scopes&) = delete;

  var_scopes(var_scopes&&) = delete;
  var_scopes& operator=(var_scopes&&) = delete;

  void add(std::string_view scope, std::string_view var, const std::shared_ptr<program>& program, const var_decl& decl) {
    assert(!vars_.contains({scope, var}));
    vars_.insert({{scope, var}, {program, decl}});
  }

  void add_shortcuts() {
    std::multiset<std::string_view> keys;
    for (const auto& entry : vars_) {
      keys.insert(entry.first.second);
    }
    for (const auto& entry : vars_) {
      const std::string_view& key = entry.first.second;
      size_t cnt = keys.count(key);
      assert(cnt > 0);
      if (cnt == 1) {
        shortcuts_.insert({key, entry.first.first});
      }
    }
  }

  inline const std::map<
    std::pair<std::string_view, std::string_view>,
    std::pair<std::shared_ptr<program>, const var_decl&>
  >& entries() const {
    return vars_;
  }

  inline const std::map<std::string_view, std::string_view>& shortcuts() const {
    return shortcuts_;
  }

private:
  std::map<
    std::pair<std::string_view, std::string_view>,
    std::pair<std::shared_ptr<program>, const var_decl&>
  > vars_;
  std::map<std::string_view, std::string_view> shortcuts_;
};

void extend_var_mapping(var_scopes& scopes, const std::vector<std::pair<std::shared_ptr<program>, std::string_view>>& named_programs, const std::shared_ptr<program>& product_program);
