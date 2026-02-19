#pragma once

#include <cstdint>
#include <string>
#include <string_view>
#include <unordered_map>
#include <vector>
#include <stdexcept>

#include "core/node.h"

namespace llm2smt {

struct SymbolInfo {
    std::string name;
    uint32_t    arity;
};

class SymbolTable {
public:
    SymbolTable() {
        // Reserve index 0 as NULL_SYMBOL
        symbols_.push_back({"<null>", 0});
    }

    // Intern a symbol name; if already declared with the same arity, return existing id.
    // Throws if already declared with a different arity.
    SymbolId intern(std::string_view name, uint32_t arity) {
        auto it = name_to_id_.find(std::string(name));
        if (it != name_to_id_.end()) {
            SymbolId id = it->second;
            if (symbols_[id].arity != arity) {
                throw std::invalid_argument(
                    std::string("Symbol '") + std::string(name) +
                    "' already declared with different arity");
            }
            return id;
        }
        SymbolId id = static_cast<SymbolId>(symbols_.size());
        symbols_.push_back({std::string(name), arity});
        name_to_id_[std::string(name)] = id;
        return id;
    }

    // Look up without registering; returns NULL_SYMBOL if not found.
    SymbolId lookup(std::string_view name) const {
        auto it = name_to_id_.find(std::string(name));
        return (it != name_to_id_.end()) ? it->second : NULL_SYMBOL;
    }

    const SymbolInfo& get(SymbolId id) const { return symbols_.at(id); }

    std::size_t size() const { return symbols_.size(); }

private:
    std::vector<SymbolInfo>                   symbols_;
    std::unordered_map<std::string, SymbolId> name_to_id_;
};

} // namespace llm2smt
