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

// Transparent hash for std::unordered_map<std::string,...> that accepts
// std::string_view in find/count without constructing a temporary std::string.
struct StringViewHash {
    using is_transparent = void;
    std::size_t operator()(std::string_view sv) const noexcept {
        return std::hash<std::string_view>{}(sv);
    }
};

class SymbolTable {
public:
    SymbolTable() {
        // Reserve index 0 as NULL_SYMBOL
        symbols_.push_back({"<null>", 0});
    }

    // Intern a symbol name; if already declared with the same arity, return existing id.
    // Throws if already declared with a different arity.
    // Hot path (existing symbol): zero heap allocations (transparent find).
    // Cold path (new symbol): one allocation for symbols_ entry; the map key
    // is aliased from that stored string to avoid a second allocation.
    SymbolId intern(std::string_view name, uint32_t arity) {
        auto it = name_to_id_.find(name);  // no allocation — transparent hash
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
        symbols_.push_back({std::string(name), arity});          // 1 allocation
        name_to_id_.emplace(symbols_.back().name, id);           // copies stored string
        return id;
    }

    // Look up without registering; returns NULL_SYMBOL if not found.
    // Zero heap allocations (transparent hash accepts string_view).
    SymbolId lookup(std::string_view name) const {
        auto it = name_to_id_.find(name);  // no allocation
        return (it != name_to_id_.end()) ? it->second : NULL_SYMBOL;
    }

    const SymbolInfo& get(SymbolId id) const { return symbols_.at(id); }

    std::size_t size() const { return symbols_.size(); }

private:
    std::vector<SymbolInfo> symbols_;
    // Transparent comparator (std::equal_to<>) allows find() with string_view key.
    std::unordered_map<std::string, SymbolId, StringViewHash, std::equal_to<>> name_to_id_;
};

} // namespace llm2smt
