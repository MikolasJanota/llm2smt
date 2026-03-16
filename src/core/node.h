#pragma once

#include <cstdint>
#include <vector>

namespace llm2smt {

using NodeId   = uint32_t;
using SymbolId = uint32_t;
using SortId   = uint32_t;

constexpr NodeId   NULL_NODE   = 0;
constexpr SymbolId NULL_SYMBOL = 0;
// BOOL_SORT is the one built-in sort; all user-declared sorts get ids >= 1.
constexpr SortId   BOOL_SORT   = 0;
constexpr SortId   NULL_SORT   = UINT32_MAX;  // uninterpreted / unspecified

struct NodeData {
    SymbolId             sym;
    std::vector<NodeId>  children;

    bool operator==(const NodeData& o) const noexcept {
        return sym == o.sym && children == o.children;
    }
};

struct NodeDataHash {
    std::size_t operator()(const NodeData& nd) const noexcept {
        // FNV-inspired hash
        std::size_t h = std::hash<uint32_t>{}(nd.sym);
        for (NodeId c : nd.children) {
            h ^= std::hash<uint32_t>{}(c) + 0x9e3779b9 + (h << 6) + (h >> 2);
        }
        return h;
    }
};

} // namespace llm2smt
