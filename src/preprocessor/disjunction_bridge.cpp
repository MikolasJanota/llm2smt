#include "preprocessor/disjunction_bridge.h"

#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "core/node.h"

namespace llm2smt {

// ── Union-find over NodeIds ────────────────────────────────────────────────

struct UF {
    std::unordered_map<NodeId, NodeId> parent;
    std::unordered_set<NodeId>         nodes;  // every NodeId ever united

    NodeId find(NodeId x)
    {
        auto it = parent.find(x);
        if (it == parent.end()) return x;
        it->second = find(it->second);  // path compression
        return it->second;
    }

    void unite(NodeId a, NodeId b)
    {
        nodes.insert(a);
        nodes.insert(b);
        a = find(a); b = find(b);
        if (a != b) parent[a] = b;
    }

    bool same(NodeId a, NodeId b) { return find(a) == find(b); }
};

// ── Collect equality atoms by recursing through Ands ──────────────────────

static void collect_eqs(FmlRef f, UF& uf)
{
    if (f->kind == FmlKind::Eq) {
        uf.unite(f->eq_lhs, f->eq_rhs);
    } else if (f->kind == FmlKind::And) {
        for (const auto& ch : f->children)
            collect_eqs(ch, uf);
    }
    // Not / Or / Pred / Ite / … — stop (conservative)
}

// ── Bridge a single Or node ────────────────────────────────────────────────

static void bridge_or(FmlRef f, std::vector<FmlRef>& out)
{
    const auto& branches = f->children;
    if (branches.size() < 2) return;

    // Build union-find closure for each branch.
    std::vector<UF> uf(branches.size());
    for (size_t i = 0; i < branches.size(); ++i)
        collect_eqs(branches[i], uf[i]);

    // Shared nodes = NodeIds appearing in every branch's equality set.
    // Start from branch 0 and intersect with subsequent branches.
    std::unordered_set<NodeId> shared = uf[0].nodes;
    for (size_t i = 1; i < branches.size(); ++i) {
        std::unordered_set<NodeId> tmp;
        for (NodeId n : shared)
            if (uf[i].nodes.count(n)) tmp.insert(n);
        shared = std::move(tmp);
        if (shared.empty()) return;  // fast exit
    }

    // For every pair of shared nodes, check if they are equivalent in ALL
    // branch closures and emit a new unit Eq if so.
    std::vector<NodeId> sv(shared.begin(), shared.end());
    for (size_t i = 0; i < sv.size(); ++i) {
        for (size_t j = i + 1; j < sv.size(); ++j) {
            NodeId a = sv[i], b = sv[j];
            bool common = true;
            for (auto& u : uf) {
                if (!u.same(a, b)) { common = false; break; }
            }
            if (common)
                out.push_back(fml_eq(a, b));
        }
    }
}

// ── Recurse through the formula tree to find all Or nodes ─────────────────

static void extract_from(FmlRef f, std::vector<FmlRef>& out)
{
    switch (f->kind) {
    case FmlKind::Or:
        bridge_or(f, out);
        break;
    case FmlKind::And:
        for (const auto& ch : f->children)
            extract_from(ch, out);
        break;
    default:
        break;
    }
}

// ── Public entry point ─────────────────────────────────────────────────────

void bridge_disjunctions(std::vector<FmlRef>& fmls)
{
    std::vector<FmlRef> new_facts;
    for (const auto& f : fmls)
        extract_from(f, new_facts);
    fmls.insert(fmls.end(), new_facts.begin(), new_facts.end());
}

} // namespace llm2smt
