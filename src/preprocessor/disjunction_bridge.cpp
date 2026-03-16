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

// ── Collect equality atoms by recursing through And trees ─────────────────

static void collect_eqs(NodeId f, UF& uf, const NodeManager& nm)
{
    if (nm.is_eq(f)) {
        NodeId c0 = nm.get(f).children[0];
        NodeId c1 = nm.get(f).children[1];
        uf.unite(c0, c1);
    } else if (nm.is_and(f)) {
        NodeId c0 = nm.get(f).children[0];
        NodeId c1 = nm.get(f).children[1];
        collect_eqs(c0, uf, nm);
        collect_eqs(c1, uf, nm);
    }
    // Not / Or / Pred / Ite / … — stop (conservative)
}

// ── Collect top-level disjuncts from a binary Or tree ─────────────────────

static void collect_or_branches(NodeId f, const NodeManager& nm,
                                  std::vector<NodeId>& branches)
{
    if (nm.is_or(f)) {
        NodeId c0 = nm.get(f).children[0];
        NodeId c1 = nm.get(f).children[1];
        collect_or_branches(c0, nm, branches);
        collect_or_branches(c1, nm, branches);
    } else {
        branches.push_back(f);
    }
}

// ── Bridge a single Or node ────────────────────────────────────────────────

static void bridge_or(NodeId f, size_t top_idx, NodeManager& nm,
                       std::vector<NodeId>& out,
                       std::vector<BridgeEquality>* eq_out)
{
    std::vector<NodeId> branches;
    collect_or_branches(f, nm, branches);
    if (branches.size() < 2) return;

    // Build union-find closure for each branch.
    std::vector<UF> uf(branches.size());
    for (size_t i = 0; i < branches.size(); ++i)
        collect_eqs(branches[i], uf[i], nm);

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
            if (common) {
                out.push_back(nm.mk_eq(a, b));
                if (eq_out)
                    eq_out->push_back({top_idx, f, a, b});
            }
        }
    }
}

// ── Recurse through the formula tree to find all Or nodes ─────────────────

static void extract_from(NodeId f, size_t top_idx, NodeManager& nm,
                           std::vector<NodeId>& out,
                           std::vector<BridgeEquality>* eq_out)
{
    if (nm.is_or(f)) {
        bridge_or(f, top_idx, nm, out, eq_out);
    } else if (nm.is_and(f)) {
        NodeId c0 = nm.get(f).children[0];
        NodeId c1 = nm.get(f).children[1];
        extract_from(c0, top_idx, nm, out, eq_out);
        extract_from(c1, top_idx, nm, out, eq_out);
    }
}

// ── Public entry point ─────────────────────────────────────────────────────

void bridge_disjunctions(std::vector<NodeId>& fmls,
                          NodeManager& nm,
                          std::vector<BridgeEquality>* equalities)
{
    std::vector<NodeId> new_facts;
    for (size_t i = 0; i < fmls.size(); ++i)
        extract_from(fmls[i], i, nm, new_facts, equalities);
    fmls.insert(fmls.end(), new_facts.begin(), new_facts.end());
}

} // namespace llm2smt
