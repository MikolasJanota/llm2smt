#include "theories/euf/cc.h"

#include <algorithm>
#include <cassert>
#include <numeric>
#include <stdexcept>

namespace llm2smt {

// ============================================================================
// Construction
// ============================================================================

CC::CC() {
    // Sentinel equation at index 0 (NULL_EQ)
    equations_.push_back(Equation{EqKind::Atomic, NULL_NODE, NULL_NODE, NULL_NODE, NULL_NODE});
    trail_.emplace_back();  // level 0 undo stack
}

// ============================================================================
// Node registration
// ============================================================================

void CC::ensure_node(NodeId n) {
    if (n >= static_cast<NodeId>(repr_.size())) {
        repr_.resize(n + 1, NULL_NODE);
        class_list_.resize(n + 1);
        use_list_.resize(n + 1);
        proof_parent_.resize(n + 1, NULL_NODE);
        proof_label_.resize(n + 1, EdgeLabel{DirectLabel{NULL_EQ}});
    }
}

NodeId CC::add_node(NodeId n) {
    ensure_node(n);
    if (repr_[n] == NULL_NODE) {
        repr_[n] = n;
        class_list_[n].push_back(n);
    }
    return n;
}

// ============================================================================
// Equation allocation
// ============================================================================

EqId CC::alloc_equation(Equation eq) {
    EqId id = static_cast<EqId>(equations_.size());
    equations_.push_back(eq);
    // Record on undo trail so we can shrink the table on backtrack
    UndoAction ua;
    ua.kind = UndoAction::Kind::EquationPop;
    record(ua);
    return id;
}

// ============================================================================
// Add equations
// ============================================================================

EqId CC::add_equation(NodeId lhs, NodeId rhs) {
    assert(lhs < repr_.size() && repr_[lhs] != NULL_NODE && "lhs not registered");
    assert(rhs < repr_.size() && repr_[rhs] != NULL_NODE && "rhs not registered");

    EqId id = alloc_equation(Equation{EqKind::Atomic, lhs, rhs, NULL_NODE, NULL_NODE});
    pending_.push_back(PendingEntry{lhs, rhs, DirectLabel{id}});
    propagate();
    return id;
}

EqId CC::add_app_equation(NodeId result, NodeId fn, NodeId arg) {
    assert(result < repr_.size() && repr_[result] != NULL_NODE && "result not registered");
    assert(fn     < repr_.size() && repr_[fn]     != NULL_NODE && "fn not registered");
    assert(arg    < repr_.size() && repr_[arg]    != NULL_NODE && "arg not registered");

    EqId id = alloc_equation(Equation{EqKind::App, result, NULL_NODE, fn, arg});

    // §3.3 Merge step for f(a1,a2)=a:
    auto key = std::make_pair(repr_[fn], repr_[arg]);
    auto it  = lookup_.find(key);
    if (it != lookup_.end()) {
        // Congruence: existing equation g = it->second with same-repr args
        EqId existing = it->second;
        NodeId other_result = equations_[existing].lhs;
        // Merge result and other_result justified by congruence(existing, id)
        pending_.push_back(PendingEntry{result, other_result,
                                        CongruenceLabel{existing, id}});
    } else {
        // No existing entry: register in lookup and use_lists
        lookup_[key] = id;
        record_lookup_remove(key);
        use_list_[repr_[fn]].push_back(id);
        record_use_list_pop(repr_[fn]);
        if (repr_[fn] != repr_[arg]) {
            use_list_[repr_[arg]].push_back(id);
            record_use_list_pop(repr_[arg]);
        }
    }
    propagate();
    return id;
}

// ============================================================================
// Query
// ============================================================================

NodeId CC::find(NodeId n) const {
    assert(n < repr_.size() && repr_[n] != NULL_NODE && "node not registered");
    return repr_[n];
}

bool CC::are_congruent(NodeId a, NodeId b) const {
    if (a >= repr_.size() || b >= repr_.size()) return false;
    if (repr_[a] == NULL_NODE || repr_[b] == NULL_NODE) return false;
    return repr_[a] == repr_[b];
}

// ============================================================================
// Propagate (§3.3)
// ============================================================================

void CC::propagate() {
    while (!pending_.empty()) {
        PendingEntry entry = pending_.front();
        pending_.pop_front();

        NodeId ra = repr_[entry.a];
        NodeId rb = repr_[entry.b];
        if (ra == rb) continue;

        // ra and rb must be flat representatives.
        // Walk chain if non-flat (can arise when undo restores stale repr).
        while (repr_[ra] != ra) ra = repr_[ra];
        while (repr_[rb] != rb) rb = repr_[rb];
        if (ra == rb) continue;

        // Union by class size: merge smaller into larger
        bool swapped = false;
        if (class_list_[ra].size() < class_list_[rb].size()) {
            std::swap(ra, rb);
            swapped = true;
        }
        // ra = kept representative, rb = merged (smaller class)

        // proof_to must be a node in ra's class (the winner).
        // Without swap: ra = root(repr[entry.a]), so entry.a is in ra's class.
        // With swap:    ra = original root(repr[entry.b]), so entry.b is in ra's class.
        // Using (repr_[entry.a] == ra) is WRONG after the while-loop chase,
        // because repr_[entry.a] still holds the pre-chase intermediate value.
        NodeId proof_from = rb;
        NodeId proof_to   = swapped ? entry.b : entry.a;
        set_proof_edge(proof_from, proof_to, entry.label);

        do_merge(ra, rb);
    }
}

void CC::do_merge(NodeId ra, NodeId rb) {
    // (Proof edge already set in propagate; this function only does the UF merge)

    // Update repr for all nodes in rb's class
    for (NodeId c : class_list_[rb]) {
        record_set_repr(c, rb); // old repr was rb
        repr_[c] = ra;
    }

    // Merge class lists and record a single undo action that can restore rb's list.
    uint32_t count = static_cast<uint32_t>(class_list_[rb].size());
    for (NodeId c : class_list_[rb]) {
        class_list_[ra].push_back(c);
    }
    class_list_[rb].clear();
    record_class_list_merge(ra, rb, count);

    // Scan use_list of rb, checking lookup with updated reprs
    for (EqId eq_id : use_list_[rb]) {
        const Equation& eq = equations_[eq_id];
        if (eq.kind != EqKind::App) continue;

        NodeId fn_r  = repr_[eq.app_fn];
        NodeId arg_r = repr_[eq.app_arg];
        auto key     = std::make_pair(fn_r, arg_r);

        auto it = lookup_.find(key);
        if (it != lookup_.end()) {
            EqId existing  = it->second;
            NodeId lhs1    = equations_[eq_id].lhs;
            NodeId lhs2    = equations_[existing].lhs;
            if (repr_[lhs1] != repr_[lhs2]) {
                pending_.push_back(PendingEntry{lhs1, lhs2,
                                                CongruenceLabel{existing, eq_id}});
            }
        } else {
            lookup_[key] = eq_id;
            record_lookup_remove(key);
            use_list_[ra].push_back(eq_id);
            record_use_list_pop(ra);
        }
    }
}

void CC::set_proof_edge(NodeId from, NodeId to, const EdgeLabel& label) {
    assert(proof_parent_[from] == NULL_NODE && "proof edge set twice — proof forest corrupted");
    proof_parent_[from] = to;
    proof_label_[from]  = label;
    record_proof_edge(from);
}

// ============================================================================
// Backtracking
// ============================================================================

void CC::push_level() {
    ++current_level_;
    trail_.emplace_back();
}

void CC::pop_level(size_t target_level) {
    while (current_level_ > target_level) {
        for (auto it = trail_[current_level_].rbegin();
             it != trail_[current_level_].rend(); ++it) {
            const UndoAction& ua = *it;
            switch (ua.kind) {
            case UndoAction::Kind::SetRepr:
                repr_[ua.node] = ua.old_val;
                break;
            case UndoAction::Kind::ClassListMerge:
                // Move the last `extra` elements from class_list_[node=ra]
                // back to class_list_[old_val=rb].
                for (uint32_t i = 0; i < ua.extra; ++i) {
                    class_list_[ua.old_val].push_back(class_list_[ua.node].back());
                    class_list_[ua.node].pop_back();
                }
                break;
            case UndoAction::Kind::UseListPop:
                use_list_[ua.node].pop_back();
                break;
            case UndoAction::Kind::LookupRemove:
                lookup_.erase(ua.lookup_key);
                break;
            case UndoAction::Kind::ProofEdge:
                proof_parent_[ua.node] = NULL_NODE;
                proof_label_[ua.node]  = EdgeLabel{DirectLabel{NULL_EQ}};
                break;
            case UndoAction::Kind::EquationPop:
                equations_.pop_back();
                break;
            }
        }
        trail_[current_level_].clear();
        --current_level_;
    }
    // Clear any pending entries (they belong to the popped level)
    pending_.clear();
}

// ============================================================================
// Undo recording
// ============================================================================

void CC::record(UndoAction ua) {
    trail_[current_level_].push_back(ua);
}

void CC::record_set_repr(NodeId node, NodeId old_repr) {
    UndoAction ua;
    ua.kind    = UndoAction::Kind::SetRepr;
    ua.node    = node;
    ua.old_val = old_repr;
    record(ua);
}

void CC::record_class_list_merge(NodeId ra, NodeId rb, uint32_t count) {
    UndoAction ua;
    ua.kind    = UndoAction::Kind::ClassListMerge;
    ua.node    = ra;
    ua.old_val = rb;
    ua.extra   = count;
    record(ua);
}

void CC::record_use_list_pop(NodeId r) {
    UndoAction ua;
    ua.kind = UndoAction::Kind::UseListPop;
    ua.node = r;
    record(ua);
}

void CC::record_lookup_remove(std::pair<NodeId,NodeId> key) {
    UndoAction ua;
    ua.kind       = UndoAction::Kind::LookupRemove;
    ua.lookup_key = key;
    record(ua);
}

void CC::record_proof_edge(NodeId node) {
    UndoAction ua;
    ua.kind = UndoAction::Kind::ProofEdge;
    ua.node = node;
    record(ua);
}

// ============================================================================
// Explain (§5)
// ============================================================================

// Find lowest common ancestor of a and b in the proof forest.
// Uses a generation-stamped scratch buffer to avoid per-call allocation.
NodeId CC::find_lca(NodeId a, NodeId b) {
    // Grow scratch lazily; a generation counter lets us skip the clear.
    if (lca_stamp_.size() < proof_parent_.size())
        lca_stamp_.resize(proof_parent_.size(), 0);
    if (++lca_gen_ == 0) {          // handle uint32_t wrap-around
        std::fill(lca_stamp_.begin(), lca_stamp_.end(), 0);
        ++lca_gen_;
    }

    // Stamp every ancestor of a (including a itself).
    NodeId cur = a;
    while (cur != NULL_NODE) {
        lca_stamp_[cur] = lca_gen_;
        NodeId p = proof_parent_[cur];
        if (p == NULL_NODE || p == cur) break;
        cur = p;
    }

    // Walk from b; first stamped node is the LCA.
    cur = b;
    while (cur != NULL_NODE) {
        if (lca_stamp_[cur] == lca_gen_) return cur;
        NodeId p = proof_parent_[cur];
        if (p == NULL_NODE || p == cur) break;
        cur = p;
    }
    if (cur != NULL_NODE && lca_stamp_[cur] == lca_gen_) return cur;
    return NULL_NODE;
}

void CC::explain_path(NodeId a, NodeId lca,
                       PathUF& uf,
                       std::deque<std::pair<NodeId,NodeId>>& pending_pairs,
                       std::vector<EqId>& result) {
    NodeId cur = a;
    // Use node identity for termination (not PathUF reps, which change under unite).
    while (cur != lca) {
        NodeId par = proof_parent_[cur];
        assert(par != NULL_NODE && "broken proof path to LCA");

        const EdgeLabel& label = proof_label_[cur];

        if (std::holds_alternative<DirectLabel>(label)) {
            EqId eq = std::get<DirectLabel>(label).eq;
            if (eq != NULL_EQ) result.push_back(eq);
        } else {
            const auto& cl = std::get<CongruenceLabel>(label);
            EqId eq1 = cl.eq1;
            EqId eq2 = cl.eq2;
            // eq1/eq2 are structural App equations, not SAT-level atomic equalities;
            // they are not added to result (build_conflict ignores App equations anyway).
            // We only use them to recover the argument nodes for recursive explanation.
            const Equation& e1 = equations_[eq1];
            const Equation& e2 = equations_[eq2];
            if (e1.kind == EqKind::App && e2.kind == EqKind::App) {
                if (e1.app_fn != e2.app_fn)
                    pending_pairs.push_back({e1.app_fn, e2.app_fn});
                if (e1.app_arg != e2.app_arg)
                    pending_pairs.push_back({e1.app_arg, e2.app_arg});
            }
        }

        uf.unite(cur, par);
        cur = par;
    }
}

std::vector<EqId> CC::explain(NodeId a, NodeId b) {
    assert(are_congruent(a, b) && "nodes are not congruent");

    std::vector<EqId> result;
    if (a == b) return result;

    PathUF uf;
    uf.init(proof_parent_.size());

    std::deque<std::pair<NodeId,NodeId>> worklist;
    worklist.push_back({a, b});

    while (!worklist.empty()) {
        auto [x, y] = worklist.front();
        worklist.pop_front();

        if (uf.find(x) == uf.find(y)) continue;

        NodeId lca = find_lca(x, y);
        assert(lca != NULL_NODE && "no LCA found — nodes must be congruent");

        explain_path(x, lca, uf, worklist, result);
        explain_path(y, lca, uf, worklist, result);
    }

    // Deduplicate
    std::sort(result.begin(), result.end());
    result.erase(std::unique(result.begin(), result.end()), result.end());
    result.erase(std::remove(result.begin(), result.end(), NULL_EQ), result.end());

    return result;
}

} // namespace llm2smt
