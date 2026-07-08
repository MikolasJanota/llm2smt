#pragma once

#include <map>
#include <optional>
#include <set>
#include <span>
#include <string>
#include <stdexcept>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "sat/ipasir_up.h"
#include "core/stats.h"
#include "theories/lra/rational.h"

namespace llm2smt::lra {

struct LinearExpr {
    std::map<std::string, Rational> coeffs;
    Rational constant{0};

    void add_var(const std::string& name, const Rational& coeff);
    void add(const LinearExpr& other, const Rational& scale = Rational(1));
    void scale(const Rational& q);
};

enum class Relation { Le, Lt, Ge, Gt, Eq, Ne };

struct Atom {
    LinearExpr lhs_minus_rhs;
    Relation rel;
};

class LraSolver : public ExternalPropagator {
public:
    enum class PivotHeuristic { MinVar, MinColumn };
    enum class RdlPropagation { Off, Cotton };

    explicit LraSolver(Stats* stats = nullptr) : stats_(stats) {}

    int new_var() {
        if (stats_) ++stats_->sat_vars;
        return next_var_++;
    }

    int register_atom(const Atom& atom);
    void declare_real(const std::string& name);
    void set_propagation(bool v) { propagation_enabled_ = v; }
    void set_incremental_prop_scan(bool v) { incremental_prop_scan_ = v; }
    void set_row_bound_propagation(bool v) { row_bound_propagation_ = v; }
    void set_row_bound_dirty_scan(bool v) { row_bound_dirty_scan_ = v; }
    void set_row_bound_indexed_dirty_scan(bool v) { row_bound_indexed_dirty_scan_ = v; }
    void set_row_bound_propagation_budget(size_t v) { row_bound_propagation_budget_ = v; }
    void set_row_bound_min_hit_rate(size_t v) { row_bound_min_hit_rate_ = v; }
    void set_row_bound_hit_window(size_t v) { row_bound_hit_window_ = v; }
    void set_tableau_row_index(bool v) { tableau_row_index_ = v; }
    void set_pivot_heuristic(const std::string& name) {
        if (name == "min-var") pivot_heuristic_ = PivotHeuristic::MinVar;
        else if (name == "min-column") pivot_heuristic_ = PivotHeuristic::MinColumn;
        else throw std::invalid_argument("unknown QF_LRA pivot heuristic: " + name);
    }
    void set_pivot_bland_after(size_t v) { pivot_bland_after_ = v; }
    void set_simple_graph_conflicts(bool v) { simple_graph_conflicts_ = v; }
    void set_simple_graph_propagation(bool v) {
        simple_graph_propagation_ = v;
        if (v) simple_graph_conflicts_ = true;
    }
    void set_simple_graph_budget(size_t v) { simple_graph_budget_ = v; }
    void set_rdl_propagation(const std::string& name) {
        if (name == "off") rdl_propagation_ = RdlPropagation::Off;
        else if (name == "cotton") rdl_propagation_ = RdlPropagation::Cotton;
        else throw std::invalid_argument("unknown QF_LRA RDL propagation mode: " + name);
    }
    void set_rdl_propagation_budget(size_t v) { rdl_propagation_budget_ = v; }
    void add_branch_hint(int lit);

    void notify_assignment(int lit, bool is_fixed) override;
    void notify_new_decision_level() override;
    void notify_backtrack(size_t new_level) override;
    const std::vector<int>& observed_vars() const override { return observed_vars_; }
    bool cb_check_found_model(const std::vector<int>& model) override;
    bool cb_has_external_clause(bool& is_forgettable) override;
    int cb_add_external_clause_lit() override;
    int cb_propagate() override;
    int cb_decide() override;
    int cb_add_reason_clause_lit(int propagated_lit) override;

    std::optional<Rational> value_of(const std::string& name) const;
    const std::vector<std::string>& real_decls() const { return real_decls_; }
    size_t last_conflict_size() const { return last_conflict_size_; }

private:
    enum class BoundKind { Lower, Upper };

    struct TableauRow {
        DeltaRational constant{Rational(0)};
        std::map<int, Rational> coeffs; // basic = constant + sum coeff * nonbasic
    };

    struct Bound {
        bool active = false;
        DeltaRational value;
        int source_lit = 0;
    };

    struct BoundTrailEntry {
        int var = 0;
        BoundKind kind = BoundKind::Lower;
        Bound previous;
    };

    struct ElementaryAtom {
        int var = 0;
        bool equality = false;
        BoundKind positive_kind = BoundKind::Upper;
        DeltaRational positive_value;
        int positive_source_lit = 0;
        int negative_source_lit = 0;
    };

    struct BoundAtomRef {
        int sat_var = 0;
        DeltaRational value;
    };

    struct GraphEdgeTemplate {
        int from = 0;
        int to = 0;
        DeltaRational weight;
    };

    struct SimpleGraphAtom {
        std::vector<GraphEdgeTemplate> positive_edges;
        std::vector<GraphEdgeTemplate> negative_edges;
    };

    struct RdlAtom {
        std::vector<GraphEdgeTemplate> positive_edges;
        std::vector<GraphEdgeTemplate> negative_edges;
    };

    struct ActiveGraphEdge {
        int from = 0;
        int to = 0;
        DeltaRational weight;
        int source_lit = 0;
    };

    struct ShortestPaths {
        std::vector<std::optional<DeltaRational>> dist;
        std::vector<int> pred_edge;
    };

    enum class RdlLabel { Lambda, Sigma, Pi, Delta };

    int next_var_ = 1;
    std::vector<int> observed_vars_;
    std::vector<int> atom_assignment_; // indexed by SAT variable: -1 false, 0 unassigned, 1 true
    std::unordered_map<int, Atom> atoms_;
    std::map<std::string, int> atom_keys_;
    std::unordered_map<int, ElementaryAtom> elementary_atoms_;
    std::vector<std::vector<int>> atoms_by_var_;
    std::vector<std::vector<BoundAtomRef>> lower_atoms_by_var_;
    std::vector<std::vector<BoundAtomRef>> upper_atoms_by_var_;

    std::vector<int> trail_;
    std::vector<size_t> level_counts_{0};
    std::vector<BoundTrailEntry> bound_trail_;
    std::vector<size_t> bound_level_counts_{0};

    std::vector<int> conflict_clause_;
    size_t conflict_idx_ = 0;
    bool has_conflict_ = false;
    size_t last_conflict_size_ = 0;

    std::vector<std::string> real_decls_;
    std::unordered_map<std::string, bool> real_decl_seen_;
    std::map<std::string, Rational> last_model_;
    bool propagation_enabled_ = true;
    bool incremental_prop_scan_ = true;
    bool row_bound_propagation_ = false;
    bool row_bound_dirty_scan_ = false;
    bool row_bound_indexed_dirty_scan_ = false;
    bool tableau_row_index_ = false;
    PivotHeuristic pivot_heuristic_ = PivotHeuristic::MinVar;
    size_t pivot_bland_after_ = 0;
    size_t row_bound_propagation_budget_ = 0;
    size_t row_bound_min_hit_rate_ = 0;
    size_t row_bound_hit_window_ = 100000;
    size_t row_bound_window_candidates_ = 0;
    size_t row_bound_window_enqueues_ = 0;
    bool row_bound_hit_cutoff_ = false;
    bool simple_graph_conflicts_ = false;
    bool simple_graph_propagation_ = false;
    size_t simple_graph_budget_ = 20000;
    RdlPropagation rdl_propagation_ = RdlPropagation::Off;
    size_t rdl_propagation_budget_ = 20000;
    size_t conflict_minimize_limit_ = 64;
    Stats* stats_ = nullptr;
    bool tableau_dirty_ = false;

    int next_lra_var_ = 0;
    std::unordered_map<std::string, int> real_to_var_;
    std::vector<std::string> var_to_real_;
    std::vector<bool> is_basic_;
    std::vector<int> basic_vars_;
    std::vector<int> nonbasic_vars_;
    std::vector<TableauRow> rows_;
    std::vector<int> row_basic_;
    std::vector<int> row_of_basic_;
    std::vector<std::vector<int>> rows_by_var_;
    std::vector<DeltaRational> beta_;
    std::vector<Bound> lower_;
    std::vector<Bound> upper_;
    std::map<std::string, int> term_var_keys_;

    std::vector<int> prop_queue_;
    size_t prop_head_ = 0;
    std::unordered_set<int> prop_enqueued_;
    std::unordered_map<int, std::vector<int>> reason_clauses_;
    std::vector<int> prop_dirty_vars_;
    std::vector<bool> prop_var_dirty_;
    std::vector<int> branch_hints_;
    std::unordered_set<int> branch_hints_seen_;
    size_t branch_hint_head_ = 0;
    int reason_serving_lit_ = 0;
    size_t reason_serving_idx_ = 0;
    std::unordered_map<int, SimpleGraphAtom> simple_graph_atoms_;
    std::vector<ActiveGraphEdge> active_simple_graph_edges_;
    std::vector<size_t> graph_edge_level_counts_{0};
    bool active_simple_graph_dirty_ = false;
    std::unordered_map<int, RdlAtom> rdl_atoms_;
    std::vector<ActiveGraphEdge> active_rdl_edges_;
    std::vector<size_t> rdl_edge_level_counts_{0};
    std::vector<size_t> rdl_sigma_edge_indices_;
    std::unordered_map<int, RdlLabel> rdl_labels_;

    bool row_index_enabled() const { return row_bound_indexed_dirty_scan_ || tableau_row_index_; }
    bool simple_graph_conflicts_enabled() const { return simple_graph_conflicts_ || simple_graph_propagation_; }
    static std::string atom_key(const Atom& atom);
    int ensure_real_var(const std::string& name);
    int ensure_term_var(const LinearExpr& expr);
    int new_tableau_var(bool basic);
    static DeltaRational strict_value(const Rational& q, BoundKind kind, bool strict);
    static Relation negate_rel(Relation r);
    void register_row_coeffs(int row_idx);
    void unregister_row_coeffs(int row_idx);
    void replace_sorted_var(std::vector<int>& xs, int old_v, int new_v);
    bool apply_bound(int var, BoundKind kind, const DeltaRational& value, int source_lit);
    void set_conflict(std::vector<int> clause);
    bool check();
    void update(int x, const DeltaRational& v);
    bool pivot_and_update(int basic, int nonbasic, const DeltaRational& value);
    bool pivot(int basic, int nonbasic);
    int choose_entering_var(int bad, bool below, bool bland_mode, DeltaRational& target);
    size_t column_length(int var) const;
    std::vector<int> explain_lower_conflict(int basic) const;
    std::vector<int> explain_upper_conflict(int basic) const;
    void rebuild_model();
    Rational choose_delta() const;
    void discover_bound_propagations();
    void discover_row_bound_propagations();
    void discover_simple_graph_propagations(const std::vector<int>* model = nullptr);
    void detect_simple_graph_conflict(const std::vector<int>* model = nullptr);
    void add_active_simple_graph_edges(int sat_var, int lit);
    void mark_all_bound_vars_for_propagation();
    int current_lit_value(int lit) const;
    bool propagation_already_known(int lit, bool row_bound, bool count_duplicate = true);
    bool enqueue_propagation(int lit, std::vector<int> reason, bool row_bound);
    bool enqueue_graph_propagation(int lit, std::vector<int> reason);
    bool feasible_for_literals(const std::vector<int>& lits,
                               std::map<std::string, Rational>* model) const;
    std::vector<int> minimize_conflict(std::vector<int> active) const;
    int graph_node_for_var(int var, bool negated) const;
    int graph_zero_node() const { return 0; }
    size_t graph_node_count() const;
    std::optional<SimpleGraphAtom> make_simple_graph_atom(const Atom& atom);
    std::optional<RdlAtom> make_rdl_atom(const Atom& atom);
    std::vector<ActiveGraphEdge> active_simple_graph_edges(const std::vector<int>* model) const;
    std::vector<ActiveGraphEdge> active_rdl_edges(const std::vector<int>* model) const;
    std::optional<ShortestPaths> shortest_paths_from(
        int source, const std::vector<ActiveGraphEdge>& edges, size_t node_count,
        bool count_rdl_stats = false) const;
    std::optional<ShortestPaths> shortest_paths_from_excluding(
        int source, const std::vector<ActiveGraphEdge>& edges, size_t node_count,
        size_t skip_edge, bool count_rdl_stats = false) const;
    std::optional<ShortestPaths> shortest_paths_from_disabled(
        int source, const std::vector<ActiveGraphEdge>& edges, size_t node_count,
        const std::vector<char>& disabled_edges, bool count_rdl_stats = false) const;
    std::optional<ShortestPaths> shortest_paths_to(
        int target, const std::vector<ActiveGraphEdge>& edges, size_t node_count,
        bool count_rdl_stats = false) const;
    std::optional<ShortestPaths> shortest_paths_to_excluding(
        int target, const std::vector<ActiveGraphEdge>& edges, size_t node_count,
        size_t skip_edge, bool count_rdl_stats = false) const;
    std::optional<ShortestPaths> shortest_paths_to_disabled(
        int target, const std::vector<ActiveGraphEdge>& edges, size_t node_count,
        const std::vector<char>& disabled_edges, bool count_rdl_stats = false) const;
    std::vector<int> graph_path_reason(
        int source, int target, const ShortestPaths& paths,
        const std::vector<ActiveGraphEdge>& edges) const;
    std::vector<int> graph_negative_cycle_reason(
        const std::vector<ActiveGraphEdge>& edges, size_t node_count) const;
    bool rdl_propagation_enabled() const { return rdl_propagation_ == RdlPropagation::Cotton; }
    int rdl_node_for_var(int var) const { return var + 1; }
    int rdl_zero_node() const { return 0; }
    size_t rdl_node_count() const { return 1 + static_cast<size_t>(next_lra_var_); }
    void add_active_rdl_edges(int sat_var, int lit);
    void rebuild_rdl_sigma_from_active();
    void discover_rdl_propagations(const std::vector<int>* model = nullptr);
    bool enqueue_rdl_propagation(int lit, std::vector<int> reason);
};

} // namespace llm2smt::lra
