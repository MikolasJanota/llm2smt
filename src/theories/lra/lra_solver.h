#pragma once

#include <map>
#include <optional>
#include <set>
#include <span>
#include <string>
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
    explicit LraSolver(Stats* stats = nullptr) : stats_(stats) {}

    int new_var() {
        if (stats_) ++stats_->sat_vars;
        return next_var_++;
    }

    int register_atom(const Atom& atom);
    void declare_real(const std::string& name);
    void set_propagation(bool v) { propagation_enabled_ = v; }
    void set_incremental_prop_scan(bool v) { incremental_prop_scan_ = v; }

    void notify_assignment(int lit, bool is_fixed) override;
    void notify_new_decision_level() override;
    void notify_backtrack(size_t new_level) override;
    const std::vector<int>& observed_vars() const override { return observed_vars_; }
    bool cb_check_found_model(const std::vector<int>& model) override;
    bool cb_has_external_clause(bool& is_forgettable) override;
    int cb_add_external_clause_lit() override;
    int cb_propagate() override;
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

    int next_var_ = 1;
    std::vector<int> observed_vars_;
    std::unordered_map<int, Atom> atoms_;
    std::map<std::string, int> atom_keys_;
    std::unordered_map<int, ElementaryAtom> elementary_atoms_;
    std::vector<std::vector<int>> atoms_by_var_;

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
    std::vector<int> row_of_basic_;
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
    int reason_serving_lit_ = 0;
    size_t reason_serving_idx_ = 0;

    static std::string atom_key(const Atom& atom);
    int ensure_real_var(const std::string& name);
    int ensure_term_var(const LinearExpr& expr);
    int new_tableau_var(bool basic);
    static DeltaRational strict_value(const Rational& q, BoundKind kind, bool strict);
    static Relation negate_rel(Relation r);
    bool apply_bound(int var, BoundKind kind, const DeltaRational& value, int source_lit);
    void set_conflict(std::vector<int> clause);
    bool check();
    void update(int x, const DeltaRational& v);
    bool pivot_and_update(int basic, int nonbasic, const DeltaRational& value);
    bool pivot(int basic, int nonbasic);
    void recompute_basic_values();
    std::vector<int> explain_lower_conflict(int basic) const;
    std::vector<int> explain_upper_conflict(int basic) const;
    void rebuild_model();
    Rational choose_delta() const;
    void discover_bound_propagations();
    void mark_all_bound_vars_for_propagation();
    bool feasible_for_literals(const std::vector<int>& lits,
                               std::map<std::string, Rational>* model) const;
    std::vector<int> minimize_conflict(std::vector<int> active) const;
};

} // namespace llm2smt::lra
