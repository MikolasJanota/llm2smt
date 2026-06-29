#pragma once

#include <map>
#include <optional>
#include <span>
#include <string>
#include <unordered_map>
#include <vector>

#include "sat/ipasir_up.h"
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
    int new_var() { return next_var_++; }

    int register_atom(const Atom& atom);
    void declare_real(const std::string& name);
    void set_fm_elim_order(std::string order);
    void set_conflict_minimize_limit(size_t limit);

    void notify_assignment(int lit, bool is_fixed) override;
    void notify_new_decision_level() override;
    void notify_backtrack(size_t new_level) override;
    const std::vector<int>& observed_vars() const override { return observed_vars_; }
    bool cb_check_found_model(const std::vector<int>& model) override;
    bool cb_has_external_clause(bool& is_forgettable) override;
    int cb_add_external_clause_lit() override;

    std::optional<Rational> value_of(const std::string& name) const;
    const std::vector<std::string>& real_decls() const { return real_decls_; }
    size_t last_conflict_size() const { return last_conflict_size_; }

private:
    struct Inequality {
        std::map<std::string, Rational> coeffs; // sum coeffs*x <= rhs
        Rational rhs;
        bool strict = false;
    };

    int next_var_ = 1;
    std::vector<int> observed_vars_;
    std::unordered_map<int, Atom> atoms_;
    std::map<std::string, int> atom_keys_;

    std::vector<int> trail_;
    std::vector<size_t> level_counts_{0};

    std::vector<int> conflict_clause_;
    size_t conflict_idx_ = 0;
    bool has_conflict_ = false;
    size_t last_conflict_size_ = 0;

    std::vector<std::string> real_decls_;
    std::unordered_map<std::string, bool> real_decl_seen_;
    std::map<std::string, Rational> last_model_;
    bool use_min_fill_elim_ = true;
    size_t conflict_minimize_limit_ = 64;

    static std::string atom_key(const Atom& atom);
    static void add_ineq_for_literal(const Atom& atom, int lit, std::vector<Inequality>& out);
    static void add_diseq_for_literal(const Atom& atom, int lit, std::vector<LinearExpr>& out);
    static bool feasible(std::vector<Inequality> ineqs,
                         std::map<std::string, Rational>* model,
                         bool use_min_fill_elim);
    static bool feasible_with_disequalities(std::vector<Inequality> ineqs,
                                            const std::vector<LinearExpr>& diseqs,
                                            size_t diseq_idx,
                                            std::map<std::string, Rational>* model,
                                            bool use_min_fill_elim);
    static bool solve_projected(std::vector<Inequality> ineqs,
                                std::vector<std::string> vars,
                                std::map<std::string, Rational>& model,
                                bool use_min_fill_elim);
    static bool choose_value_for(const std::string& var,
                                 const std::vector<Inequality>& ineqs,
                                 const std::map<std::string, Rational>& model,
                                 Rational& value);
    static bool check_ineqs(const std::vector<Inequality>& ineqs,
                            const std::map<std::string, Rational>& model);
    bool feasible_for_literals(const std::vector<int>& lits,
                               std::map<std::string, Rational>* model) const;
    std::vector<int> minimize_conflict(std::vector<int> active) const;
};

} // namespace llm2smt::lra
