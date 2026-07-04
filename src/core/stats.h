#pragma once

#include <cstdint>
#include <iomanip>
#include <ostream>
#include <string>

namespace llm2smt {

// Counters for major solver events.  Collected unconditionally (cost ≈ zero);
// printed only when --stats is passed on the command line.
struct Stats {
    // ── Preprocessor ───────────────────────────────────────────────────────
    uint64_t preproc_fmls_in         = 0; // assertions fed to the simplifier
    uint64_t preproc_fmls_true_out   = 0; // assertions simplified to True
    uint64_t preproc_fmls_false_out  = 0; // assertions simplified to False
    uint64_t preproc_forced_atoms    = 0; // atoms extracted as unit clauses
    uint64_t preproc_passes_run      = 0; // simplifier passes that changed something
    uint64_t preproc_diseq_folds     = 0; // Eq atoms folded false by known disequalities
    uint64_t preproc_bridge_eqs      = 0; // equalities derived by disjunction bridging
    uint64_t preproc_bridge_skipped  = 0; // Or nodes skipped by bridge size caps
    uint64_t preproc_simp_ms         = 0; // wall-clock ms for simplifier.run()
    uint64_t preproc_flush_ms        = 0; // wall-clock ms for flush_pending_fmls() (NNF+simp+encode)
    uint64_t preproc_finite_domain_amo_clauses = 0; // SAT AMO clauses from distinct endpoints
    uint64_t preproc_finite_domain_eq_def_clauses = 0; // SAT definitions for equalities between finite-domain terms
    uint64_t preproc_finite_domain_bound_clauses = 0; // SAT links between finite-domain choices and simple bounds
    uint64_t lra_bool_cache_hits     = 0; // QF_LRA Boolean compound cache hits
    uint64_t lra_bool_cache_hits_and = 0; // QF_LRA Boolean and cache hits
    uint64_t lra_bool_cache_hits_or  = 0; // QF_LRA Boolean or cache hits
    uint64_t lra_bool_cache_hits_ite = 0; // QF_LRA Boolean ite cache hits
    uint64_t lra_bool_cache_hits_eq  = 0; // QF_LRA Boolean/equality/distinct cache hits
    uint64_t lra_eq_cache_hits       = 0; // QF_LRA arithmetic equality definition cache hits
    uint64_t lra_atom_cache_hits     = 0; // QF_LRA elementary arithmetic atom cache hits
    uint64_t lra_term_cache_hits     = 0; // QF_LRA arithmetic term normalization cache hits
    uint64_t lra_ite_terms           = 0; // QF_LRA arithmetic ite auxiliary terms introduced
    uint64_t lra_eq_elim_rows        = 0; // top-level equality rows processed by QF_LRA elimination
    uint64_t lra_eq_elim_vars        = 0; // variables eliminated by QF_LRA equality elimination
    uint64_t lra_eq_elim_contradictions = 0; // inconsistent equality rows detected before SAT search
    uint64_t lra_dl_fast_path_attempts = 0; // top-level QF_LRA assertion batches checked by the DL/UTVPI pre-encoder
    uint64_t lra_dl_fast_path_unsats = 0; // batches proved UNSAT by the DL/UTVPI pre-encoder
    uint64_t lra_dl_fast_path_fallbacks = 0; // batches passed to normal SAT/LRA encoding after the fast-path check
    uint64_t lra_dl_fast_path_atoms = 0; // arithmetic atoms accepted by the DL/UTVPI pre-encoder
    uint64_t lra_dl_fast_path_rejected = 0; // batches containing guarded or non-graph arithmetic outside the fast path
    uint64_t lra_const_bool_folds    = 0; // QF_LRA Boolean constants/connectives folded before Tseitin encoding
    uint64_t lra_const_arith_folds   = 0; // QF_LRA arithmetic atoms folded to constants before LRA registration
    uint64_t lra_ite_terms_simplified = 0; // QF_LRA arithmetic ite auxiliaries avoided by local simplification

    // ── SAT encoding ───────────────────────────────────────────────────────
    uint64_t sat_vars                = 0; // SAT variables allocated through the wrapper
    uint64_t sat_clauses             = 0; // clauses added through the wrapper
    uint64_t sat_clause_lits         = 0; // total literals across input clauses
    uint64_t sat_binary_clauses      = 0; // binary clauses added through the wrapper
    uint64_t sat_unit_clauses        = 0; // unit clauses added through the wrapper

    // ── EUF theory ─────────────────────────────────────────────────────────
    uint64_t euf_assignments         = 0; // notify_assignment callbacks
    uint64_t euf_eq_assignments      = 0; // positive (equality) assignments
    uint64_t euf_diseq_assignments   = 0; // negative (disequality) assignments
    uint64_t euf_check_model_calls   = 0; // cb_check_found_model callbacks
    uint64_t euf_conflicts           = 0; // theory lemmas (conflict clauses) generated
    uint64_t euf_conflict_lits_total = 0; // total literals across all conflict clauses
    uint64_t euf_prop_candidates_considered = 0; // equality atoms inspected by propagation discovery

    // ── LRA theory ─────────────────────────────────────────────────────────
    uint64_t lra_assignments         = 0; // notify_assignment callbacks on arithmetic atoms
    uint64_t lra_check_calls         = 0; // simplex consistency checks
    uint64_t lra_final_checks        = 0; // complete SAT models accepted by the LRA final check
    uint64_t lra_pivots              = 0; // successful tableau pivots
    uint64_t lra_check_max_pivots    = 0; // maximum pivots used in one simplex check call
    uint64_t lra_pivot_candidates    = 0; // eligible entering variables inspected by pivot heuristics
    uint64_t lra_pivot_min_column_choices = 0; // pivots selected by the min-column heuristic
    uint64_t lra_pivot_bland_fallbacks = 0; // pivots selected after fallback to Bland/min-var
    uint64_t lra_conflicts           = 0; // theory conflict clauses generated
    uint64_t lra_conflict_lits_total = 0; // total literals across all LRA conflicts
    uint64_t lra_propagations        = 0; // theory literals delivered to SAT
    uint64_t lra_prop_candidates_considered = 0; // elementary atoms inspected by propagation discovery
    uint64_t lra_row_prop_candidates_considered = 0; // row-bound atoms inspected by propagation discovery
    uint64_t lra_row_bound_propagations = 0; // literals enqueued from derived row bounds
    uint64_t lra_simple_graph_atoms = 0; // atoms recognized as unary/difference/UTVPI graph constraints
    uint64_t lra_simple_graph_edges = 0; // active graph edges inspected during the last graph discovery
    uint64_t lra_simple_graph_candidates = 0; // graph atom candidates inspected by propagation discovery
    uint64_t lra_simple_graph_propagations = 0; // literals enqueued from graph shortest-path implications
    uint64_t lra_simple_graph_conflicts = 0; // conflicts found by graph negative-cycle or contradicted propagation
    uint64_t lra_simple_graph_conflict_checks = 0; // negative-cycle checks performed on active graph edges
    uint64_t lra_simple_graph_clean_skips = 0; // graph conflict checks skipped because active edges were unchanged
    uint64_t lra_simple_graph_active_edges = 0; // current active graph edges maintained incrementally
    uint64_t lra_simple_graph_rebuilds_avoided = 0; // active graph scans avoided by incremental edge maintenance
    uint64_t lra_simple_graph_budget_cutoffs = 0; // graph discovery calls stopped by candidate budget
    uint64_t lra_simple_graph_skipped = 0; // LRA atoms not representable as unary/DL/UTVPI graph constraints
    uint64_t lra_branch_decisions     = 0; // finite-domain branch hints returned to SAT
    uint64_t lra_atoms               = 0; // unique elementary LRA atoms registered
    uint64_t lra_term_vars           = 0; // unique tableau term variables introduced
    uint64_t lra_real_vars           = 0; // unique user/internal Real variables declared
    uint64_t lra_lower_bound_applications = 0; // stronger lower bounds applied to tableau variables
    uint64_t lra_upper_bound_applications = 0; // stronger upper bounds applied to tableau variables
    uint64_t lra_fixed_equalities    = 0; // positive equality atoms applied as lower+upper bounds
    uint64_t lra_offset_equalities   = 0; // equality atoms of the form x - y + c = 0
    uint64_t lra_max_rows            = 0; // maximum tableau row count
    uint64_t lra_max_columns         = 0; // maximum tableau variable count

    // ── Overall timing ──────────────────────────────────────────────────────
    uint64_t total_ms                = 0; // wall-clock ms for the full solve (set in main)

    void print(std::ostream& out) const {
        static constexpr int kColWidth = 30;
        auto row = [&](const std::string& name, uint64_t val) {
            out << "  " << std::left << std::setw(kColWidth) << name << val << "\n";
        };
        out << "[stats]\n";
        out << "  -- timing (ms) --\n";
        row("total_ms",                 total_ms);
        row("preproc.flush_ms",         preproc_flush_ms);
        row("preproc.simp_ms",          preproc_simp_ms);
        out << "  -- preprocessor --\n";
        row("preproc.fmls_in",          preproc_fmls_in);
        row("preproc.fmls_true_out",    preproc_fmls_true_out);
        row("preproc.fmls_false_out",   preproc_fmls_false_out);
        row("preproc.forced_atoms",     preproc_forced_atoms);
        row("preproc.passes_run",       preproc_passes_run);
        row("preproc.diseq_folds",      preproc_diseq_folds);
        row("preproc.bridge_eqs",       preproc_bridge_eqs);
        row("preproc.bridge_skipped",   preproc_bridge_skipped);
        row("preproc.finite_domain_amo", preproc_finite_domain_amo_clauses);
        row("preproc.finite_domain_eq_defs", preproc_finite_domain_eq_def_clauses);
        row("preproc.finite_domain_bounds", preproc_finite_domain_bound_clauses);
        row("lra.bool_cache_hits",      lra_bool_cache_hits);
        row("lra.bool_cache_hits.and",  lra_bool_cache_hits_and);
        row("lra.bool_cache_hits.or",   lra_bool_cache_hits_or);
        row("lra.bool_cache_hits.ite",  lra_bool_cache_hits_ite);
        row("lra.bool_cache_hits.eq",   lra_bool_cache_hits_eq);
        row("lra.eq_cache_hits",        lra_eq_cache_hits);
        row("lra.atom_cache_hits",      lra_atom_cache_hits);
        row("lra.term_cache_hits",      lra_term_cache_hits);
        row("lra.ite_terms",            lra_ite_terms);
        row("lra.eq_elim_rows",         lra_eq_elim_rows);
        row("lra.eq_elim_vars",         lra_eq_elim_vars);
        row("lra.eq_elim_contradictions", lra_eq_elim_contradictions);
        row("lra.dl_fast_path_attempts", lra_dl_fast_path_attempts);
        row("lra.dl_fast_path_unsats",  lra_dl_fast_path_unsats);
        row("lra.dl_fast_path_fallbacks", lra_dl_fast_path_fallbacks);
        row("lra.dl_fast_path_atoms",   lra_dl_fast_path_atoms);
        row("lra.dl_fast_path_rejected", lra_dl_fast_path_rejected);
        row("lra.const_bool_folds",     lra_const_bool_folds);
        row("lra.const_arith_folds",    lra_const_arith_folds);
        row("lra.ite_terms_simplified", lra_ite_terms_simplified);
        out << "  -- sat encoding --\n";
        row("sat.vars",                 sat_vars);
        row("sat.clauses",              sat_clauses);
        row("sat.clause_lits",          sat_clause_lits);
        row("sat.binary_clauses",       sat_binary_clauses);
        row("sat.unit_clauses",         sat_unit_clauses);
        out << "  -- euf theory --\n";
        row("euf.assignments",          euf_assignments);
        row("euf.eq_assignments",       euf_eq_assignments);
        row("euf.diseq_assignments",    euf_diseq_assignments);
        row("euf.check_model_calls",    euf_check_model_calls);
        row("euf.conflicts",            euf_conflicts);
        row("euf.conflict_lits_total",  euf_conflict_lits_total);
        row("euf.prop_candidates_considered", euf_prop_candidates_considered);
        out << "  -- lra theory --\n";
        row("lra.assignments",          lra_assignments);
        row("lra.check_calls",          lra_check_calls);
        row("lra.final_checks",         lra_final_checks);
        row("lra.pivots",               lra_pivots);
        row("lra.check_max_pivots",     lra_check_max_pivots);
        row("lra.pivot_candidates",     lra_pivot_candidates);
        row("lra.pivot_min_column_choices", lra_pivot_min_column_choices);
        row("lra.pivot_bland_fallbacks", lra_pivot_bland_fallbacks);
        row("lra.conflicts",            lra_conflicts);
        row("lra.conflict_lits_total",  lra_conflict_lits_total);
        row("lra.propagations",         lra_propagations);
        row("lra.prop_candidates_considered", lra_prop_candidates_considered);
        row("lra.row_prop_candidates_considered", lra_row_prop_candidates_considered);
        row("lra.row_bound_propagations", lra_row_bound_propagations);
        row("lra.simple_graph_atoms",    lra_simple_graph_atoms);
        row("lra.simple_graph_edges",    lra_simple_graph_edges);
        row("lra.simple_graph_candidates", lra_simple_graph_candidates);
        row("lra.simple_graph_propagations", lra_simple_graph_propagations);
        row("lra.simple_graph_conflicts", lra_simple_graph_conflicts);
        row("lra.simple_graph_checks", lra_simple_graph_conflict_checks);
        row("lra.simple_graph_clean_skips", lra_simple_graph_clean_skips);
        row("lra.simple_graph_active", lra_simple_graph_active_edges);
        row("lra.simple_graph_reuse", lra_simple_graph_rebuilds_avoided);
        row("lra.simple_graph_budget_cutoffs", lra_simple_graph_budget_cutoffs);
        row("lra.simple_graph_skipped",  lra_simple_graph_skipped);
        row("lra.branch_decisions",       lra_branch_decisions);
        row("lra.atoms",                lra_atoms);
        row("lra.term_vars",            lra_term_vars);
        row("lra.real_vars",            lra_real_vars);
        row("lra.lower_bound_applications", lra_lower_bound_applications);
        row("lra.upper_bound_applications", lra_upper_bound_applications);
        row("lra.fixed_equalities",     lra_fixed_equalities);
        row("lra.offset_equalities",    lra_offset_equalities);
        row("lra.max_rows",             lra_max_rows);
        row("lra.max_columns",          lra_max_columns);
        out << "  -- z3-shaped --\n";
        row("mk-bool-var",              sat_vars);
        row("mk-clause",                sat_clauses);
        row("mk-clause-binary",         sat_binary_clauses);
        row("units",                    sat_unit_clauses);
        row("num-checks",               lra_check_calls);
        row("final-checks",             lra_final_checks);
        row("arith-conflicts",          lra_conflicts);
        row("arith-bound-propagations-lp", lra_propagations);
        row("arith-lower",              lra_lower_bound_applications);
        row("arith-upper",              lra_upper_bound_applications);
        row("arith-fixed-eqs",          lra_fixed_equalities);
        row("arith-offset-eqs",         lra_offset_equalities);
        row("arith-make-feasible",      lra_pivots);
        row("arith-max-rows",           lra_max_rows);
        row("arith-max-columns",        lra_max_columns);
    }
};

} // namespace llm2smt
