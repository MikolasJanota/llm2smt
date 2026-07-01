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
    uint64_t lra_bool_cache_hits     = 0; // QF_LRA Boolean compound cache hits
    uint64_t lra_bool_cache_hits_and = 0; // QF_LRA Boolean and cache hits
    uint64_t lra_bool_cache_hits_or  = 0; // QF_LRA Boolean or cache hits
    uint64_t lra_bool_cache_hits_ite = 0; // QF_LRA Boolean ite cache hits
    uint64_t lra_bool_cache_hits_eq  = 0; // QF_LRA Boolean/equality/distinct cache hits
    uint64_t lra_eq_cache_hits       = 0; // QF_LRA arithmetic equality definition cache hits
    uint64_t lra_atom_cache_hits     = 0; // QF_LRA elementary arithmetic atom cache hits
    uint64_t lra_ite_terms           = 0; // QF_LRA arithmetic ite auxiliary terms introduced

    // ── SAT encoding ───────────────────────────────────────────────────────
    uint64_t sat_vars                = 0; // SAT variables allocated through the wrapper
    uint64_t sat_clauses             = 0; // clauses added through the wrapper
    uint64_t sat_clause_lits         = 0; // total literals across input clauses

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
    uint64_t lra_pivots              = 0; // successful tableau pivots
    uint64_t lra_conflicts           = 0; // theory conflict clauses generated
    uint64_t lra_conflict_lits_total = 0; // total literals across all LRA conflicts
    uint64_t lra_propagations        = 0; // theory literals delivered to SAT
    uint64_t lra_prop_candidates_considered = 0; // elementary atoms inspected by propagation discovery
    uint64_t lra_atoms               = 0; // unique elementary LRA atoms registered
    uint64_t lra_term_vars           = 0; // unique tableau term variables introduced
    uint64_t lra_real_vars           = 0; // unique user/internal Real variables declared

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
        row("lra.bool_cache_hits",      lra_bool_cache_hits);
        row("lra.bool_cache_hits.and",  lra_bool_cache_hits_and);
        row("lra.bool_cache_hits.or",   lra_bool_cache_hits_or);
        row("lra.bool_cache_hits.ite",  lra_bool_cache_hits_ite);
        row("lra.bool_cache_hits.eq",   lra_bool_cache_hits_eq);
        row("lra.eq_cache_hits",        lra_eq_cache_hits);
        row("lra.atom_cache_hits",      lra_atom_cache_hits);
        row("lra.ite_terms",            lra_ite_terms);
        out << "  -- sat encoding --\n";
        row("sat.vars",                 sat_vars);
        row("sat.clauses",              sat_clauses);
        row("sat.clause_lits",          sat_clause_lits);
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
        row("lra.pivots",               lra_pivots);
        row("lra.conflicts",            lra_conflicts);
        row("lra.conflict_lits_total",  lra_conflict_lits_total);
        row("lra.propagations",         lra_propagations);
        row("lra.prop_candidates_considered", lra_prop_candidates_considered);
        row("lra.atoms",                lra_atoms);
        row("lra.term_vars",            lra_term_vars);
        row("lra.real_vars",            lra_real_vars);
    }
};

} // namespace llm2smt
