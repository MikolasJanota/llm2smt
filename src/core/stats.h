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
    uint64_t preproc_simp_ms         = 0; // wall-clock ms for simplifier.run()
    uint64_t preproc_flush_ms        = 0; // wall-clock ms for flush_pending_fmls() (NNF+simp+encode)
    uint64_t preproc_finite_domain_amo_clauses = 0; // SAT AMO clauses from distinct endpoints

    // ── EUF theory ─────────────────────────────────────────────────────────
    uint64_t euf_assignments         = 0; // notify_assignment callbacks
    uint64_t euf_eq_assignments      = 0; // positive (equality) assignments
    uint64_t euf_diseq_assignments   = 0; // negative (disequality) assignments
    uint64_t euf_check_model_calls   = 0; // cb_check_found_model callbacks
    uint64_t euf_conflicts           = 0; // theory lemmas (conflict clauses) generated
    uint64_t euf_conflict_lits_total = 0; // total literals across all conflict clauses
    uint64_t euf_prop_candidates_considered = 0; // equality atoms inspected by propagation discovery

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
        row("preproc.finite_domain_amo", preproc_finite_domain_amo_clauses);
        out << "  -- euf theory --\n";
        row("euf.assignments",          euf_assignments);
        row("euf.eq_assignments",       euf_eq_assignments);
        row("euf.diseq_assignments",    euf_diseq_assignments);
        row("euf.check_model_calls",    euf_check_model_calls);
        row("euf.conflicts",            euf_conflicts);
        row("euf.conflict_lits_total",  euf_conflict_lits_total);
        row("euf.prop_candidates_considered", euf_prop_candidates_considered);
    }
};

} // namespace llm2smt
