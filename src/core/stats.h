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

    // ── EUF theory ─────────────────────────────────────────────────────────
    uint64_t euf_assignments         = 0; // notify_assignment callbacks
    uint64_t euf_eq_assignments      = 0; // positive (equality) assignments
    uint64_t euf_diseq_assignments   = 0; // negative (disequality) assignments
    uint64_t euf_check_model_calls   = 0; // cb_check_found_model callbacks
    uint64_t euf_conflicts           = 0; // theory lemmas (conflict clauses) generated
    uint64_t euf_conflict_lits_total = 0; // total literals across all conflict clauses

    void print(std::ostream& out) const {
        auto row = [&](const std::string& name, uint64_t val) {
            out << "  " << std::left << std::setw(30) << name << val << "\n";
        };
        out << "[stats]\n";
        out << "  -- preprocessor --\n";
        row("preproc.fmls_in",          preproc_fmls_in);
        row("preproc.fmls_true_out",    preproc_fmls_true_out);
        row("preproc.fmls_false_out",   preproc_fmls_false_out);
        row("preproc.forced_atoms",     preproc_forced_atoms);
        row("preproc.passes_run",       preproc_passes_run);
        out << "  -- euf theory --\n";
        row("euf.assignments",          euf_assignments);
        row("euf.eq_assignments",       euf_eq_assignments);
        row("euf.diseq_assignments",    euf_diseq_assignments);
        row("euf.check_model_calls",    euf_check_model_calls);
        row("euf.conflicts",            euf_conflicts);
        row("euf.conflict_lits_total",  euf_conflict_lits_total);
    }
};

} // namespace llm2smt
