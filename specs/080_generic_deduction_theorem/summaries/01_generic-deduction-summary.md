# Implementation Summary: Task #80 -- Generic DeductionTheorem Interface

## Overview

Created a `HasHilbertTree` typeclass in `Cslib/Foundations/Logic/Metalogic/DeductionHelpers.lean` with 6 fields and 4 generic helper lemmas, then refactored all 4 logic domains (PL, Modal, Temporal, Bimodal) to use the shared helpers. Each logic now instantiates `HasHilbertTree` and calls the generic `deduction_axiom`, `deduction_imp_self`, `deduction_assumption_other`, and `deduction_mp_under_imp` instead of defining its own copies.

## Changes

### New File
- `Cslib/Foundations/Logic/Metalogic/DeductionHelpers.lean` (119 lines)
  - `HasHilbertTree` typeclass: 6 fields (Tree, implyK, implyS, assumption, mp, weakening)
  - 4 generic helper lemmas proven once

### Modified Files
- `Cslib/Logics/Propositional/Metalogic/DeductionTheorem.lean`: Added `HasHilbertTree (PL.Proposition Atom)` instance, removed 4 per-logic helpers (-31 lines)
- `Cslib/Logics/Modal/Metalogic/DeductionTheorem.lean`: Added `HasHilbertTree (Proposition Atom)` instance, removed 4 per-logic helpers (-39 lines)
- `Cslib/Logics/Temporal/Metalogic/DeductionTheorem.lean`: Added `HasHilbertTree (Formula Atom)` instance with swapped axiom mapping (`.imp_s` -> `implyK`, `.imp_k` -> `implyS`), removed 4 per-logic helpers (-38 lines)
- `Cslib/Logics/Bimodal/Metalogic/Core/DeductionTheorem.lean`: Added `@[reducible] def bimodalHilbertTree` (fc-parameterized, uses `letI` in proofs), removed 6 per-logic helpers including `weaken_under_imp`/`weaken_under_imp_ctx` (-72 lines)

## Key Design Decisions

1. **`deduction_axiom` takes `d_empty : Tree [] phi`** rather than axiom-specific parameters. Each logic builds the empty-context derivation inline at call sites.
2. **Bimodal uses `def` not `instance`** because its deduction theorem is polymorphic in `{fc : FrameClass}`. The `bimodalHilbertTree` function returns a `HasHilbertTree` for any `fc`, introduced via `letI` in proofs.
3. **Swapped axiom names preserved**: The typeclass fields use semantic names (`implyK` = weakening axiom, `implyS` = distribution axiom). PL/Modal map `.implyK`/`.implyS` directly; Temporal/Bimodal map `.imp_s` -> `implyK` and `.imp_k` -> `implyS`.
4. **Per-logic `deduction_with_mem`/`deduction_theorem` remain concrete**: These use native `match` on DerivationTree constructors and `termination_by` on concrete height functions, which cannot work through typeclass abstraction.

## Plan Deviations

- **Phase 1**: `deduction_axiom` signature altered to take `d_empty` parameter instead of `h_ax` (simplifies generic interface)
- **Phase 3**: No separate bridge function for Temporal axiom case; inline construction `.axiom [] psi h_ax h_fc` suffices
- **Phase 4**: Bimodal `deduction_assumption_same` replaced with generic `deduction_imp_self` (no longer uses `identity` from Perpetuity/Helpers); `bimodalHilbertTree` defined as `@[reducible] def` with `letI` pattern rather than global instance

## Metrics

- **Lines removed from 4 existing files**: 171
- **Lines added (new shared file)**: 119
- **Net line reduction**: 52
- **Duplicated helper definitions eliminated**: 4 per file x 4 files = 16 definitions -> 4 generic definitions
- **Build passes**: Full `lake build` (2915 jobs)
- **No sorry introduced**: 0 in modified files
- **No new axioms**: Only standard Lean axioms (propext, Classical.choice, Quot.sound)
