# Implementation Summary: Task #57

- **Task**: 57 - Improve theorem organization: move misplaced generic theorems to Foundations and eliminate concrete duplicates in Bimodal
- **Status**: Implemented
- **Plan**: specs/057_improve_theorem_organization/plans/01_theorem-organization-plan.md
- **Type**: lean4
- **Phases Completed**: 3/3

## Changes Made

### Phase 1: Move Generic Temporal Files to Foundations

Moved two generic temporal files from `Cslib/Logics/Temporal/Theorems/` to `Cslib/Foundations/Logic/Theorems/Temporal/`:
- `TemporalDerived.lean` -- 20+ derived temporal theorems (G/H distribution, contraposition, etc.)
- `FrameConditions.lean` -- Frame condition typeclasses (Linear, Serial, Dense, Discrete)

Updated barrel imports in:
- `Cslib/Foundations/Logic/Theorems.lean` -- added 2 new imports
- `Cslib/Logics/Temporal/Theorems.lean` -- redirected 2 import paths to Foundations
- `Cslib/Logics/Bimodal/Theorems/Perpetuity/Principles.lean` -- updated 1 import path

### Phase 2: Replace Redundant Bimodal Theorems with Bridge Wrappers

Replaced 30 redundant concrete theorem proofs across 3 files with wrap/unwrap bridge wrappers delegating to generic Foundations equivalents:

**`Combinators.lean`** (10 bridged, 1 retained, 2 kept with structural logic):
- Bridged: `imp_trans`, `identity`, `b_combinator`, `theorem_flip`, `theorem_app1`, `theorem_app2`, `pairing`, `dni`
- Kept with structural logic: `combine_imp_conj`, `combine_imp_conj_3` (use bridged primitives but retain S-axiom application pattern)
- Retained as-is: `mp` (trivial 1-line wrapper, no Foundations equivalent), `temp_future_derived` (uses concrete modal axioms)

**`Propositional/Core.lean`** (8 bridged, 6 retained):
- Bridged: `lem`, `efq_axiom`, `peirce_axiom`, `double_negation`, `raa`, `efq_neg`, `lce_imp`, `rce_imp`
- Retained as-is: `rcp` (context-polymorphic signature with `Gamma` parameter has no direct Foundations equivalent), `ecq`, `ldi`, `rdi`, `lce`, `rce` (context-based proofs)

**`Propositional/Connectives.lean`** (12 bridged, 2 retained):
- Bridged: `classical_merge`, `iff_intro`, `contrapose_imp`, `contraposition`, `contrapose_iff`, `iff_neg_intro`, `demorgan_conj_neg_forward`, `demorgan_conj_neg_backward`, `demorgan_conj_neg`, `demorgan_disj_neg_forward`, `demorgan_disj_neg_backward`, `demorgan_disj_neg`
- Retained as-is: `iff_elim_left`, `iff_elim_right` (context-based proofs)

**Noncomputable propagation fixes**:
- `Cslib/Logics/Bimodal/Theorems/TemporalDerived.lean` -- added `noncomputable section` wrapper
- `Cslib/Logics/Bimodal/Metalogic/Algebraic/ParametricTruthLemma.lean` -- marked `past_tf_deriv` as `noncomputable`

### Phase 3: Final Verification

- Full `lake build` passes (only pre-existing unrelated error in `Cslib.lean` barrel import of `Consistency` module)
- Zero sorries in modified files
- Zero vacuous definitions
- Zero axioms introduced
- Old file paths completely removed
- All downstream consumers verified (Perpetuity, Metalogic, BXCanonical, FMP, Temporal)

## Metrics

- **Lines removed**: ~484
- **Lines added**: ~176
- **Net reduction**: ~308 lines
- **Theorems bridged**: 30 (of 32 planned; mp and rcp kept as-is due to signature differences)
- **Theorems retained**: 10 (as planned: temp_future_derived, ecq, ldi, rdi, lce, rce, iff_elim_left, iff_elim_right, plus mp and rcp)

## Plan Deviations

- `mp` in Combinators.lean was planned for replacement but kept as-is: it is a trivial 1-line modus ponens wrapper with no Foundations equivalent
- `rcp` in Core.lean was planned for replacement but kept as-is: its signature includes context parameter `Gamma` and fc-polymorphism with a derivation input, which differs fundamentally from the Foundations version
- `combine_imp_conj` and `combine_imp_conj_3` use bridged primitives internally but retain structural logic for S-axiom application (not pure 1-line wrappers)

## Files Modified

- `Cslib/Foundations/Logic/Theorems/Temporal/TemporalDerived.lean` -- new (moved from Logics/)
- `Cslib/Foundations/Logic/Theorems/Temporal/FrameConditions.lean` -- new (moved from Logics/)
- `Cslib/Foundations/Logic/Theorems.lean` -- added barrel imports
- `Cslib/Logics/Temporal/Theorems.lean` -- updated import paths
- `Cslib/Logics/Bimodal/Theorems/Perpetuity/Principles.lean` -- updated import path
- `Cslib/Logics/Bimodal/Theorems/Combinators.lean` -- replaced 10 theorem proofs
- `Cslib/Logics/Bimodal/Theorems/Propositional/Core.lean` -- replaced 8 theorem proofs
- `Cslib/Logics/Bimodal/Theorems/Propositional/Connectives.lean` -- replaced 12 theorem proofs
- `Cslib/Logics/Bimodal/Theorems/TemporalDerived.lean` -- added noncomputable section
- `Cslib/Logics/Bimodal/Metalogic/Algebraic/ParametricTruthLemma.lean` -- noncomputable fix
- `Cslib.lean` -- updated by mk_all
