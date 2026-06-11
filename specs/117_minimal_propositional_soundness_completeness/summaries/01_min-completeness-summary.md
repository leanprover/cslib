# Implementation Summary: Task #117

- **Task**: 117 - Minimal propositional soundness and completeness
- **Status**: Implemented
- **Session**: sess_1781190779_1bb1b5
- **Date**: 2026-06-11

## Overview

Proved soundness and completeness of MinPropAxiom (implyK + implyS only, no EFQ) with respect to minimal Kripke semantics (MValid). Three new files were created following the architecture of the intuitionistic counterparts but with structurally simpler proofs throughout.

## Files Created

1. **`Cslib/Logics/Propositional/Metalogic/MinSoundness.lean`** (~90 lines)
   - `min_axiom_sound`: 2 axiom cases (implyK, implyS) are MValid
   - `min_soundness`: 4-case match on DerivationTree with arbitrary `bot_forces`
   - `min_soundness_derivable`: Wrapper from Derivable to MValid

2. **`Cslib/Logics/Propositional/Metalogic/MinLindenbaum.lean`** (~260 lines)
   - `MinTheory`: Deductively closed sets without consistency requirement
   - `min_theory_imp_property`: MP closure for MinTheory
   - `min_deriv_from_closure_to_S`: Compilation lemma
   - `min_deriv_imp_of_union`: Cut lemma for union contexts
   - `min_deductive_closure`: Deductive closure definition
   - `min_imp_witness`: Implication witness lemma (no EFQ needed)
   - `lift_min_to_cl`: Lift MinPropAxiom derivations to classical
   - `min_consistent`: MinPropAxiom consistency via classical soundness
   - `min_theorems_theory`: Set of theorems is a MinTheory

3. **`Cslib/Logics/Propositional/Metalogic/MinCompleteness.lean`** (~130 lines)
   - `MinCanonicalWorld`: Subtype of MinTheory with Preorder instance
   - `min_canonical_val`, `min_bot_forces`: Canonical model definitions
   - Upward closure proofs for both
   - `min_truth_lemma`: 3 cases (atom: Iff.rfl, bot: Iff.rfl, imp: witness/closure)
   - `min_completeness`: Canonical model completeness via by_contra
   - `min_soundness_completeness`: Biconditional MValid <-> Derivable MinPropAxiom

## Key Structural Differences from Intuitionistic

| Aspect | Intuitionistic | Minimal |
|--------|---------------|---------|
| Axioms | 3 (implyK, implyS, efq) | 2 (implyK, implyS) |
| World definition | IntDCCS (consistent + closed) | MinTheory (closed only) |
| bot_forces | fun _ => False | bot in w.val |
| Truth lemma bot | False <-> bot not in S (multi-step) | Iff.rfl (trivial) |
| Imp witness | Needs EFQ for consistency sub-proof | No EFQ needed |
| Consistency proof | Lift to classical via toProp | Same approach |

## Plan Deviations

- **Task 2.9**: `lift_min_to_int` was altered to `lift_min_to_cl` -- lifted directly to PropositionalAxiom (classical) instead of IntPropAxiom, avoiding an IntLindenbaum import dependency.
- **Task 2.10**: `min_consistent` was altered to use `prop_soundness` (classical soundness) directly instead of `int_consistent`, consistent with the direct-to-classical lifting approach.

## Verification

- Zero sorries in all three files
- Zero vacuous definitions
- Zero new axioms (only standard Lean axioms: propext, Classical.choice, Quot.sound)
- Full `lake build` passes (2957 jobs)
- `lean_verify` confirms axiom safety on `min_soundness_completeness`
- Plan compliance check: all 6 goals found
