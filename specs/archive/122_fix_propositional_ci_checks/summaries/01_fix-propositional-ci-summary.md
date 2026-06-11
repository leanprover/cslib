# Implementation Summary: Fix Propositional CI Check Failures

- **Task**: 122 - Fix all CONTRIBUTING.md CI check failures in propositional metalogic files
- **Session**: sess_1781194255_b2a0c0
- **Date**: 2026-06-11
- **Status**: Implemented

## Changes Made

### Phase 1: Rename snake_case definitions to lowerCamelCase (8 defs)

Renamed 8 `def` declarations and structure fields flagged by `defsWithUnderscore` linter:

| Old Name | New Name | File |
|----------|----------|------|
| `bot_forces` | `botForces` | Kripke.lean (structure field) |
| `int_canonical_val` | `intCanonicalVal` | IntCompleteness.lean |
| `int_neg_phi_imp_psi` | `intNegPhiImpPsi` | IntLindenbaum.lean |
| `int_deductive_closure` | `intDeductiveClosure` | IntLindenbaum.lean |
| `min_canonical_val` | `minCanonicalVal` | MinCompleteness.lean |
| `min_bot_forces` | `minBotForces` | MinCompleteness.lean |
| `min_deductive_closure` | `minDeductiveClosure` | MinLindenbaum.lean |
| `lift_min_to_cl` | `liftMinToCl` | MinLindenbaum.lean |

Used `replace_all` to rename each identifier and all its call sites within each file. Dependent theorem names (e.g., `int_canonical_val_upward_closed` -> `intCanonicalVal_upward_closed`) were also renamed for consistency, though the linter does not flag theorems.

Local parameter names (e.g., `bot_forces` in `IForces`, `iforces_persistence`, `MValid`) were NOT renamed since the linter only checks `.isDefinition` declarations.

### Phase 2: Fix simpNF violation

Removed `@[simp]` annotation from `mem_hilbertAxiomTheory` in Equivalence.lean (line 74). The lemma was redundant because `mem_axiomTheory` already applies to `HilbertAxiomTheory` (an `abbrev` transparent to `simp`).

### Phase 3: Fix imports (9 files)

| File | Change |
|------|--------|
| Derivation.lean | Replaced `Axioms` import with `Defs` |
| DeductionTheorem.lean | Added `Axioms` import |
| Soundness.lean | Added `Axioms` import |
| IntSoundness.lean | Added `Axioms` import |
| MinSoundness.lean | Added `Axioms` import |
| Instances.lean | Added `Axioms` import |
| IntMinInstances.lean | Added `Axioms` import |
| MinLindenbaum.lean | Removed `MCS` import |
| DerivedRules.lean | Added `Std.Tactic.BVDecide.Normalize` import |

### Phase 4: Remove unused DecidableEq

Removed `[DecidableEq Atom']` from both `hilbertSubstitution` and `hilbertSubstitutionDeriv` in FromHilbert.lean. Neither function body uses `DecidableEq`.

### Phase 5: CI Verification on main

All CI checks pass on `main`:
- `lake build` -- zero errors (2957 jobs)
- `lake lint` -- zero propositional violations
- `lake shake --add-public --keep-implied --keep-prefix` -- zero propositional issues
- `lake exe lint-style` -- pass
- `lake exe checkInitImports` -- pass
- `lake exe mk_all --module` -- updated Cslib.lean with new modal modules (pre-existing gap)

Note: `lake test` has a pre-existing failure in `CslibTests.GrindLint` (modal logic, unrelated to propositional files).

### Phase 6: Propagate to pr1/foundations-logic

Cherry-picked commit `55e3099a` to `pr1/foundations-logic`. Cslib.lean had a merge conflict (resolved by taking main's version and running `mk_all --module`). All CI checks pass on pr1.

## Files Modified (16 total)

All under `Cslib/Logics/Propositional/`:
- `Semantics/Kripke.lean` -- botForces structure field rename
- `Metalogic/IntCompleteness.lean` -- intCanonicalVal rename
- `Metalogic/IntLindenbaum.lean` -- intNegPhiImpPsi, intDeductiveClosure renames
- `Metalogic/MinCompleteness.lean` -- minCanonicalVal, minBotForces renames
- `Metalogic/MinLindenbaum.lean` -- minDeductiveClosure, liftMinToCl renames, MCS import removal
- `NaturalDeduction/Equivalence.lean` -- @[simp] removal
- `NaturalDeduction/FromHilbert.lean` -- DecidableEq removal
- `NaturalDeduction/DerivedRules.lean` -- BVDecide.Normalize import
- `ProofSystem/Derivation.lean` -- Axioms -> Defs import
- `ProofSystem/Instances.lean` -- Axioms import added
- `ProofSystem/IntMinInstances.lean` -- Axioms import added
- `Metalogic/DeductionTheorem.lean` -- Axioms import added
- `Metalogic/Soundness.lean` -- Axioms import added
- `Metalogic/IntSoundness.lean` -- Axioms import added
- `Metalogic/MinSoundness.lean` -- Axioms import added

Plus `Cslib.lean` (module list update from `mk_all --module`).

## Plan Deviations

- None (implementation followed plan)

## Verification Results

- sorry_count: 0
- vacuous_count: 0
- axiom_count: 0
- build_passed: true (both branches)
- lint_passed: true (zero propositional violations on both branches)
- shake_passed: true (zero propositional issues on both branches)
