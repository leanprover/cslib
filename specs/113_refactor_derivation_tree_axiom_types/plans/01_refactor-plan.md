# Implementation Plan: Refactor Propositional DerivationTree to Axiom-Parameterized Form

- **Task**: 113 - Refactor propositional DerivationTree to be parameterized over an axiom predicate
- **Status**: [NOT STARTED]
- **Effort**: 5 hours
- **Dependencies**: None
- **Research Inputs**: specs/113_refactor_derivation_tree_axiom_types/reports/01_refactor-research.md
- **Artifacts**: plans/01_refactor-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: true

## Overview

Refactor the propositional `DerivationTree` from a hardcoded `PropositionalAxiom` type to a parameterized `(Axioms : PL.Proposition Atom -> Prop)` predicate, following the established modal pattern in `Cslib/Logics/Modal/Metalogic/DerivationTree.lean`. This makes the proof system generic over axiom sets, enabling reuse for intuitionistic (`IntPropAxiom`) and minimal (`MinPropAxiom`) logics. Downstream files (DeductionTheorem, MCS, Instances) are updated to propagate the axiom parameter, with backward-compatible aliases preserving existing API. A new `IntMinInstances.lean` registers `HilbertInt` and `HilbertMin` instances using the existing tag types.

### Research Integration

The research report identifies the modal DerivationTree as the exact pattern to follow: parameterize `DerivationTree` by `Axioms`, thread `h_implyK`/`h_implyS` through deduction theorem and MCS, and fix NaturalDeduction files at `PropositionalAxiom` using backward-compat aliases. Key risk areas identified: NaturalDeduction/FromHilbert.lean (many callsites using `impI` which wraps `deductionTheorem`), MCS EFQ/Peirce dependencies, and the `HasHilbertTree` instance. The research recommends approach (A) for NaturalDeduction: fix at `PropositionalAxiom` rather than full parameterization.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md consulted for this plan.

## Goals & Non-Goals

**Goals**:
- Parameterize `DerivationTree` by an axiom predicate, matching modal pattern exactly
- Add `IntPropAxiom` (implyK, implyS, efq) and `MinPropAxiom` (implyK, implyS) inductive types
- Add subsumption proofs: `MinPropAxiom -> IntPropAxiom -> PropositionalAxiom`
- Parameterize `Deriv`, `Derivable`, `propDerivationSystem`, deduction theorem, MCS
- Register `HilbertInt` (IntuitionisticHilbert) and `HilbertMin` (MinimalHilbert) instances
- Maintain full backward compatibility via aliases and fixed instantiations
- All downstream files (including NaturalDeduction) compile without changes to their external API

**Non-Goals**:
- Full parameterization of NaturalDeduction files (deferred; they use `PropositionalAxiom` constructors directly)
- Parameterizing `hilbertSubstitution` over arbitrary axiom preservation (can be done later)
- Changing the Modal/Temporal/Bimodal proof systems (they already follow this pattern)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| NaturalDeduction `impI`/`botE` breakage after `DerivationTree` parameterization | H | H | Fix NaturalDeduction files at `PropositionalAxiom` via backward-compat aliases; `impI` calls `deductionTheorem` which now needs the hardcoded axiom set |
| `HasHilbertTree` instance conflict between global and `letI` in deduction theorem | M | M | Follow modal pattern exactly: global instance at `PropositionalAxiom`, `letI` inside parameterized functions |
| MCS theorems requiring EFQ/Peirce beyond implyK/implyS | M | L | Add explicit `h_efq`/`h_peirce` parameters only where needed; most MCS theorems only need deduction theorem (implyK + implyS) |
| Universe polymorphism issues from `Axioms` parameter | L | L | `Axioms : PL.Proposition Atom -> Prop` is in `Prop`, no universe impact expected |
| Backward-compat `abbrev` causing definitional unfolding issues | L | L | Use `abbrev` first, fall back to `@[reducible] def` if issues arise |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4, 5 | 3 |
| 5 | 6 | 4, 5 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Axiom Types and Core Parameterization [COMPLETED]

**Goal**: Add new axiom inductive types and parameterize `DerivationTree` with backward-compat aliases.

**Tasks**:
- [ ] Add `IntPropAxiom` inductive to `Axioms.lean` with constructors: `implyK`, `implyS`, `efq`
- [ ] Add `MinPropAxiom` inductive to `Axioms.lean` with constructors: `implyK`, `implyS`
- [ ] Add subsumption proofs: `MinPropAxiom.toIntProp` and `IntPropAxiom.toProp` (simple case analysis)
- [ ] Parameterize `DerivationTree` in `Derivation.lean`: add `(Axioms : PL.Proposition Atom -> Prop)` parameter, change `.ax` constructor from `(h : PropositionalAxiom phi)` to `(h : Axioms phi)`
- [ ] Parameterize `height` and all height theorems to carry implicit `{Axioms}`
- [ ] Parameterize `Deriv`, `Derivable`, `mp_deriv`, `weakening_deriv`, `assumption_deriv`
- [ ] Parameterize `propDerivationSystem` to take explicit `(Axioms : PL.Proposition Atom -> Prop)`
- [ ] Add backward-compat aliases: `ClDerivationTree`, `ClDeriv`, `ClDerivable`, `clPropDerivationSystem`

**Timing**: 1.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/ProofSystem/Axioms.lean` - Add IntPropAxiom, MinPropAxiom, subsumption proofs
- `Cslib/Logics/Propositional/ProofSystem/Derivation.lean` - Parameterize DerivationTree and all dependents

**Verification**:
- `lake build Cslib.Logics.Propositional.ProofSystem.Derivation` compiles

---

### Phase 2: Deduction Theorem Parameterization [NOT STARTED]

**Goal**: Parameterize the deduction theorem with explicit `h_implyK`/`h_implyS` proofs, following the modal pattern exactly.

**Tasks**:
- [ ] Update `HasHilbertTree` global instance to use `DerivationTree PropositionalAxiom` (not bare `DerivationTree`)
- [ ] Parameterize `deductionWithMem` with `{Axioms}`, `h_implyK`, `h_implyS` parameters; add `letI : HasHilbertTree` inside body (modal pattern)
- [ ] Parameterize `deductionTheorem` with `{Axioms}`, `h_implyK`, `h_implyS` parameters; add `letI : HasHilbertTree` inside body
- [ ] Parameterize `prop_has_deduction_theorem` to take `{Axioms}`, `h_implyK`, `h_implyS`
- [ ] Add backward-compat wrapper: `cl_prop_has_deduction_theorem` instantiating at `PropositionalAxiom` with `(.implyK _ _)` and `(.implyS _ _ _)`

**Timing**: 1.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/Metalogic/DeductionTheorem.lean` - Full parameterization following modal pattern

**Verification**:
- `lake build Cslib.Logics.Propositional.Metalogic.DeductionTheorem` compiles

---

### Phase 3: MCS Parameterization [NOT STARTED]

**Goal**: Parameterize MCS definitions and theorems by axiom predicate, following the modal MCS pattern.

**Tasks**:
- [ ] Parameterize `PropSetConsistent` and `PropSetMaximalConsistent` abbrevs to take `(Axioms : PL.Proposition Atom -> Prop)`
- [ ] Parameterize `prop_lindenbaum` with `{Axioms}`
- [ ] Parameterize `prop_closed_under_derivation` with `{Axioms}`, `h_implyK`, `h_implyS` (uses deduction theorem)
- [ ] Parameterize `prop_implication_property` with `{Axioms}`, `h_implyK`, `h_implyS`
- [ ] Parameterize `prop_negation_complete` with `{Axioms}`, `h_implyK`, `h_implyS`
- [ ] Parameterize `prop_mcs_bot_not_mem` with `{Axioms}` (only needs `propDerivationSystem Axioms`, no implyK/S)
- [ ] Parameterize `prop_mcs_neg_of_not_mem` with `{Axioms}`, `h_implyK`, `h_implyS` (calls `prop_negation_complete`)
- [ ] Parameterize `prop_mcs_not_mem_of_neg` with `{Axioms}`, `h_implyK`, `h_implyS`
- [ ] Parameterize `prop_mcs_mem_iff_neg_not_mem` with `{Axioms}`, `h_implyK`, `h_implyS`

**Timing**: 1 hour

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Propositional/Metalogic/MCS.lean` - Full parameterization following modal MCS pattern

**Verification**:
- `lake build Cslib.Logics.Propositional.Metalogic.MCS` compiles

---

### Phase 4: Instance Updates and IntMinInstances [NOT STARTED]

**Goal**: Update `HilbertCl` instances and create new `HilbertInt`/`HilbertMin` instances.

**Tasks**:
- [ ] Update `Instances.lean`: change `DerivationTree [] phi` to `DerivationTree PropositionalAxiom [] phi` in `InferenceSystem` instance
- [ ] Update `ModusPonens`, `HasAxiomImplyK`, `HasAxiomImplyS`, `HasAxiomEFQ`, `HasAxiomPeirce` instances to use `DerivationTree PropositionalAxiom`
- [ ] Create `IntMinInstances.lean` with `HilbertInt` instances:
  - `InferenceSystem` mapping `derivation` to `DerivationTree IntPropAxiom [] phi`
  - `ModusPonens` using `DerivationTree.modus_ponens`
  - `HasAxiomImplyK` using `.implyK`
  - `HasAxiomImplyS` using `.implyS`
  - `HasAxiomEFQ` using `.efq`
  - `IntuitionisticHilbert` (empty body, inherits from above)
- [ ] Add `HilbertMin` instances in `IntMinInstances.lean`:
  - `InferenceSystem` mapping `derivation` to `DerivationTree MinPropAxiom [] phi`
  - `ModusPonens` using `DerivationTree.modus_ponens`
  - `HasAxiomImplyK` using `.implyK`
  - `HasAxiomImplyS` using `.implyS`
  - `MinimalHilbert` (empty body, inherits from above)
- [ ] Register `IntMinInstances.lean` in `Cslib.lean` root import file

**Timing**: 0.5 hours

**Depends on**: 3

**Files to modify**:
- `Cslib/Logics/Propositional/ProofSystem/Instances.lean` - Update HilbertCl instances

**Files to create**:
- `Cslib/Logics/Propositional/ProofSystem/IntMinInstances.lean` - HilbertInt, HilbertMin instances

**Verification**:
- `lake build Cslib.Logics.Propositional.ProofSystem.IntMinInstances` compiles
- `lake build Cslib.Logics.Propositional.ProofSystem.Instances` compiles

---

### Phase 5: NaturalDeduction Backward Compatibility [NOT STARTED]

**Goal**: Update NaturalDeduction files to compile with the parameterized `DerivationTree`, fixing all uses at `PropositionalAxiom`.

**Tasks**:
- [ ] Update `FromHilbert.lean`:
  - `impI`: change `DerivationTree (A :: Gamma) B` to `DerivationTree PropositionalAxiom (A :: Gamma) B` (or rely on backward-compat alias); `deductionTheorem` call needs `h_implyK`/`h_implyS` -- provide via `(.implyK _ _)` and `(.implyS _ _ _)`
  - `impE`: update type signatures with `PropositionalAxiom`
  - `botE`: update type signatures with `PropositionalAxiom`, uses `.efq` directly
  - `assume`, `axiomRule`: update type signatures
  - `hilbertCut`, `hilbertWeakening`: update type signatures
  - All `Deriv`-level wrappers: update `Deriv` -> `Deriv PropositionalAxiom` (or use `ClDeriv` alias)
  - `subst_preserves_axiom`: no change needed (already specific to `PropositionalAxiom`)
  - `hilbertSubstitution`: update `DerivationTree` -> `DerivationTree PropositionalAxiom`
- [ ] Update `HilbertDerivedRules.lean`: all `DerivationTree` references become `DerivationTree PropositionalAxiom` (or use `ClDerivationTree` alias); all `PropositionalAxiom` constructor uses remain unchanged
- [ ] Update `Equivalence.lean`: 
  - `hilbertToND`: `DerivationTree` -> `DerivationTree PropositionalAxiom`
  - `ndToHilbert`: same, plus `deductionTheorem` call needs `h_implyK`/`h_implyS`
  - `hilbert_iff_nd`: `Derivable` -> `Derivable PropositionalAxiom` (or `ClDerivable`)
  - `Deriv` -> `Deriv PropositionalAxiom` (or `ClDeriv`)

**Timing**: 1 hour

**Depends on**: 3

**Files to modify**:
- `Cslib/Logics/Propositional/NaturalDeduction/FromHilbert.lean` - Fix at PropositionalAxiom
- `Cslib/Logics/Propositional/NaturalDeduction/HilbertDerivedRules.lean` - Fix at PropositionalAxiom
- `Cslib/Logics/Propositional/NaturalDeduction/Equivalence.lean` - Fix at PropositionalAxiom

**Verification**:
- `lake build Cslib.Logics.Propositional.NaturalDeduction.Equivalence` compiles (this transitively verifies FromHilbert and HilbertDerivedRules)

---

### Phase 6: Full Build and Verification [NOT STARTED]

**Goal**: Verify the entire project builds cleanly with no regressions.

**Tasks**:
- [ ] Run `lake build` for full project build
- [ ] Verify no `sorry` in any modified file via `lean_verify` on key definitions
- [ ] Verify no regressions in downstream modules (Modal, Temporal, Bimodal) -- these should be unaffected since they have their own DerivationTree

**Timing**: 0.5 hours

**Depends on**: 4, 5

**Files to modify**: none (verification only)

**Verification**:
- `lake build` succeeds with no errors
- No `sorry` in modified files

## Testing & Validation

- [ ] `lake build Cslib.Logics.Propositional.ProofSystem.Derivation` passes (Phase 1)
- [ ] `lake build Cslib.Logics.Propositional.Metalogic.DeductionTheorem` passes (Phase 2)
- [ ] `lake build Cslib.Logics.Propositional.Metalogic.MCS` passes (Phase 3)
- [ ] `lake build Cslib.Logics.Propositional.ProofSystem.Instances` passes (Phase 4)
- [ ] `lake build Cslib.Logics.Propositional.ProofSystem.IntMinInstances` passes (Phase 4)
- [ ] `lake build Cslib.Logics.Propositional.NaturalDeduction.Equivalence` passes (Phase 5)
- [ ] `lake build` full project passes (Phase 6)
- [ ] `lean_verify` confirms no sorry in key definitions

## Artifacts & Outputs

- `specs/113_refactor_derivation_tree_axiom_types/plans/01_refactor-plan.md` (this file)
- Modified: `Axioms.lean`, `Derivation.lean`, `DeductionTheorem.lean`, `MCS.lean`, `Instances.lean`
- Modified: `FromHilbert.lean`, `HilbertDerivedRules.lean`, `Equivalence.lean`
- Created: `IntMinInstances.lean`
- Modified: `Cslib.lean` (root import)

## Rollback/Contingency

All changes are in the propositional proof system subtree. If the refactor fails:
1. `git stash` or `git checkout` the affected files to revert to pre-refactor state
2. The modal/temporal/bimodal systems are unaffected (they already use the parameterized pattern)
3. If NaturalDeduction files prove intractable, they can be temporarily commented out and addressed in a follow-up task -- the core parameterization (Phases 1-4) can land independently
