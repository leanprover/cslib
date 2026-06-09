# Implementation Plan: Port Base MCS Completeness Properties

- **Task**: 34 - Port base MCS completeness properties
- **Status**: [NOT STARTED]
- **Effort**: 2 hours
- **Dependencies**: Tasks 6, 7 (completed -- DerivationTree, DeductionTheorem, MCSProperties)
- **Research Inputs**: specs/034_port_base_completeness_mcs_properties/reports/01_mcs-completeness-research.md
- **Artifacts**: plans/01_mcs-completeness-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: false

## Overview

Port 11 sorry-free MCS completeness theorems (~520 lines) from the BimodalLogic repository to a new file `Cslib/Logics/Bimodal/Metalogic/Completeness.lean`. The theorems fall into three groups: propositional MCS properties (disjunction and conjunction intro/elim/iff), modal properties (box_closure, box_box), and diamond-box duality (neg_box_implies_diamond_neg, diamond_neg_implies_neg_box, diamond_box_duality). All dependencies are already ported from tasks 6 and 7, making this a mechanical namespace-and-type-polymorphism translation.

### Research Integration

Key findings from the research report:
- All 11 theorems are sorry-free in the source and use a uniform MCS proof pattern
- Required imports: `Cslib.Logics.Bimodal.Metalogic.Core` (barrel) and `Cslib.Logics.Bimodal.Theorems.Perpetuity.Helpers` (double_negation, dni)
- Translation is mechanical: `Formula` becomes `Formula Atom` with `{Atom : Type*}`, namespaces shift from `Bimodal.Metalogic` to `Cslib.Logic.Bimodal.Metalogic`, import paths update to Cslib modules
- The `double_negation` and `dni` helpers from Perpetuity.Helpers use `noncomputable section`, which will be needed for the diamond-box duality proofs
- No blockers identified

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This plan advances Phase 4 (Bimodal porting), specifically task 8 (expanded) which covers `Bimodal/Metalogic/` completeness, decidability, separation, and conservative extension. The MCS completeness properties are foundational for the canonical model construction used in both dense and discrete completeness proofs.

## Goals & Non-Goals

**Goals**:
- Create `Cslib/Logics/Bimodal/Metalogic/Completeness.lean` with all 11 MCS completeness theorems
- All theorems sorry-free
- File compiles cleanly with `lake build Cslib.Logics.Bimodal.Metalogic.Completeness`
- Follow existing cslib copyright header and namespace conventions

**Non-Goals**:
- Porting saturation lemmas or CanonicalWorldState (not in scope for task 34)
- Adding the file to a barrel import (no Bimodal/Metalogic barrel exists yet)
- Modifying any existing files

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Notation scope issues with `⊢` | L | M | Use explicit `DerivationTree` terms or open scoped notation from ProofSystem.Derivation |
| `noncomputable` propagation from Helpers | L | L | Wrap diamond-box duality section in `noncomputable section` as done in MCSProperties.lean |
| `simp` lemma differences between source and target Lean versions | L | L | Check `simp` closures with `lean_goal`; adjust `simp only` sets if needed |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |

Phases within the same wave can execute in parallel.

### Phase 1: File Creation and Propositional MCS Properties [COMPLETED]

**Goal**: Create the target file with copyright header, imports, namespace setup, and port all 6 propositional MCS properties.

**Tasks**:
- [ ] Create `Cslib/Logics/Bimodal/Metalogic/Completeness.lean` with Apache 2.0 copyright header
- [ ] Add imports: `Cslib.Logics.Bimodal.Metalogic.Core`, `Cslib.Logics.Bimodal.Theorems.Perpetuity.Helpers`
- [ ] Add module docstring describing the file contents
- [ ] Set up namespace `Cslib.Logic.Bimodal.Metalogic` with `open Cslib.Logic.Bimodal` and `open Cslib.Logic`
- [ ] Add `variable {Atom : Type*}` and `attribute [local instance] Classical.propDecidable`
- [ ] Port `disjunction_intro` -- change `{S : Set Formula}` to `{S : Set (Formula Atom)}`, `{phi psi : Formula}` to `{phi psi : Formula Atom}`
- [ ] Port `disjunction_elim`
- [ ] Port `disjunction_iff`
- [ ] Port `conjunction_intro`
- [ ] Port `conjunction_elim`
- [ ] Port `conjunction_iff`
- [ ] Verify: `lake build Cslib.Logics.Bimodal.Metalogic.Completeness`

**Timing**: 1 hour

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/Completeness.lean` -- create new file (~300 lines)

**Verification**:
- File compiles with `lake build Cslib.Logics.Bimodal.Metalogic.Completeness`
- All 6 propositional theorems present and sorry-free

---

### Phase 2: Modal Properties and Diamond-Box Duality [COMPLETED]

**Goal**: Port the 2 modal properties and 3 diamond-box duality theorems, completing all 11 theorems.

**Tasks**:
- [ ] Port `box_closure` (Modal T property)
- [ ] Port `box_box` (Modal 4 property)
- [ ] Add `noncomputable section` for diamond-box duality proofs (needed for `double_negation` and `dni` from Helpers)
- [ ] Add `open Cslib.Logic.Bimodal.Theorems.Perpetuity (double_negation dni)` within the noncomputable section
- [ ] Port `neg_box_implies_diamond_neg` -- uses `double_negation`, `DerivationTree.necessitation`, `Axiom.modal_k_dist`
- [ ] Port `diamond_neg_implies_neg_box` -- uses `dni`, `DerivationTree.necessitation`, `Axiom.modal_k_dist`
- [ ] Port `diamond_box_duality` (iff wrapper)
- [ ] Close `noncomputable section` and namespace
- [ ] Verify: `lake build Cslib.Logics.Bimodal.Metalogic.Completeness`

**Timing**: 40 minutes

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/Completeness.lean` -- append ~200 lines

**Verification**:
- File compiles with `lake build Cslib.Logics.Bimodal.Metalogic.Completeness`
- All 11 theorems present and sorry-free

---

### Phase 3: Final Verification and Cleanup [NOT STARTED]

**Goal**: Verify the complete file compiles, check for sorry-free status, and confirm no regressions.

**Tasks**:
- [ ] Run `lake build Cslib.Logics.Bimodal.Metalogic.Completeness` for final verification
- [ ] Run `lean_verify` on key theorems (diamond_box_duality, conjunction_iff, disjunction_iff) to confirm no sorry/axiom usage
- [ ] Run `lake build` to verify no regressions in the full project
- [ ] Verify line count is reasonable (~460-520 lines)

**Timing**: 20 minutes

**Depends on**: 2

**Files to modify**:
- None (verification only)

**Verification**:
- `lake build` succeeds with no errors
- `lean_verify` confirms sorry-free status on key theorems
- All 11 theorems match the source signatures (with type polymorphism applied)

## Testing & Validation

- [ ] `lake build Cslib.Logics.Bimodal.Metalogic.Completeness` compiles without errors
- [ ] `lake build` (full project) succeeds with no regressions
- [ ] All 11 theorems are present: disjunction_intro, disjunction_elim, disjunction_iff, conjunction_intro, conjunction_elim, conjunction_iff, box_closure, box_box, neg_box_implies_diamond_neg, diamond_neg_implies_neg_box, diamond_box_duality
- [ ] No `sorry` in the file
- [ ] No vacuous definitions (`def X := True` etc.)
- [ ] Copyright header matches cslib convention

## Artifacts & Outputs

- `Cslib/Logics/Bimodal/Metalogic/Completeness.lean` -- new file (~460-520 lines)
- `specs/034_port_base_completeness_mcs_properties/plans/01_mcs-completeness-plan.md` -- this plan

## Rollback/Contingency

Since this creates a single new file with no modifications to existing files, rollback is straightforward: delete `Cslib/Logics/Bimodal/Metalogic/Completeness.lean`. No other files are affected.

## Porting Checklist

| # | Source Theorem | Target Signature | Group |
|---|---------------|-----------------|-------|
| 1 | `disjunction_intro` | `{S : Set (Formula Atom)} -> SetMaximalConsistent S -> (phi in S \/ psi in S) -> (phi.or psi) in S` | Propositional |
| 2 | `disjunction_elim` | `{S : Set (Formula Atom)} -> SetMaximalConsistent S -> (phi.or psi) in S -> phi in S \/ psi in S` | Propositional |
| 3 | `disjunction_iff` | `SetMaximalConsistent S -> ((phi.or psi) in S <-> (phi in S \/ psi in S))` | Propositional |
| 4 | `conjunction_intro` | `SetMaximalConsistent S -> phi in S -> psi in S -> (phi.and psi) in S` | Propositional |
| 5 | `conjunction_elim` | `SetMaximalConsistent S -> (phi.and psi) in S -> phi in S /\ psi in S` | Propositional |
| 6 | `conjunction_iff` | `SetMaximalConsistent S -> ((phi.and psi) in S <-> (phi in S /\ psi in S))` | Propositional |
| 7 | `box_closure` | `SetMaximalConsistent S -> Formula.box phi in S -> phi in S` | Modal |
| 8 | `box_box` | `SetMaximalConsistent S -> Formula.box phi in S -> (Formula.box phi).box in S` | Modal |
| 9 | `neg_box_implies_diamond_neg` | `SetMaximalConsistent S -> (Formula.box phi).neg in S -> phi.neg.diamond in S` | Diamond-Box |
| 10 | `diamond_neg_implies_neg_box` | `SetMaximalConsistent S -> phi.neg.diamond in S -> (Formula.box phi).neg in S` | Diamond-Box |
| 11 | `diamond_box_duality` | `SetMaximalConsistent S -> ((Formula.box phi).neg in S <-> phi.neg.diamond in S)` | Diamond-Box |

**Key translation rules**:
- `Formula` -> `Formula Atom`
- `Set Formula` -> `Set (Formula Atom)`
- `{Atom : Type*}` added as implicit variable
- `SetMaximalConsistent (fc := FrameClass.Base) S` stays as-is (already fc-parameterized in target)
- Namespace: `Bimodal.Metalogic` -> `Cslib.Logic.Bimodal.Metalogic`
- `double_negation` / `dni` accessed via `open Cslib.Logic.Bimodal.Theorems.Perpetuity`
