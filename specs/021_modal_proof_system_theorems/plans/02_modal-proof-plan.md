# Implementation Plan: Task #21

- **Task**: 21 - Port modal proof system and theorems
- **Status**: [NOT STARTED]
- **Effort**: 4 hours
- **Dependencies**: Task 16 (DecidableEq, completed), Task 20 (propositional theorems, completed)
- **Research Inputs**: specs/021_modal_proof_system_theorems/reports/02_modal-proof-research.md
- **Artifacts**: plans/02_modal-proof-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: true

## Overview

This plan ports modal-level derived theorems from BimodalLogic to cslib's generic typeclass framework. All theorems are stated generically over `[ModalHilbert S]` or `[ModalS5Hilbert S]` using `InferenceSystem.DerivableIn` -- no concrete `DerivationTree` inductive is needed. The work produces two new files (`Modal/Basic.lean` and `Modal/S5.lean`) under `Cslib/Foundations/Logic/Theorems/Modal/`, plus an aggregator update, totaling approximately 850-1,000 lines of new Lean code.

### Research Integration

The research report (02_modal-proof-research.md) established:
1. The generic typeclass approach is correct -- no concrete DerivationTree needed.
2. Axiom 5 (diamond-phi implies box-diamond-phi) must be derived from B + 4 as an early theorem in S5.lean.
3. `GeneralizedNecessitation` should be skipped (deferred to Task 7) since no S4/S5 theorem depends on it.
4. All "S4" theorems from BimodalLogic actually require S5 axioms (B or 5_collapse), so they belong in S5.lean under `[ModalS5Hilbert S]`.
5. Propositional foundation from Task 20 provides all required combinators: `imp_trans`, `b_combinator`, `theorem_flip`, `pairing`, `dni`, `double_negation`, `contrapose_imp`, `contraposition`, `classical_merge`, `iff_intro`, `demorgan_*`, `raa`, `efq_neg`, `rcp`, `lce_imp`, `rce_imp`.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This plan advances the following ROADMAP.md items:
- "Modal (Task 21): ~1,600 lines adding a standalone modal proof system with S4 and S5 theorem libraries and generalized necessitation"
- Import hierarchy: Foundations/Logic/Theorems -> Modal/Theorems (Task 21)

## Goals & Non-Goals

**Goals**:
- Create `Modal/Basic.lean` with K-level theorems (`box_mono`, `diamond_mono`, `box_contrapose`, `k_dist_diamond`, duality lemmas, `box_iff_intro`) generic over `[ModalHilbert S]`
- Create `Modal/S5.lean` with S5-level theorems (axiom 5 derivation, `t_box_to_diamond`, `diamond_4`, `box_conj_iff`, `diamond_disj_iff`, `s5_diamond_box`, S4-style nested modality theorems) generic over `[ModalS5Hilbert S]`
- Update `Theorems.lean` aggregator to import the new Modal module
- Ensure all theorems build cleanly with `lake build`

**Non-Goals**:
- Porting `GeneralizedNecessitation` (deferred to Task 7)
- Creating concrete `DerivationTree` inductive or `InferenceSystem` instances for tag types
- Porting temporal theorems (`future_mono`, `past_mono`, perpetuity principles)
- Adding `HasAxiom5` to `ModalS5Hilbert` (axiom 5 is derived from B + 4)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Axiom 5 derivation from B+4 may require non-obvious proof engineering | M | M | Research report provides step-by-step derivation; standard modal logic result |
| Verbose type signatures (no abbrev for diamond) reduce readability | L | H | Use local notation macros for neg/box/diamond at file top |
| Proof term complexity from nested `HasImp.imp`/`HasBot.bot` expansions | M | M | Follow exact BimodalLogic proof structure; lean on propositional combinators |
| Diamond encoding `HasImp.imp (HasBox.box (HasImp.imp phi HasBot.bot)) HasBot.bot` may cause unification issues | M | L | Test early with `box_mono` and `diamond_mono`; adjust if needed |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |

Phases within the same wave can execute in parallel.

### Phase 1: Modal/Basic.lean -- K-Level Theorems [COMPLETED]

**Goal**: Create `Cslib/Foundations/Logic/Theorems/Modal/Basic.lean` with all theorems generic over `[ModalHilbert S]` (K axiom + Necessitation only, no T/4/B).

**Tasks**:
- [ ] Create directory `Cslib/Foundations/Logic/Theorems/Modal/`
- [ ] Create `Basic.lean` with module header, imports (`ProofSystem`, `Combinators`, `Propositional.Core`, `Propositional.Connectives`), and namespace `Cslib.Logic.Theorems.Modal.Basic`
- [ ] Set up `variable` block: `{F : Type*} [HasBot F] [HasImp F] [HasBox F]`, `{S : Type*} [InferenceSystem S F]`, `[ModalHilbert S (F := F)]`
- [ ] Add `set_option linter.style.longLine false` and `noncomputable section`
- [ ] Implement `box_mono`: From `⊢ (phi -> psi)`, derive `⊢ (box phi -> box psi)` using `Necessitation.nec` + `HasAxiomK.K` + `ModusPonens.mp`
- [ ] Implement `diamond_mono`: From `⊢ (phi -> psi)`, derive `⊢ (diamond phi -> diamond psi)` using `contraposition` of `box_mono` applied to negated implication
- [ ] Implement `box_contrapose`: `⊢ box(phi -> psi) -> box(neg psi -> neg phi)` using `box_mono` + `b_combinator` + `theorem_flip`
- [ ] Implement `k_dist_diamond`: `⊢ box(phi -> psi) -> (diamond phi -> diamond psi)` using `box_contrapose` + `HasAxiomK.K` + `contrapose_imp`
- [ ] Implement `modal_duality_neg`: `⊢ diamond(neg phi) -> neg(box phi)` using `dni` + `box_mono` + `contraposition`
- [ ] Implement `modal_duality_neg_rev`: `⊢ neg(box phi) -> diamond(neg phi)` using `double_negation` + `box_mono` + `contraposition`
- [ ] Implement `box_iff_intro`: From `⊢ phi <-> psi`, derive `⊢ box phi <-> box psi` using `box_mono` + `lce_imp` + `rce_imp` + `iff_intro`
- [ ] Run `lake build Cslib.Foundations.Logic.Theorems.Modal.Basic` to verify

**Timing**: 1.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Foundations/Logic/Theorems/Modal/Basic.lean` - Create new file (~250 lines)

**Verification**:
- `lake build Cslib.Foundations.Logic.Theorems.Modal.Basic` succeeds with no errors or sorries
- All 7 theorems type-check

---

### Phase 2: Modal/S5.lean -- S5-Level Theorems [COMPLETED]

**Goal**: Create `Cslib/Foundations/Logic/Theorems/Modal/S5.lean` with all theorems generic over `[ModalS5Hilbert S]`, including the derived axiom 5, core S5 results, and the S4-level nested modality theorems (which require S5 axioms).

**Tasks**:
- [ ] Create `S5.lean` with module header, imports (`ProofSystem`, `Combinators`, `Propositional.Core`, `Propositional.Connectives`, `Modal.Basic`), and namespace `Cslib.Logic.Theorems.Modal.S5`
- [ ] Set up `variable` block: `{F : Type*} [HasBot F] [HasImp F] [HasBox F]`, `{S : Type*} [InferenceSystem S F]`, `[ModalS5Hilbert S (F := F)]`
- [ ] Add `set_option linter.style.longLine false` and `noncomputable section`
- [ ] **Axiom 5 Derivation Block** (critical foundation):
  - [ ] Implement `diamond_4`: `⊢ diamond(diamond phi) -> diamond phi` from T + 4 via duality (contrapose `HasAxiom4.four` applied to negated formula, then duality cleanup)
  - [ ] Implement `axiom5_derived`: `⊢ diamond phi -> box(diamond phi)` from B + diamond_4 + box_mono (apply B to diamond phi, use box_mono on diamond_4 to collapse)
  - [ ] Implement `axiom5_collapse_derived`: `⊢ diamond(box phi) -> box phi` from axiom5_derived + T + duality
- [ ] **Core S5 Theorems**:
  - [ ] Implement `t_box_to_diamond`: `⊢ box phi -> diamond phi` using T + `raa`
  - [ ] Implement `t_box_consistency`: `⊢ neg(box(phi and neg phi))` using T + contradiction
  - [ ] Implement `box_disj_intro`: `⊢ (box phi or box psi) -> box(phi or psi)` using `box_mono` + `classical_merge`
  - [ ] Implement `box_conj_iff`: `⊢ box(phi and psi) <-> (box phi and box psi)` using K + `box_mono` + `pairing`
  - [ ] Implement `diamond_disj_iff`: `⊢ diamond(phi or psi) <-> (diamond phi or diamond psi)` using `box_conj_iff` + `demorgan` + `contraposition`
- [ ] **S5 Collapse and Diamond-Box Theorems**:
  - [ ] Implement `s5_diamond_box`: `⊢ diamond(box phi) <-> box phi` using `axiom5_collapse_derived` + `t_box_to_diamond` + `iff_intro`
  - [ ] Implement `s5_diamond_box_to_truth`: `⊢ diamond(box phi) -> phi` using `axiom5_collapse_derived` + T
- [ ] **S4-Level Nested Modality Theorems** (all under `[ModalS5Hilbert S]`):
  - [ ] Implement `s4_diamond_box_conj`: `⊢ (diamond A and box B) -> diamond(A and box B)` using 4 + `k_dist_diamond` + `pairing` + `theorem_flip`
  - [ ] Implement `s4_box_diamond_box`: `⊢ box A -> box(diamond(box A))` using B + `box_mono`
  - [ ] Implement `s4_diamond_box_diamond`: `⊢ diamond(box(diamond A)) <-> diamond A` using `axiom5_collapse_derived` + `diamond_mono` + `iff_intro`
  - [ ] Implement `s5_diamond_conj_diamond`: `⊢ diamond(A and diamond B) <-> (diamond A and diamond B)` using `axiom5_derived` + `diamond_4` + distribution
- [ ] Run `lake build Cslib.Foundations.Logic.Theorems.Modal.S5` to verify

**Timing**: 2 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Foundations/Logic/Theorems/Modal/S5.lean` - Create new file (~600-750 lines)

**Verification**:
- `lake build Cslib.Foundations.Logic.Theorems.Modal.S5` succeeds with no errors or sorries
- All ~16 theorems type-check
- Axiom 5 derivation from B + 4 is correct (no `HasAxiom5` instance required)

---

### Phase 3: Aggregator Update and Final Build [NOT STARTED]

**Goal**: Update the `Theorems.lean` aggregator to import the new Modal module and verify the full project builds.

**Tasks**:
- [ ] Edit `Cslib/Foundations/Logic/Theorems.lean` to add imports for `Modal.Basic` and `Modal.S5`
- [ ] Update the module docstring to list the new Modal submodules
- [ ] Run `lake build` to verify full project builds
- [ ] Verify no import cycles or namespace conflicts

**Timing**: 0.5 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Foundations/Logic/Theorems.lean` - Add Modal imports (~10 lines changed)

**Verification**:
- `lake build` succeeds with no errors
- `import Cslib.Foundations.Logic.Theorems` transitively imports all Modal theorems

## Testing & Validation

- [ ] `lake build Cslib.Foundations.Logic.Theorems.Modal.Basic` -- Phase 1 builds
- [ ] `lake build Cslib.Foundations.Logic.Theorems.Modal.S5` -- Phase 2 builds
- [ ] `lake build` -- Full project builds with no regressions
- [ ] No `sorry` or vacuous definitions (`def X := True`) in any file
- [ ] All theorems use only `[ModalHilbert S]` or `[ModalS5Hilbert S]` constraints (no concrete types)
- [ ] `axiom5_derived` proves `⊢ diamond phi -> box(diamond phi)` without `HasAxiom5` instance

## Artifacts & Outputs

- `Cslib/Foundations/Logic/Theorems/Modal/Basic.lean` -- K-level modal theorems (~250 lines)
- `Cslib/Foundations/Logic/Theorems/Modal/S5.lean` -- S5-level modal theorems (~600-750 lines)
- `Cslib/Foundations/Logic/Theorems.lean` -- Updated aggregator
- `specs/021_modal_proof_system_theorems/plans/02_modal-proof-plan.md` -- This plan

## Rollback/Contingency

- If axiom 5 derivation from B+4 fails, consider adding `HasAxiom5` as an explicit typeclass field to `ModalS5Hilbert` (low risk -- standard modal logic result).
- If diamond encoding causes unification issues, try `unfold`/`simp only` tactics with `Axioms.AxiomB`, `Axioms.AxiomT`, etc. to normalize terms.
- All new files are additive (no existing files modified except the aggregator), so rollback is simply deleting the `Modal/` directory and reverting `Theorems.lean`.
