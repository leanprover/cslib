# Implementation Plan: Task #90

- **Task**: 90 - Expand Modal Cube Proof Systems and Metalogic
- **Status**: [NOT STARTED]
- **Effort**: 22 hours
- **Dependencies**: None
- **Research Inputs**: specs/090_expand_modal_cube_proof_systems_metalogic/reports/01_modal-cube-expansion.md
- **Artifacts**: plans/01_modal-cube-expansion.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: true

## Overview

This plan decomposes the work needed to bring the modal logic metalogic infrastructure to parity with the Temporal/ module into a set of well-ordered implementation sub-tasks. The current codebase has a complete soundness/completeness pipeline for S5 only (5 files, ~1100 lines in Metalogic/). The goal is to: (1) parameterize DerivationTree over an axiom predicate so it works for any normal modal logic, (2) add intermediate typeclass bundles (ModalTHilbert, ModalDHilbert, ModalS4Hilbert) and tag types to ProofSystem.lean, (3) create Instances.lean bridging concrete derivation trees to the abstract typeclass hierarchy, (4) establish soundness and completeness for K, T, D, and S4 individually, and (5) integrate the untracked HilbertDerivedRules.lean. The output is a set of 7 implementation tasks with clear dependencies, each independently implementable and testable.

### Research Integration

The research report (01_modal-cube-expansion.md) provides:
- Architecture recommendation: typeclass-based hierarchy (Option A) with per-system axiom predicates and a shared parameterized DerivationTree
- Per-system analysis of soundness/completeness proof strategies for K, T, D, S4
- Critical insight that DeductionTheorem and MCS generalize mechanically since they never inspect the axiom payload
- Risk assessment: DerivationTree parameterization is highest-risk; K completeness box witness needs a different argument than S5 since axiom T is unavailable
- Line estimates: ~2,200 new lines total across all systems
- Dependency DAG: Phase 0 (infrastructure) -> Phase 1 (S5 preservation + instances) -> Phase 2 (per-system, parallelizable) -> Phase 3 (Cube bridge)

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md items explicitly referenced. This task advances the modal logic infrastructure toward full modal cube coverage.

## Goals & Non-Goals

**Goals**:
- Parameterize DerivationTree over axiom predicates to support multiple modal systems
- Add ModalTHilbert, ModalDHilbert, ModalS4Hilbert typeclasses and tag types to ProofSystem.lean
- Create Modal/ProofSystem/Instances.lean bridging concrete derivation trees to the typeclass hierarchy
- Establish soundness and completeness for systems K, T, D, S4
- Integrate HilbertDerivedRules.lean into the build
- Produce sorry-free Lean 4 code throughout
- Maintain backward compatibility: all existing S5 code must continue to compile

**Non-Goals**:
- Completeness for the remaining 10 cube systems (B, K45, D4, D5, D45, DB, TB, KB5, and compound systems)
- Cube bridge theorems connecting semantic Cube.lean definitions to syntactic proof systems (deferred to future task)
- Naming alignment between Modal (Proposition) and Temporal/Bimodal (Formula)
- Test/example files demonstrating derivations in each system

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| DerivationTree parameterization breaks S5 pipeline | H | M | Keep ModalAxiom as alias for S5 axiom set; test incrementally with lake build after each change |
| K completeness box witness diverges from S5 pattern | M | M | The alternative argument (derive box(bot) then use K+necessitated EFQ) is standard in literature; follow Blackburn Ch. 4 |
| ModalS5Hilbert refactoring to extend ModalS4Hilbert causes Bimodal ripple effects | M | L | Test Bimodal/ProofSystem/Instances.lean compiles after change; field set is unchanged, only inheritance path changes |
| D completeness seriality proof is non-trivial | M | L | Standard argument via axiom D: inconsistency of box-set implies box(bot), then D gives diamond(bot), yielding contradiction |
| Diamond inheritance issues with new typeclass hierarchy | M | L | Lean 4 handles diamond inheritance correctly; test each new class in isolation |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3 | 1 |
| 3 | 4, 5, 6 | 2 |
| 4 | 7 | 4, 5, 6 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Infrastructure Refactoring -- Parameterize DerivationTree and Add Typeclasses [NOT STARTED]

**Goal**: Parameterize the core proof infrastructure over an axiom predicate so that DerivationTree, DeductionTheorem, and MCS work for any normal modal logic. Add intermediate typeclass bundles and tag types.

**Tasks**:
- [ ] Define per-system axiom inductive types (AxiomK, AxiomT, AxiomD, AxiomS4) alongside existing ModalAxiom in DerivationTree.lean
- [ ] Parameterize DerivationTree over `Axioms : Proposition Atom -> Prop` replacing the hardcoded `ModalAxiom`
- [ ] Create type alias so `ModalAxiom` becomes the S5 axiom set, preserving backward compatibility
- [ ] Update the `height` function and height lemmas for the parameterized tree
- [ ] Update `Deriv`, `Derivable`, `modalDerivationSystem` to be parameterized (or create per-system versions)
- [ ] Generalize DeductionTheorem.lean to work over any axiom predicate (mechanical: DT never inspects axiom payload)
- [ ] Generalize MCS.lean: parameterize modal-specific properties, keeping S5-specific lemmas (mcs_box_closure, mcs_box_box) under explicit axiom assumptions
- [ ] Add `ModalTHilbert`, `ModalDHilbert`, `ModalS4Hilbert` bundled classes to ProofSystem.lean
- [ ] Add `Modal.HilbertT`, `Modal.HilbertD`, `Modal.HilbertS4` tag types to ProofSystem.lean
- [ ] Refactor `ModalS5Hilbert` to extend `ModalS4Hilbert` with `HasAxiomB` instead of extending `ModalHilbert` directly with T, 4, B
- [ ] Verify the full project builds (`lake build`) with zero regressions

**Timing**: 5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/DerivationTree.lean` - Parameterize axiom predicates, define per-system axiom types
- `Cslib/Logics/Modal/Metalogic/DeductionTheorem.lean` - Generalize over axiom predicate
- `Cslib/Logics/Modal/Metalogic/MCS.lean` - Generalize, separate S5-specific lemmas
- `Cslib/Foundations/Logic/ProofSystem.lean` - Add new typeclasses, tag types, refactor ModalS5Hilbert
- `Cslib/Logics/Bimodal/ProofSystem/Instances.lean` - May need adjustment if ModalS5Hilbert extends change

**Verification**:
- `lake build` passes with zero new errors
- All existing S5 metalogic files compile unchanged (modulo parameterization)
- Bimodal/ProofSystem/Instances.lean still compiles
- New typeclasses are registered and usable

---

### Phase 2: S5 Preservation and Instances.lean [NOT STARTED]

**Goal**: Create Modal/ProofSystem/Instances.lean registering typeclass instances for all systems (starting with S5), and verify the existing S5 soundness/completeness pipeline still works with the parameterized infrastructure.

**Tasks**:
- [ ] Create `Cslib/Logics/Modal/ProofSystem/Instances.lean` following the Temporal pattern
- [ ] Register `InferenceSystem`, `ModusPonens`, `Necessitation` instances for `Modal.HilbertS5`
- [ ] Register propositional axiom instances (HasAxiomImplyK, HasAxiomImplyS, HasAxiomEFQ, HasAxiomPeirce) for S5
- [ ] Register modal axiom instances (HasAxiomK, HasAxiomT, HasAxiom4, HasAxiomB) for S5
- [ ] Register bundled `ModalS5Hilbert` instance for S5
- [ ] Register instances for K, T, D, S4 tag types (InferenceSystem, ModusPonens, Necessitation, appropriate axiom sets)
- [ ] Register bundled class instances (ModalHilbert for K, ModalTHilbert for T, ModalDHilbert for D, ModalS4Hilbert for S4)
- [ ] Verify Soundness.lean and Completeness.lean still compile with S5 parameterization
- [ ] Update Metalogic.lean aggregator module to import Instances.lean (or create ProofSystem.lean aggregator)
- [ ] `lake build` passes

**Timing**: 3 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Modal/ProofSystem/Instances.lean` - NEW: all typeclass instance registrations
- `Cslib/Logics/Modal/Metalogic.lean` - Update aggregator imports
- `Cslib/Logics/Modal/Metalogic/Soundness.lean` - Adapt to parameterized DerivationTree if needed
- `Cslib/Logics/Modal/Metalogic/Completeness.lean` - Adapt to parameterized framework if needed

**Verification**:
- All existing theorems (soundness_derivable, completeness) still hold
- `#check` of each new instance succeeds
- `lake build` passes

---

### Phase 3: Integrate HilbertDerivedRules.lean [NOT STARTED]

**Goal**: Add the untracked HilbertDerivedRules.lean (447 lines, sorry-free) to the build by importing it into the module graph.

**Tasks**:
- [ ] Determine the appropriate import point (NaturalDeduction aggregator or Equivalence.lean)
- [ ] Add `public import Cslib.Logics.Propositional.NaturalDeduction.HilbertDerivedRules` to the chosen aggregator
- [ ] Verify the file compiles in CI context (`lake build Cslib.Logics.Propositional.NaturalDeduction.HilbertDerivedRules`)
- [ ] `lake build` passes with the new import

**Timing**: 30 minutes

**Depends on**: 1 (infrastructure must be stable before adding new imports)

**Files to modify**:
- `Cslib/Logics/Propositional/NaturalDeduction.lean` or equivalent aggregator - Add import
- `Cslib/Logics/Propositional/NaturalDeduction/HilbertDerivedRules.lean` - No changes expected (already sorry-free)

**Verification**:
- `lake build` passes
- `grep -r "HilbertDerivedRules" Cslib/` shows at least one import

---

### Phase 4: K and T Soundness and Completeness [NOT STARTED]

**Goal**: Establish soundness and completeness for modal logics K and T, with sorry-free proofs.

**Tasks**:
- [ ] Create `Cslib/Logics/Modal/Metalogic/Soundness/K.lean` with K-specific soundness (only propositional + K distribution axioms; valid on all frames)
- [ ] Create `Cslib/Logics/Modal/Metalogic/Completeness/K.lean` with K-specific completeness
  - Canonical model with no frame property requirements
  - Box witness proof with K-specific argument: derive box(bot) from inconsistency, then use K + necessitated EFQ to get box(phi)
  - Truth lemma (identical structure to S5)
- [ ] Create `Cslib/Logics/Modal/Metalogic/Soundness/T.lean` with T-specific soundness (reflexive frames)
- [ ] Create `Cslib/Logics/Modal/Metalogic/Completeness/T.lean` with T-specific completeness
  - Canonical model is reflexive (from axiom T / mcs_box_closure)
  - Simplification of S5: remove transitivity and Euclidean cases
- [ ] Update Metalogic.lean or create per-system aggregators to import new files
- [ ] `lake build` passes

**Timing**: 5 hours

**Depends on**: 2 (Instances.lean and verified parameterized infrastructure)

**Files to create**:
- `Cslib/Logics/Modal/Metalogic/Soundness/K.lean` - K soundness (~80 lines)
- `Cslib/Logics/Modal/Metalogic/Completeness/K.lean` - K completeness (~250 lines)
- `Cslib/Logics/Modal/Metalogic/Soundness/T.lean` - T soundness (~60 lines)
- `Cslib/Logics/Modal/Metalogic/Completeness/T.lean` - T completeness (~200 lines)

**Verification**:
- All four new files compile without sorry
- `lean_verify` on key theorems (K_soundness, K_completeness, T_soundness, T_completeness) shows no axiom usage beyond standard Lean axioms
- `lake build` passes

---

### Phase 5: D Soundness and Completeness [NOT STARTED]

**Goal**: Establish soundness and completeness for modal logic D (serial frames), with sorry-free proofs.

**Tasks**:
- [ ] Create `Cslib/Logics/Modal/Metalogic/Soundness/D.lean` with D-specific soundness (serial frames)
  - D axiom validity proof uses Relation.Serial
- [ ] Create `Cslib/Logics/Modal/Metalogic/Completeness/D.lean` with D-specific completeness
  - Canonical model is serial: for every MCS S, {psi | box psi in S} is consistent
  - Seriality proof: inconsistency implies box(bot) in S, then D gives diamond(bot), combined with box(top) in S yields bot in S, contradiction
  - Box witness proof uses K-style argument (no box_closure since no axiom T)
- [ ] Update aggregator imports
- [ ] `lake build` passes

**Timing**: 3 hours

**Depends on**: 2 (Instances.lean and verified parameterized infrastructure)

**Files to create**:
- `Cslib/Logics/Modal/Metalogic/Soundness/D.lean` - D soundness (~60 lines)
- `Cslib/Logics/Modal/Metalogic/Completeness/D.lean` - D completeness (~250 lines)

**Verification**:
- Both files compile without sorry
- `lean_verify` on D_soundness, D_completeness
- `lake build` passes

---

### Phase 6: S4 Soundness and Completeness [NOT STARTED]

**Goal**: Establish soundness and completeness for modal logic S4 (reflexive + transitive frames), with sorry-free proofs.

**Tasks**:
- [ ] Create `Cslib/Logics/Modal/Metalogic/Soundness/S4.lean` with S4-specific soundness
  - Combines T soundness (reflexivity) and 4 soundness (transitivity)
- [ ] Create `Cslib/Logics/Modal/Metalogic/Completeness/S4.lean` with S4-specific completeness
  - Canonical model is reflexive (from axiom T) AND transitive (from axiom 4)
  - Can reuse canonical_refl proof from T and canonical_trans from S5
  - Box witness identical to T case
- [ ] Update aggregator imports
- [ ] `lake build` passes

**Timing**: 3 hours

**Depends on**: 2 (Instances.lean and verified parameterized infrastructure; also benefits from T proofs in Phase 4 as reference but does not strictly depend on them)

**Files to create**:
- `Cslib/Logics/Modal/Metalogic/Soundness/S4.lean` - S4 soundness (~70 lines)
- `Cslib/Logics/Modal/Metalogic/Completeness/S4.lean` - S4 completeness (~220 lines)

**Verification**:
- Both files compile without sorry
- `lean_verify` on S4_soundness, S4_completeness
- `lake build` passes

---

### Phase 7: Final Integration and Verification [NOT STARTED]

**Goal**: Ensure all new modules integrate cleanly, update aggregator modules, and verify the full project builds.

**Tasks**:
- [ ] Create or update `Cslib/Logics/Modal/ProofSystem.lean` aggregator to import Instances.lean
- [ ] Update `Cslib/Logics/Modal/Metalogic.lean` aggregator to import per-system soundness/completeness files
- [ ] Verify `Cslib/Logics/Modal/Metalogic/Soundness.lean` (original S5) still compiles alongside new per-system files
- [ ] Verify `Cslib/Logics/Modal/Metalogic/Completeness.lean` (original S5) still compiles alongside new per-system files
- [ ] Verify Bimodal/ProofSystem/Instances.lean still compiles
- [ ] Verify Foundations/Logic/Theorems/Modal/S5.lean still works with refactored ModalS5Hilbert
- [ ] Update Metalogic.lean module docstring to reflect multi-system support
- [ ] Full `lake build` with zero errors

**Timing**: 1.5 hours

**Depends on**: 4, 5, 6

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic.lean` - Update aggregator
- `Cslib/Logics/Modal/ProofSystem.lean` - Create or update aggregator
- Various documentation strings

**Verification**:
- `lake build` passes with zero errors
- All modal logic files (K, T, D, S4, S5) accessible via aggregator imports
- No sorry in any new or modified file

## Testing & Validation

- [ ] `lake build` passes after each phase
- [ ] All existing S5 theorems (soundness_derivable, completeness) remain valid
- [ ] Bimodal/ProofSystem/Instances.lean compiles without changes (or with minimal adaptation)
- [ ] Foundations/Logic/Theorems/Modal/ files compile against refactored typeclasses
- [ ] Per-system soundness and completeness theorems verified with `lean_verify`
- [ ] Zero sorry in all new and modified files
- [ ] HilbertDerivedRules.lean accessible via import graph

## Artifacts & Outputs

- `specs/090_expand_modal_cube_proof_systems_metalogic/plans/01_modal-cube-expansion.md` (this file)
- New files to be created:
  - `Cslib/Logics/Modal/ProofSystem/Instances.lean` (~400 lines)
  - `Cslib/Logics/Modal/Metalogic/Soundness/K.lean` (~80 lines)
  - `Cslib/Logics/Modal/Metalogic/Completeness/K.lean` (~250 lines)
  - `Cslib/Logics/Modal/Metalogic/Soundness/T.lean` (~60 lines)
  - `Cslib/Logics/Modal/Metalogic/Completeness/T.lean` (~200 lines)
  - `Cslib/Logics/Modal/Metalogic/Soundness/D.lean` (~60 lines)
  - `Cslib/Logics/Modal/Metalogic/Completeness/D.lean` (~250 lines)
  - `Cslib/Logics/Modal/Metalogic/Soundness/S4.lean` (~70 lines)
  - `Cslib/Logics/Modal/Metalogic/Completeness/S4.lean` (~220 lines)
- Modified files:
  - `Cslib/Logics/Modal/Metalogic/DerivationTree.lean` (parameterized)
  - `Cslib/Logics/Modal/Metalogic/DeductionTheorem.lean` (generalized)
  - `Cslib/Logics/Modal/Metalogic/MCS.lean` (generalized)
  - `Cslib/Foundations/Logic/ProofSystem.lean` (new typeclasses, tags, refactored S5)
  - `Cslib/Logics/Modal/Metalogic.lean` (updated aggregator)
- Estimated total: ~2,200 new lines

## Rollback/Contingency

- Each phase commits independently; revert to previous commit if a phase fails
- Phase 1 (infrastructure) is the highest-risk phase. If DerivationTree parameterization proves infeasible, fall back to creating separate DerivationTree types per system (Option C from research, higher duplication but lower risk)
- If K completeness box witness proof is blocked, mark K completeness as [BLOCKED] and proceed with T, D, S4 (which all have simpler box witness arguments)
- If ModalS5Hilbert refactoring causes Bimodal breakage, keep the original ModalS5Hilbert definition and add ModalS4Hilbert independently (without the extends chain)
