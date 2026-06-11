# Implementation Plan: Task #93

- **Task**: 93 - Register typeclass instances for all modal systems (K, T, D, S4, S5)
- **Status**: [COMPLETED]
- **Effort**: 3 hours
- **Dependencies**: Task 92 (completed -- parameterized DerivationTree)
- **Research Inputs**: specs/093_modal_s5_preservation_instances/reports/01_modal-system-instances.md
- **Artifacts**: plans/01_modal-system-instances.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: true

## Overview

Create `Cslib/Logics/Modal/ProofSystem/Instances.lean` registering typeclass instances that connect the abstract proof system hierarchy (from `ProofSystem.lean`) to the concrete parameterized `DerivationTree` (from task 92) for all five normal modal logics: K, T, D, S4, and S5. This follows the established pattern from `Bimodal/ProofSystem/Instances.lean` and `Temporal/ProofSystem/Instances.lean`. The file defines 4 new axiom inductive types (KAxiom, TAxiom, DAxiom, S4Axiom), reuses the existing ModalAxiom for S5, and registers InferenceSystem, inference rule, axiom, and bundled class instances for each system.

### Research Integration

Research report `reports/01_modal-system-instances.md` confirmed:
- DerivationTree is parameterized over `Axioms : Proposition Atom -> Prop` (task 92)
- All 5 tag types (Modal.HilbertK/T/D/S4/S5) and bundled classes exist in ProofSystem.lean
- Instance pattern validated via `lean_run_code` for all 5 systems
- Definitional equality between polymorphic axiom abbreviations and constructor formulas verified
- Dot notation must be avoided in axiom predicate constructors (use `Modal.Proposition.imp` etc.)
- Diamond in AxiomD/AxiomB expands to `imp (box (imp phi bot)) bot`
- S5 reuses existing ModalAxiom for backward compatibility

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md items explicitly reference this task. This is phase 2 of the modal cube expansion (task 90), a prerequisite for tasks 95-98 (per-system soundness/completeness).

## Goals & Non-Goals

**Goals**:
- Define 4 new axiom inductive types: KAxiom, TAxiom, DAxiom, S4Axiom
- Register InferenceSystem, ModusPonens, Necessitation instances for all 5 tag types
- Register propositional axiom instances (HasAxiomImplyK, HasAxiomImplyS, HasAxiomEFQ, HasAxiomPeirce) for all 5 systems
- Register appropriate modal axiom instances per system (K: HasAxiomK; T: +HasAxiomT; D: +HasAxiomD; S4: +HasAxiom4; S5: +HasAxiomB)
- Register bundled class instances (ModalHilbert, ModalTHilbert, ModalDHilbert, ModalS4Hilbert, ModalS5Hilbert)
- Wire Instances.lean into module graph via Metalogic.lean and Cslib.lean
- Verify Soundness.lean and Completeness.lean still compile (zero regressions)

**Non-Goals**:
- Modifying Soundness.lean or Completeness.lean (they use ModalAxiom directly)
- Adding derived rules or theorem-level results
- Creating separate ProofSystem aggregator module (defer to task 98 integration)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Definitional equality failure for axiom constructors | H | L | Research verified via lean_run_code; use fully qualified `Modal.Proposition.*` syntax |
| Diamond expansion mismatch in AxiomD/AxiomB | M | L | Research confirmed expansion: `imp (box (imp phi bot)) bot`; verify with lean_goal |
| Universe polymorphism mismatch | M | L | Use `{Atom : Type u}` matching existing ModalAxiom |
| Import cycle from Instances.lean | M | L | Import only DerivationTree and ProofSystem (no cycles possible) |
| Regression in Soundness/Completeness | H | L | These files use ModalAxiom directly, not typeclass instances |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |

Phases within the same wave can execute in parallel.

### Phase 1: Create Instances.lean with Axiom Predicates and All Instances [COMPLETED]

**Goal**: Create the complete `Cslib/Logics/Modal/ProofSystem/Instances.lean` file with all axiom inductive types and instance registrations for K, T, D, S4, S5.

**Tasks**:
- [x] Create directory `Cslib/Logics/Modal/ProofSystem/` *(completed)*
- [x] Create `Instances.lean` with copyright header and module imports *(completed)*
- [x] Define `KAxiom` inductive: 4 propositional (implyK, implyS, efq, peirce) + modalK *(completed)*
- [x] Define `TAxiom` inductive: 4 propositional + modalK, modalT *(completed)*
- [x] Define `DAxiom` inductive: 4 propositional + modalK, modalD *(completed)*
- [x] Define `S4Axiom` inductive: 4 propositional + modalK, modalT, modalFour *(completed)*
- [x] Register K instances: InferenceSystem, ModusPonens, Necessitation, 4 propositional axioms, HasAxiomK, ModalHilbert *(completed)*
- [x] Register T instances: InferenceSystem, ModusPonens, Necessitation, 4 propositional axioms, HasAxiomK, HasAxiomT, ModalHilbert, ModalTHilbert *(completed)*
- [x] Register D instances: InferenceSystem, ModusPonens, Necessitation, 4 propositional axioms, HasAxiomK, HasAxiomD, ModalHilbert, ModalDHilbert *(completed)*
- [x] Register S4 instances: InferenceSystem, ModusPonens, Necessitation, 4 propositional axioms, HasAxiomK, HasAxiomT, HasAxiom4, ModalHilbert, ModalTHilbert, ModalS4Hilbert *(completed)*
- [x] Register S5 instances (using existing ModalAxiom): InferenceSystem, ModusPonens, Necessitation, 4 propositional axioms, HasAxiomK, HasAxiomT, HasAxiom4, HasAxiomB, ModalHilbert, ModalTHilbert, ModalS4Hilbert, ModalS5Hilbert *(completed)*
- [x] Use `DerivationTree.ax` for axiom instances (not `DerivationTree.axiom` -- verify constructor name) *(completed)*
- [x] Use fully qualified `Modal.Proposition.imp`, `Modal.Proposition.box`, `Modal.Proposition.bot` in axiom predicates *(completed)*
- [x] Verify file compiles via `lake build Cslib.Logics.Modal.ProofSystem.Instances` (may need Cslib.lean import first) *(completed -- verified via lean_goal, no errors)*

**Timing**: 2 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/ProofSystem/Instances.lean` -- NEW (~400 lines)

**Verification**:
- File compiles without errors
- All 5 bundled class instances registered
- No `sorry` in file

**Implementation Notes**:

Axiom predicate constructors must use fully qualified syntax to ensure definitional equality:

```lean
inductive KAxiom : Modal.Proposition Atom -> Prop where
  | implyK (phi psi : Modal.Proposition Atom) :
      KAxiom (Modal.Proposition.imp phi (Modal.Proposition.imp psi phi))
  -- ... etc.
```

Instance pattern per system (K example):
```lean
instance : InferenceSystem Modal.HilbertK (Modal.Proposition Atom) where
  derivation phi := Modal.DerivationTree (@KAxiom Atom) [] phi

instance : ModusPonens Modal.HilbertK (F := Modal.Proposition Atom) where
  mp := fun h1 h2 => by
    obtain <d1> := h1; obtain <d2> := h2
    exact <Modal.DerivationTree.modus_ponens [] _ _ d1 d2>

instance : Necessitation Modal.HilbertK (F := Modal.Proposition Atom) where
  nec := fun h => by
    obtain <d> := h
    exact <Modal.DerivationTree.necessitation _ d>
```

Diamond expansion for AxiomD and AxiomB:
- `diamond phi = neg (box (neg phi)) = imp (box (imp phi bot)) bot`
- Constructors must match this expansion exactly

---

### Phase 2: Wire Imports and Verify Full Build [COMPLETED]

**Goal**: Add Instances.lean to the module graph and verify zero regressions across the full project.

**Tasks**:
- [x] Add `public import Cslib.Logics.Modal.ProofSystem.Instances` to `Cslib/Logics/Modal/Metalogic.lean` *(completed)*
- [x] Add `public import Cslib.Logics.Modal.ProofSystem.Instances` to `Cslib.lean` *(completed)*
- [x] Run `lake build` to verify full project builds with zero errors *(completed -- 2916 jobs, zero errors)*
- [x] Verify Soundness.lean and Completeness.lean still compile (no regressions) *(completed -- full build passed)*
- [x] Verify Bimodal/ProofSystem/Instances.lean still compiles *(completed -- full build passed)*
- [x] Grep for `sorry` in new file to confirm zero occurrences *(completed -- zero sorries)*

**Timing**: 30 minutes

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic.lean` -- add import line
- `Cslib.lean` -- add import line

**Verification**:
- `lake build` passes with zero errors
- `grep -r sorry Cslib/Logics/Modal/ProofSystem/Instances.lean` returns empty
- Soundness.lean, Completeness.lean, and Bimodal/ProofSystem/Instances.lean unchanged and compiling

## Testing & Validation

- [ ] `lake build Cslib.Logics.Modal.ProofSystem.Instances` compiles without errors
- [ ] `lake build` full project passes with zero errors
- [ ] Zero `sorry` occurrences in Instances.lean
- [ ] All 5 bundled instances registered: ModalHilbert (K), ModalTHilbert (T), ModalDHilbert (D), ModalS4Hilbert (S4), ModalS5Hilbert (S5)
- [ ] Existing Soundness.lean and Completeness.lean compile unchanged
- [ ] Bimodal/ProofSystem/Instances.lean compiles unchanged

## Artifacts & Outputs

- `Cslib/Logics/Modal/ProofSystem/Instances.lean` -- new file (~400 lines)
- `Cslib/Logics/Modal/Metalogic.lean` -- updated with import
- `Cslib.lean` -- updated with import
- `specs/093_modal_s5_preservation_instances/plans/01_modal-system-instances.md` -- this plan
- `specs/093_modal_s5_preservation_instances/summaries/01_modal-system-instances-summary.md` -- execution summary (after implementation)

## Rollback/Contingency

- Delete `Cslib/Logics/Modal/ProofSystem/` directory
- Revert import additions in `Metalogic.lean` and `Cslib.lean`
- No other files are modified, so rollback is clean
