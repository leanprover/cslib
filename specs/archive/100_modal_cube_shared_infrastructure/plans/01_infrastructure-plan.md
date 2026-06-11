# Implementation Plan: Task #100 - Modal Cube Shared Infrastructure

- **Task**: 100 - Modal Cube Shared Infrastructure
- **Status**: [NOT STARTED]
- **Effort**: 4 hours
- **Dependencies**: None (this task unblocks tasks 101-111)
- **Research Inputs**: specs/100_modal_cube_shared_infrastructure/reports/01_infrastructure-research.md
- **Artifacts**: plans/01_infrastructure-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: true

## Overview

Add shared infrastructure for 10 modal cube logics (KB, K4, K5, K45, TB, KB5, D4, D5, D45, DB) by extending three existing Lean files. Phase 1 adds bundled typeclass definitions and tag types to ProofSystem.lean. Phase 2 adds axiom predicates and instance registrations to Instances.lean. Phase 3 adds two new canonical frame property lemmas (canonical_symm and canonical_eucl_from_5) to Completeness.lean. Together these unblock all downstream soundness/completeness tasks (101-111).

### Research Integration

The research report (01_infrastructure-research.md) provides:
- Detailed BRV Theorem 4.28 proof analysis for canonical_symm (symmetry from axiom B alone)
- Corrected proof strategy for canonical_eucl_from_5 (Euclideanness from axiom 5 alone)
- Complete lists of 10 tag types, 10 bundled classes with extends hierarchy, and 10 axiom predicates with constructor counts
- Identification of shared double-negation introduction pattern (d_dni) reusable from existing canonical_eucl
- Risk assessment: Phases 1-2 are low risk (additive, copy-paste patterns); Phase 3 is medium risk (canonical proof construction)

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md found.

## Goals & Non-Goals

**Goals**:
- Add 10 bundled typeclass classes to ProofSystem.lean following the existing ModalHilbert/ModalTHilbert/ModalDHilbert/ModalS4Hilbert/ModalS5Hilbert pattern
- Add 10 opaque tag types to ProofSystem.lean following the existing Modal.HilbertK/HilbertT/etc. pattern
- Add 10 axiom predicates (inductive types) to Instances.lean following the existing KAxiom/TAxiom/DAxiom/S4Axiom pattern
- Register all typeclass instances for all 10 logics in Instances.lean
- Prove canonical_symm (symmetry from axiom B) and canonical_eucl_from_5 (Euclideanness from axiom 5)
- Pass `lake build` with zero errors

**Non-Goals**:
- Individual soundness/completeness theorems for each logic (tasks 101-111)
- Modifying or refactoring existing K/T/D/S4/S5 infrastructure
- Adding truth lemma variants for new logics (those belong to per-logic tasks)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Typeclass diamond/cycle in bundled class hierarchy | H | L | Follow existing extends pattern exactly; each new class has single parent + one HasAxiom |
| Double-negation derivation mismatch in canonical_symm | M | M | Reuse exact d_dni pattern from canonical_eucl (lines 127-133 of Completeness.lean) |
| Diamond/box encoding issues in canonical_eucl_from_5 | M | M | Unfold Proposition.diamond carefully; use lean_goal to verify intermediate states |
| Instance registration order causing synthesis failures | M | L | Register in strict order: InferenceSystem, rules, axioms, bundled classes (bottom-up) |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3 | 1 |

Phases within the same wave can execute in parallel.

### Phase 1: Bundled Classes and Tag Types (ProofSystem.lean) [COMPLETED]

**Goal**: Add 10 new bundled typeclass definitions and 10 new opaque tag types to ProofSystem.lean, extending the existing hierarchy.

**Tasks**:
- [x] Add 10 bundled class definitions after ModalS5Hilbert (line 325), each using `extends` to compose the correct parent class with the correct HasAxiom:
  - `ModalBHilbert` extends `ModalHilbert` + `HasAxiomB`
  - `ModalK4Hilbert` extends `ModalHilbert` + `HasAxiom4`
  - `ModalK5Hilbert` extends `ModalHilbert` + `HasAxiom5`
  - `ModalK45Hilbert` extends `ModalK4Hilbert` + `HasAxiom5`
  - `ModalTBHilbert` extends `ModalTHilbert` + `HasAxiomB`
  - `ModalKB5Hilbert` extends `ModalBHilbert` + `HasAxiom5`
  - `ModalD4Hilbert` extends `ModalDHilbert` + `HasAxiom4`
  - `ModalD5Hilbert` extends `ModalDHilbert` + `HasAxiom5`
  - `ModalD45Hilbert` extends `ModalD4Hilbert` + `HasAxiom5`
  - `ModalDBHilbert` extends `ModalDHilbert` + `HasAxiomB`
- [x] Add 10 opaque tag types after Modal.HilbertS5 (line 388):
  - `Modal.HilbertB` (KB), `Modal.HilbertK4`, `Modal.HilbertK5`, `Modal.HilbertK45`
  - `Modal.HilbertTB`, `Modal.HilbertKB5`
  - `Modal.HilbertD4`, `Modal.HilbertD5`, `Modal.HilbertD45`, `Modal.HilbertDB`
- [x] Verify `lake build Cslib.Foundations.Logic.ProofSystem` passes

**Timing**: 45 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Foundations/Logic/ProofSystem.lean` -- add bundled classes after line 325 and tag types after line 388

**Verification**:
- `lake build Cslib.Foundations.Logic.ProofSystem` compiles without errors
- Each bundled class has the correct extends chain matching the research report hierarchy table

---

### Phase 2: Axiom Predicates and Instance Registrations (Instances.lean) [COMPLETED]

**Goal**: Add 10 axiom predicate inductive types and register all typeclass instances connecting tag types to DerivationTree, following the exact pattern of the existing K/T/D/S4/S5 instance registrations.

**Tasks**:
- [x] Add 10 axiom predicate inductive types after S4Axiom (line 155), each with 4 propositional constructors (implyK, implyS, efq, peirce) and the appropriate modal constructors:
  - `BAxiom` (6 constructors: + modalK, modalB)
  - `K4Axiom` (6 constructors: + modalK, modalFour)
  - `K5Axiom` (6 constructors: + modalK, modalFive)
  - `K45Axiom` (7 constructors: + modalK, modalFour, modalFive)
  - `TBAxiom` (7 constructors: + modalK, modalT, modalB)
  - `KB5Axiom` (7 constructors: + modalK, modalB, modalFive)
  - `D4Axiom` (7 constructors: + modalK, modalD, modalFour)
  - `D5Axiom` (7 constructors: + modalK, modalD, modalFive)
  - `D45Axiom` (8 constructors: + modalK, modalD, modalFour, modalFive)
  - `DBAxiom` (7 constructors: + modalK, modalD, modalB)
- [x] For the `modalFive` constructor in each axiom predicate that includes axiom 5, encode it as: `((Proposition.box (phi.imp .bot)).imp .bot).imp (Proposition.box ((Proposition.box (phi.imp .bot)).imp .bot))` matching the Axiom5 definition in Axioms.lean
- [x] For the `modalB` constructor, encode as: `phi.imp (Proposition.box ((Proposition.box (phi.imp .bot)).imp .bot))` matching AxiomB
- [x] For each of the 10 logics, register the full instance chain after the existing S5 instances (line 501):
  1. `InferenceSystem Modal.HilbertX (Modal.Proposition Atom)` with `derivation phi := Modal.DerivationTree (@Modal.XAxiom Atom) [] phi`
  2. `ModusPonens Modal.HilbertX` (same pattern as K)
  3. `Necessitation Modal.HilbertX` (same pattern as K)
  4. `HasAxiomImplyK`, `HasAxiomImplyS`, `HasAxiomEFQ`, `HasAxiomPeirce` (propositional axioms)
  5. `HasAxiomK` (modal K axiom)
  6. Each additional modal axiom: `HasAxiomT`, `HasAxiom4`, `HasAxiomB`, `HasAxiom5`, `HasAxiomD` as appropriate
  7. Bundled class instances bottom-up: `ModalHilbert`, then parent (e.g., `ModalDHilbert`), then specific (e.g., `ModalD4Hilbert`)
- [x] Verify `lake build Cslib.Logics.Modal.ProofSystem.Instances` passes

**Timing**: 1.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Modal/ProofSystem/Instances.lean` -- add axiom predicates after line 155 and instance registrations after line 501

**Verification**:
- `lake build Cslib.Logics.Modal.ProofSystem.Instances` compiles without errors
- Each logic has the complete instance chain verified by typeclass synthesis (the empty `where` body for bundled class instances)
- Spot-check: `lean_hover_info` on a bundled class instance confirms correct types

---

### Phase 3: Canonical Frame Property Lemmas (Completeness.lean) [COMPLETED]

**Goal**: Prove canonical_symm (the canonical frame of any logic containing axiom B is symmetric) and canonical_eucl_from_5 (the canonical frame of any logic containing axiom 5 is Euclidean). Both follow BRV Chapter 4 canonicity framework.

**Tasks**:
- [x] Add `canonical_symm` after `canonical_trans` (before `canonical_eucl`, around line 94) with signature:
  ```
  theorem canonical_symm
      {Axioms : Proposition Atom -> Prop}
      (h_implyK : ...) (h_implyS : ...)
      (h_K : ...) (h_B : ...)
      (S T : CanonicalWorld Axioms) :
      (CanonicalModel Axioms).r S T ->
      (CanonicalModel Axioms).r T S
  ```
  Proof strategy (BRV 4.28 clause 2):
  1. Take arbitrary phi with `box phi in T.val`, need `phi in S.val`
  2. By contradiction: assume `phi not in S.val`
  3. `neg phi in S.val` via `mcs_neg_of_not_mem`
  4. `box(diamond(neg phi)) in S.val` via `mcs_box_diamond` (axiom B)
  5. `diamond(neg phi) in T.val` via `hST`
  6. From `box phi in T.val`, derive `box(neg neg phi) in T.val` using the d_dni double-negation introduction pattern from canonical_eucl
  7. Contradiction: `diamond(neg phi)` and `box(neg neg phi)` in T.val gives `bot in T.val` via `modal_implication_property`; contradicts `mcs_bot_not_mem`

- [x] Add `canonical_eucl_from_5` after `canonical_eucl` (around line 142) with signature:
  ```
  theorem canonical_eucl_from_5
      {Axioms : Proposition Atom -> Prop}
      (h_implyK : ...) (h_implyS : ...)
      (h_K : ...) (h_5 : ...)
      (S T U : CanonicalWorld Axioms) :
      (CanonicalModel Axioms).r S T ->
      (CanonicalModel Axioms).r S U ->
      (CanonicalModel Axioms).r T U
  ```
  Proof strategy (standard canonicity of axiom 5):
  1. Take arbitrary phi with `box phi in T.val`, need `phi in U.val`
  2. By contradiction: assume `phi not in U.val`
  3. `neg phi in U.val` via `mcs_neg_of_not_mem`
  4. Establish `diamond(neg phi) in S.val` via sub-contradiction:
     - If not, then `box(neg neg phi) in S.val`
     - By `hSU`: `neg neg phi in U.val`
     - With `neg phi in U.val`, get `bot in U.val` via `modal_implication_property`; contradiction
  5. By axiom 5 + MP: `box(diamond(neg phi)) in S.val`
  6. By `hST`: `diamond(neg phi) in T.val`
  7. From `box phi in T.val`, derive `box(neg neg phi) in T.val` (same d_dni pattern)
  8. Contradiction: `diamond(neg phi)` and `box(neg neg phi)` in T.val gives `bot in T.val`

- [x] Use `lean_goal` at key proof positions to verify intermediate goal states match expectations
- [x] Verify `lake build Cslib.Logics.Modal.Metalogic.Completeness` passes

**Timing**: 1.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Completeness.lean` -- add canonical_symm after canonical_trans and canonical_eucl_from_5 after canonical_eucl

**Verification**:
- `lake build Cslib.Logics.Modal.Metalogic.Completeness` compiles without errors
- `lean_verify` on both theorems confirms no sorry or axioms
- Both proofs use only existing MCS infrastructure (no new helper lemmas needed)

---

## Testing & Validation

- [ ] `lake build Cslib.Foundations.Logic.ProofSystem` -- Phase 1 bundled classes and tag types
- [ ] `lake build Cslib.Logics.Modal.ProofSystem.Instances` -- Phase 2 axiom predicates and instances
- [ ] `lake build Cslib.Logics.Modal.Metalogic.Completeness` -- Phase 3 canonical lemmas
- [ ] `lake build` -- Full project build passes (no regressions)
- [ ] `lean_verify` on `Cslib.Logic.Modal.canonical_symm` -- no sorry, no axioms
- [ ] `lean_verify` on `Cslib.Logic.Modal.canonical_eucl_from_5` -- no sorry, no axioms
- [ ] Grep for `sorry` in all modified files: zero occurrences

## Artifacts & Outputs

- `Cslib/Foundations/Logic/ProofSystem.lean` (modified) -- 10 bundled classes + 10 tag types
- `Cslib/Logics/Modal/ProofSystem/Instances.lean` (modified) -- 10 axiom predicates + ~100 instance registrations
- `Cslib/Logics/Modal/Metalogic/Completeness.lean` (modified) -- canonical_symm + canonical_eucl_from_5
- `specs/100_modal_cube_shared_infrastructure/plans/01_infrastructure-plan.md` (this file)

## Rollback/Contingency

All changes are additive (no existing code modified). Rollback via `git checkout main -- <file>` for each of the three files. If Phase 3 proofs are blocked, Phases 1-2 can still be committed independently since they provide value for downstream tasks (the canonical lemmas can be added later via a separate task or as part of individual completeness tasks 101-111).
