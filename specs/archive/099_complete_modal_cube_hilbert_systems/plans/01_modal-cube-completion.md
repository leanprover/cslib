# Implementation Plan: Task #99

- **Task**: 99 - Complete modal cube Hilbert proof systems
- **Status**: [IMPLEMENTING]
- **Effort**: 16 hours
- **Dependencies**: None (builds on existing K/T/D/S4/S5 infrastructure)
- **Research Inputs**: specs/099_complete_modal_cube_hilbert_systems/reports/01_team-research.md
- **Artifacts**: plans/01_modal-cube-completion.md
- **Standards**: plan-format.md, status-markers.md, artifact-management.md
- **Type**: lean4
- **Lean Intent**: true

## Overview

Construct Hilbert proof systems with soundness and completeness for all 10 remaining logics in the modal cube (B, K4, K5, K45, D4, D5, D45, DB, TB, KB5). The implementation leverages the fully parameterized infrastructure already in place: `soundness` with `h_ax_sound` callbacks, three truth lemma variants (`truth_lemma`, `truth_lemma_d`, `k_truth_lemma`), canonical model construction, and four existing canonical frame property lemmas (`canonical_refl`, `canonical_trans`, `canonical_eucl`, `canonical_serial`). Only two genuinely new mathematical proofs are required: `canonical_symm` (symmetry from axiom B alone) and `canonical_eucl_from_5` (Euclideanness from axiom 5 alone). Everything else is systematic composition of existing patterns.

### Research Integration

The team research report (4 teammates) confirmed:
- All 6 individual axiom typeclasses (`HasAxiomK/T/4/B/5/D`) exist.
- All 6 semantic validity lemmas (`Satisfies.k/t/b/four/five/d`) exist.
- The parameterized `soundness` theorem, three truth lemma variants, and the canonical model construction are fully reusable.
- Only `canonical_symm` and `canonical_eucl_from_5` need to be proved from scratch.
- Each logic maps to exactly one truth lemma variant based on whether it has T (use `truth_lemma`), D without T (use `truth_lemma_d`), or neither (use `k_truth_lemma`).
- MCS helper `mcs_box_diamond` already exists (used by `canonical_eucl`), providing the B-axiom interaction needed for `canonical_symm`.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This task advances the modal metalogic component of the project. While not explicitly listed as a remaining item in ROADMAP.md (which focuses on bimodal, temporal, and continuous completeness), completing the modal cube Hilbert systems strengthens the modal foundation used by downstream modules.

## Goals & Non-Goals

**Goals**:
- Define 10 new axiom predicates (inductive types) in `Instances.lean`
- Add 10 new tag types to `ProofSystem.lean`
- Add 10 new bundled classes to `ProofSystem.lean` (following the existing K/T/D/S4/S5 pattern)
- Register all typeclass instances for the 10 new systems
- Prove `canonical_symm` (symmetry from axiom B alone)
- Prove `canonical_eucl_from_5` (Euclideanness from axiom 5 alone)
- Prove soundness for all 10 logics (20 files: `{Logic}Soundness.lean`)
- Prove completeness for all 10 logics (20 files: `{Logic}Completeness.lean`)
- Update `Metalogic.lean` aggregator with all new imports
- Verify `lake build` passes for the full module

**Non-Goals**:
- Refactoring the shared contrapositive setup across completeness proofs (follow-up task)
- Cube bridge theorems connecting semantic (Cube.lean) and syntactic characterizations
- Bimodal or temporal integration
- New truth lemma variants (all 3 needed variants already exist)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `canonical_eucl_from_5` proof is hard (DNE derivation tree gymnastics) | H | H | Follow the detailed proof strategy from Teammate C; use `canonical_eucl` (Completeness.lean:95-141) as a template for derivation tree manipulation |
| `canonical_symm` proof requires B-axiom derivation steps | M | M | Proof strategy clearly outlined in research; `mcs_box_diamond` already handles the B-axiom interaction in MCS |
| Diamond encoding `(box(phi->bot))->bot` makes proofs syntactically heavy | M | H | Established pattern in `canonical_eucl` lines 127-141; follow exactly |
| Code volume (20+ new files) risks mechanical errors | L | M | Soundness files are near-identical by pattern; completeness files compose existing lemmas; use existing files as literal templates |
| Typeclass instance resolution may be slow with 15 systems | L | L | Tag types are opaque so instances are direct; no diamond inheritance issues |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3, 4 | 1 |
| 3 | 5, 6, 7, 8 | 1 (2, 3, 4 are for code reference only, not build deps) |
| 4 | 9, 10, 11 | 1 (same note) |
| 5 | 12 | 1-11 |

---

### Phase 1: Shared Infrastructure [NOT STARTED]

**Goal**: Prove the two critical canonical frame property lemmas (`canonical_symm`, `canonical_eucl_from_5`), add all 10 tag types, bundled classes, axiom predicates, and instance registrations.

**Tasks**:
- [ ] Add 10 new tag types to `ProofSystem.lean` (after `Modal.HilbertS5`):
  - `Modal.HilbertB`, `Modal.HilbertK4`, `Modal.HilbertK5`, `Modal.HilbertK45`
  - `Modal.HilbertD4`, `Modal.HilbertD5`, `Modal.HilbertD45`, `Modal.HilbertDB`
  - `Modal.HilbertTB`, `Modal.HilbertKB5`
- [ ] Add 10 new bundled classes to `ProofSystem.lean` (after `ModalS5Hilbert`):
  - `ModalBHilbert` extends `ModalHilbert` + `HasAxiomB`
  - `ModalK4Hilbert` extends `ModalHilbert` + `HasAxiom4`
  - `ModalK5Hilbert` extends `ModalHilbert` + `HasAxiom5`
  - `ModalK45Hilbert` extends `ModalK4Hilbert` + `HasAxiom5` (or `ModalHilbert` + `HasAxiom4` + `HasAxiom5`)
  - `ModalD4Hilbert` extends `ModalDHilbert` + `HasAxiom4`
  - `ModalD5Hilbert` extends `ModalDHilbert` + `HasAxiom5`
  - `ModalD45Hilbert` extends `ModalDHilbert` + `HasAxiom4` + `HasAxiom5`
  - `ModalDBHilbert` extends `ModalDHilbert` + `HasAxiomB`
  - `ModalTBHilbert` extends `ModalTHilbert` + `HasAxiomB`
  - `ModalKB5Hilbert` extends `ModalBHilbert` + `HasAxiom5` (or `ModalHilbert` + `HasAxiomB` + `HasAxiom5`)
- [ ] Define 10 axiom predicates in `Instances.lean` (follow `KAxiom`/`TAxiom`/`DAxiom`/`S4Axiom`/`ModalAxiom` pattern):
  - `BAxiom` (K + B): propositional (4) + `modalK` + `modalB`
  - `K4Axiom` (K + 4): propositional (4) + `modalK` + `modalFour`
  - `K5Axiom` (K + 5): propositional (4) + `modalK` + `modalFive`
  - `K45Axiom` (K + 4 + 5): propositional (4) + `modalK` + `modalFour` + `modalFive`
  - `D4Axiom` (K + D + 4): propositional (4) + `modalK` + `modalD` + `modalFour`
  - `D5Axiom` (K + D + 5): propositional (4) + `modalK` + `modalD` + `modalFive`
  - `D45Axiom` (K + D + 4 + 5): propositional (4) + `modalK` + `modalD` + `modalFour` + `modalFive`
  - `DBAxiom` (K + D + B): propositional (4) + `modalK` + `modalD` + `modalB`
  - `TBAxiom` (K + T + B): propositional (4) + `modalK` + `modalT` + `modalB`
  - `KB5Axiom` (K + B + 5): propositional (4) + `modalK` + `modalB` + `modalFive`
- [ ] Register all typeclass instances for 10 new systems in `Instances.lean` (follow exact pattern from K/T/D/S4/S5 sections):
  - For each system: `InferenceSystem`, `ModusPonens`, `Necessitation`, `HasAxiomImplyK`, `HasAxiomImplyS`, `HasAxiomEFQ`, `HasAxiomPeirce`, `HasAxiomK`, plus system-specific axiom instances, plus bundled class instance(s)
- [ ] Prove `canonical_symm` in `Completeness.lean` (after `canonical_eucl`):
  - **Signature**: Takes `h_implyK`, `h_implyS`, `h_efq`, `h_peirce`, `h_K`, `h_B` axiom callbacks; returns `(CanonicalModel Axioms).r S T -> (CanonicalModel Axioms).r T S`
  - **Proof strategy** (Blackburn Thm 4.28 clause 2):
    1. Assume `R(S,T)` (canonical). Take `box(phi) in T`. Need `phi in S`.
    2. By contraposition: assume `phi not in S`, then `neg(phi) in S` (MCS).
    3. By axiom B at S: `neg(phi) -> box(diamond(neg(phi)))`, so `box(diamond(neg(phi))) in S` via `mcs_box_diamond`.
    4. Since `R(S,T)`: `diamond(neg(phi)) in T`.
    5. Diamond encoding: `diamond(neg(phi)) = (box(neg(neg(phi)))) -> bot = (box((phi->bot)->bot)) -> bot`.
    6. From `box(phi) in T`, derive `box((phi->bot)->bot) in T` via necessitation of DNE introduction (derivation tree: build `phi -> ((phi->bot)->bot)`, necessitate, apply K+box_mp).
    7. Then `(box((phi->bot)->bot)) -> bot in T` and `box((phi->bot)->bot) in T` gives `bot in T` -- contradiction with MCS.
  - **Key helper**: Follow the DNE derivation tree pattern from `canonical_eucl` (Completeness.lean lines 127-141), which already builds `box(bp -> ((bp->bot)->bot))` via `deductionTheorem` + necessitation + `mcs_box_mp`.
- [ ] Prove `canonical_eucl_from_5` in `Completeness.lean` (after `canonical_symm`):
  - **Signature**: Takes `h_implyK`, `h_implyS`, `h_efq`, `h_peirce`, `h_K`, `h_5` axiom callbacks; returns `(CanonicalModel Axioms).r S T -> (CanonicalModel Axioms).r S U -> (CanonicalModel Axioms).r T U`
  - **Proof strategy** (Blackburn Thm 4.28 clause 4, research Teammate C):
    1. Assume `R(S,T)` and `R(S,U)`. Take `box(phi) in T`. Need `phi in U`.
    2. By contraposition: assume `box(phi) not in S` (if `box(phi) in S`, then `phi in U` via `R(S,U)`, done).
    3. `box(phi) not in S` implies `neg(box(phi)) in S`, i.e., `diamond(neg(phi)) in S`.
    4. Wait -- more carefully: we need `diamond(neg(phi)) in S`. Since `box(phi) not in S`, we get `neg(box(phi)) in S`. Now `neg(box(phi)) = box(phi) -> bot`. And `diamond(neg(phi)) = (box((phi->bot)->bot)) -> bot`. These are different formulas. The actual approach:
    5. Assume `box(phi) not in S`. Then by `mcs_neg_of_not_mem`: `(box(phi) -> bot) in S`.
    6. Key: need to derive `◇¬φ ∈ S`, i.e., `(□(¬φ→⊥))→⊥ ∈ S`. Actually, we should show: from `¬□φ ∈ S` and axiom 5, derive `□¬□φ ∈ S`. Then since `R(S,T)`: `¬□φ ∈ T`, contradicting `□φ ∈ T`.
    7. Simpler proof: By contraposition. Assume `□φ ∈ T`. Want `φ ∈ U`.
       - Case 1: `□φ ∈ S`. Then `φ ∈ U` via `R(S,U)`. Done.
       - Case 2: `□φ ∉ S`. Then `¬□φ ∈ S` by MCS. Now `¬□φ = (□φ) → ⊥ = ◇(¬φ)` only if `¬φ = φ → ⊥`. Actually `¬□φ = (□φ)→⊥`, and `◇(¬φ) = (□((φ→⊥)→⊥))→⊥`. These are NOT the same formula.
       - The correct approach uses axiom 5 directly: `◇ψ → □◇ψ`. Apply with `ψ = ¬φ`:
         `◇(¬φ) → □◇(¬φ)`.
       - Need to show: `◇(¬φ) ∈ S`. This follows from `□φ ∉ S` via a derivation argument similar to `canonical_eucl`.
       - Then axiom 5 gives `□◇(¬φ) ∈ S`. Since `R(S,T)`: `◇(¬φ) ∈ T`.
       - But `□φ ∈ T` implies `□¬¬φ ∈ T` (via DNE introduction + K + NEC, same derivation tree as in `canonical_eucl`).
       - `◇(¬φ) = (□((φ→⊥)→⊥))→⊥ = ¬(□¬¬φ)`. So `¬(□¬¬φ) ∈ T` and `□¬¬φ ∈ T` gives `⊥ ∈ T`. Contradiction.
    8. The derivation tree for DNE introduction (`□φ ∈ T ⊢ □¬¬φ ∈ T`) follows `canonical_eucl` lines 127-141 exactly. The new content is the axiom 5 application, which is a single `mcs_mp_axiom` call.
  - **Key helper needed**: `mcs_five_eucl` -- from `◇φ ∈ S` derive `□◇φ ∈ S` using axiom 5. This is simply `mcs_mp_axiom h_implyK h_implyS h_mcs h_dia (h_5 φ)`, following the pattern of `mcs_box_diamond` (which does the same for axiom B). Add to `MCS.lean` or inline.
- [ ] Verify Phase 1 builds: `lake build Cslib.Logics.Modal.ProofSystem.Instances` and `lake build Cslib.Logics.Modal.Metalogic.Completeness`

**Timing**: 4 hours (2h for `canonical_symm` + `canonical_eucl_from_5`, 1.5h for axiom predicates + instances, 0.5h for tag types + bundled classes)

**Depends on**: none

**Files to modify**:
- `Cslib/Foundations/Logic/ProofSystem.lean` -- add 10 tag types + 10 bundled classes
- `Cslib/Logics/Modal/ProofSystem/Instances.lean` -- add 10 axiom predicates + instance registrations
- `Cslib/Logics/Modal/Metalogic/Completeness.lean` -- add `canonical_symm` + `canonical_eucl_from_5`
- `Cslib/Logics/Modal/Metalogic/MCS.lean` -- optionally add `mcs_five_eucl` helper (or inline in Completeness.lean)

**Verification**:
- `lake build Cslib.Logics.Modal.ProofSystem.Instances` succeeds
- `lake build Cslib.Logics.Modal.Metalogic.Completeness` succeeds
- All 10 bundled class instances resolve without timeout
- `canonical_symm` and `canonical_eucl_from_5` have no `sorry`

---

### Phase 2: B (KB) Soundness + Completeness [NOT STARTED]

**Goal**: Prove soundness and completeness for modal logic B (K + axiom B) over symmetric frames.

**Tasks**:
- [ ] Create `Cslib/Logics/Modal/Metalogic/BSoundness.lean`:
  - Import `Soundness.lean` + `Instances.lean`
  - Prove `b_axiom_sound`: dispatch propositional/K cases identically to `k_axiom_sound`; for `modalB`, use `Satisfies.b` with symmetry hypothesis
  - Prove `b_soundness` and `b_soundness_derivable` wrappers via parameterized `soundness`
  - Frame hypothesis: `h_symm : forall w1 w2, m.r w1 w2 -> m.r w2 w1`
- [ ] Create `Cslib/Logics/Modal/Metalogic/BCompleteness.lean`:
  - Import `KCompleteness.lean` (for `k_truth_lemma`, `k_mcs_box_witness`) + `Completeness.lean` (for `canonical_symm`) + `Instances.lean`
  - Truth lemma: use `k_truth_lemma` (B has no T or D)
  - Canonical frame property: `canonical_symm` from Phase 1
  - Completeness: `b_completeness` -- follows `k_completeness` structure but with symmetry hypothesis in `h_valid` and `canonical_symm` in the canonical model
  - Validity hypothesis type: `forall World m, (forall w1 w2, m.r w1 w2 -> m.r w2 w1) -> forall w, Satisfies m w phi`
- [ ] Verify: `lake build Cslib.Logics.Modal.Metalogic.BCompleteness`

**Timing**: 1 hour

**Depends on**: 1

**Files to create**:
- `Cslib/Logics/Modal/Metalogic/BSoundness.lean`
- `Cslib/Logics/Modal/Metalogic/BCompleteness.lean`

**Verification**:
- Both files compile without `sorry`
- `b_axiom_sound`, `b_soundness`, `b_soundness_derivable`, `b_completeness` are defined

---

### Phase 3: K4 (Four) Soundness + Completeness [NOT STARTED]

**Goal**: Prove soundness and completeness for modal logic K4 (K + axiom 4) over transitive frames.

**Tasks**:
- [ ] Create `Cslib/Logics/Modal/Metalogic/K4Soundness.lean`:
  - Prove `k4_axiom_sound`: propositional/K cases + `modalFour` via `Satisfies.four` with transitivity
  - Frame hypothesis: `h_trans : forall w1 w2 w3, m.r w1 w2 -> m.r w2 w3 -> m.r w1 w3`
- [ ] Create `Cslib/Logics/Modal/Metalogic/K4Completeness.lean`:
  - Truth lemma: `k_truth_lemma` (K4 has no T or D)
  - Canonical frame property: `canonical_trans` (already exists)
  - Completeness: `k4_completeness` -- analogous to `k_completeness` with transitivity
  - Validity hypothesis: `forall World m, (forall w1 w2 w3, m.r w1 w2 -> m.r w2 w3 -> m.r w1 w3) -> forall w, Satisfies m w phi`
- [ ] Verify: `lake build Cslib.Logics.Modal.Metalogic.K4Completeness`

**Timing**: 1 hour

**Depends on**: 1

**Files to create**:
- `Cslib/Logics/Modal/Metalogic/K4Soundness.lean`
- `Cslib/Logics/Modal/Metalogic/K4Completeness.lean`

**Verification**:
- Both files compile without `sorry`

---

### Phase 4: K5 (Five) Soundness + Completeness [NOT STARTED]

**Goal**: Prove soundness and completeness for modal logic K5 (K + axiom 5) over Euclidean frames.

**Tasks**:
- [ ] Create `Cslib/Logics/Modal/Metalogic/K5Soundness.lean`:
  - Prove `k5_axiom_sound`: propositional/K cases + `modalFive` via `Satisfies.five` with Euclideanness
  - Frame hypothesis: `h_eucl : forall w1 w2 w3, m.r w1 w2 -> m.r w1 w3 -> m.r w2 w3`
- [ ] Create `Cslib/Logics/Modal/Metalogic/K5Completeness.lean`:
  - Truth lemma: `k_truth_lemma` (K5 has no T or D)
  - Canonical frame property: `canonical_eucl_from_5` from Phase 1
  - Completeness: `k5_completeness`
  - Validity hypothesis: `forall World m, (forall w1 w2 w3, m.r w1 w2 -> m.r w1 w3 -> m.r w2 w3) -> forall w, Satisfies m w phi`
- [ ] Verify: `lake build Cslib.Logics.Modal.Metalogic.K5Completeness`

**Timing**: 1 hour

**Depends on**: 1

**Files to create**:
- `Cslib/Logics/Modal/Metalogic/K5Soundness.lean`
- `Cslib/Logics/Modal/Metalogic/K5Completeness.lean`

**Verification**:
- Both files compile without `sorry`

---

### Phase 5: K45 Soundness + Completeness [NOT STARTED]

**Goal**: Prove soundness and completeness for modal logic K45 (K + 4 + 5) over transitive + Euclidean frames.

**Tasks**:
- [ ] Create `Cslib/Logics/Modal/Metalogic/K45Soundness.lean`:
  - Prove `k45_axiom_sound`: propositional/K + `modalFour` (transitivity) + `modalFive` (Euclideanness)
  - Frame hypotheses: `h_trans` + `h_eucl`
- [ ] Create `Cslib/Logics/Modal/Metalogic/K45Completeness.lean`:
  - Truth lemma: `k_truth_lemma`
  - Canonical frame properties: `canonical_trans` + `canonical_eucl_from_5`
  - Completeness: `k45_completeness`
- [ ] Verify: `lake build Cslib.Logics.Modal.Metalogic.K45Completeness`

**Timing**: 1 hour

**Depends on**: 1

**Files to create**:
- `Cslib/Logics/Modal/Metalogic/K45Soundness.lean`
- `Cslib/Logics/Modal/Metalogic/K45Completeness.lean`

**Verification**:
- Both files compile without `sorry`

---

### Phase 6: TB (KTB) Soundness + Completeness [NOT STARTED]

**Goal**: Prove soundness and completeness for modal logic TB (K + T + B) over reflexive + symmetric frames.

**Tasks**:
- [ ] Create `Cslib/Logics/Modal/Metalogic/TBSoundness.lean`:
  - Prove `tb_axiom_sound`: propositional/K + `modalT` (reflexivity) + `modalB` (symmetry)
  - Frame hypotheses: `h_refl` + `h_symm`
- [ ] Create `Cslib/Logics/Modal/Metalogic/TBCompleteness.lean`:
  - Truth lemma: `truth_lemma` (TB has axiom T, so use the T-based truth lemma with `mcs_box_witness`)
  - Canonical frame properties: `canonical_refl` + `canonical_symm`
  - Completeness: `tb_completeness`
- [ ] Verify: `lake build Cslib.Logics.Modal.Metalogic.TBCompleteness`

**Timing**: 1 hour

**Depends on**: 1

**Files to create**:
- `Cslib/Logics/Modal/Metalogic/TBSoundness.lean`
- `Cslib/Logics/Modal/Metalogic/TBCompleteness.lean`

**Verification**:
- Both files compile without `sorry`

---

### Phase 7: KB5 Soundness + Completeness [NOT STARTED]

**Goal**: Prove soundness and completeness for modal logic KB5 (K + B + 5) over symmetric + Euclidean frames.

**Tasks**:
- [ ] Create `Cslib/Logics/Modal/Metalogic/KB5Soundness.lean`:
  - Prove `kb5_axiom_sound`: propositional/K + `modalB` (symmetry) + `modalFive` (Euclideanness)
  - Frame hypotheses: `h_symm` + `h_eucl`
- [ ] Create `Cslib/Logics/Modal/Metalogic/KB5Completeness.lean`:
  - Truth lemma: `k_truth_lemma` (KB5 has no T or D)
  - Canonical frame properties: `canonical_symm` + `canonical_eucl_from_5` (both from Phase 1; verify they compose independently)
  - Completeness: `kb5_completeness`
  - Note: This is where both new canonical lemmas interact for the first time. The composition should be straightforward since each provides an independent frame property.
- [ ] Verify: `lake build Cslib.Logics.Modal.Metalogic.KB5Completeness`

**Timing**: 1.5 hours (extra time for verifying B+5 interaction)

**Depends on**: 1

**Files to create**:
- `Cslib/Logics/Modal/Metalogic/KB5Soundness.lean`
- `Cslib/Logics/Modal/Metalogic/KB5Completeness.lean`

**Verification**:
- Both files compile without `sorry`
- `canonical_symm` and `canonical_eucl_from_5` compose without issues in KB5 completeness

---

### Phase 8: D4 Soundness + Completeness [NOT STARTED]

**Goal**: Prove soundness and completeness for modal logic D4 (K + D + 4) over serial + transitive frames.

**Tasks**:
- [ ] Create `Cslib/Logics/Modal/Metalogic/D4Soundness.lean`:
  - Prove `d4_axiom_sound`: propositional/K + `modalD` (seriality) + `modalFour` (transitivity)
  - Frame hypotheses: `h_serial : Relation.Serial m.r` + `h_trans`
- [ ] Create `Cslib/Logics/Modal/Metalogic/D4Completeness.lean`:
  - Truth lemma: `truth_lemma_d` (D4 has D but not T)
  - Canonical frame properties: `canonical_serial` + `canonical_trans`
  - Completeness: `d4_completeness`
  - Validity hypothesis: `forall World m, Relation.Serial m.r -> (forall w1 w2 w3, ...) -> forall w, Satisfies m w phi`
- [ ] Verify: `lake build Cslib.Logics.Modal.Metalogic.D4Completeness`

**Timing**: 1 hour

**Depends on**: 1

**Files to create**:
- `Cslib/Logics/Modal/Metalogic/D4Soundness.lean`
- `Cslib/Logics/Modal/Metalogic/D4Completeness.lean`

**Verification**:
- Both files compile without `sorry`

---

### Phase 9: D5 Soundness + Completeness [NOT STARTED]

**Goal**: Prove soundness and completeness for modal logic D5 (K + D + 5) over serial + Euclidean frames.

**Tasks**:
- [ ] Create `Cslib/Logics/Modal/Metalogic/D5Soundness.lean`:
  - Prove `d5_axiom_sound`: propositional/K + `modalD` (seriality) + `modalFive` (Euclideanness)
  - Frame hypotheses: `h_serial` + `h_eucl`
- [ ] Create `Cslib/Logics/Modal/Metalogic/D5Completeness.lean`:
  - Truth lemma: `truth_lemma_d` (D5 has D but not T)
  - Canonical frame properties: `canonical_serial` + `canonical_eucl_from_5`
  - Completeness: `d5_completeness`
- [ ] Verify: `lake build Cslib.Logics.Modal.Metalogic.D5Completeness`

**Timing**: 1 hour

**Depends on**: 1

**Files to create**:
- `Cslib/Logics/Modal/Metalogic/D5Soundness.lean`
- `Cslib/Logics/Modal/Metalogic/D5Completeness.lean`

**Verification**:
- Both files compile without `sorry`

---

### Phase 10: D45 Soundness + Completeness [NOT STARTED]

**Goal**: Prove soundness and completeness for modal logic D45 (K + D + 4 + 5) over serial + transitive + Euclidean frames.

**Tasks**:
- [ ] Create `Cslib/Logics/Modal/Metalogic/D45Soundness.lean`:
  - Prove `d45_axiom_sound`: propositional/K + `modalD` + `modalFour` + `modalFive`
  - Frame hypotheses: `h_serial` + `h_trans` + `h_eucl`
- [ ] Create `Cslib/Logics/Modal/Metalogic/D45Completeness.lean`:
  - Truth lemma: `truth_lemma_d` (D45 has D but not T)
  - Canonical frame properties: `canonical_serial` + `canonical_trans` + `canonical_eucl_from_5`
  - Completeness: `d45_completeness`
- [ ] Verify: `lake build Cslib.Logics.Modal.Metalogic.D45Completeness`

**Timing**: 1 hour

**Depends on**: 1

**Files to create**:
- `Cslib/Logics/Modal/Metalogic/D45Soundness.lean`
- `Cslib/Logics/Modal/Metalogic/D45Completeness.lean`

**Verification**:
- Both files compile without `sorry`

---

### Phase 11: DB Soundness + Completeness [NOT STARTED]

**Goal**: Prove soundness and completeness for modal logic DB (K + D + B) over serial + symmetric frames.

**Tasks**:
- [ ] Create `Cslib/Logics/Modal/Metalogic/DBSoundness.lean`:
  - Prove `db_axiom_sound`: propositional/K + `modalD` (seriality) + `modalB` (symmetry)
  - Frame hypotheses: `h_serial` + `h_symm`
- [ ] Create `Cslib/Logics/Modal/Metalogic/DBCompleteness.lean`:
  - Truth lemma: `truth_lemma_d` (DB has D but not T)
  - Canonical frame properties: `canonical_serial` + `canonical_symm`
  - Completeness: `db_completeness`
- [ ] Verify: `lake build Cslib.Logics.Modal.Metalogic.DBCompleteness`

**Timing**: 1 hour

**Depends on**: 1

**Files to create**:
- `Cslib/Logics/Modal/Metalogic/DBSoundness.lean`
- `Cslib/Logics/Modal/Metalogic/DBCompleteness.lean`

**Verification**:
- Both files compile without `sorry`

---

### Phase 12: Integration and Final Verification [NOT STARTED]

**Goal**: Update the module aggregator, verify the full build, and ensure all 15 modal logics are complete.

**Tasks**:
- [ ] Update `Cslib/Logics/Modal/Metalogic.lean` to import all 20 new files:
  ```
  public import Cslib.Logics.Modal.Metalogic.BSoundness
  public import Cslib.Logics.Modal.Metalogic.BCompleteness
  public import Cslib.Logics.Modal.Metalogic.K4Soundness
  public import Cslib.Logics.Modal.Metalogic.K4Completeness
  public import Cslib.Logics.Modal.Metalogic.K5Soundness
  public import Cslib.Logics.Modal.Metalogic.K5Completeness
  public import Cslib.Logics.Modal.Metalogic.K45Soundness
  public import Cslib.Logics.Modal.Metalogic.K45Completeness
  public import Cslib.Logics.Modal.Metalogic.D4Soundness
  public import Cslib.Logics.Modal.Metalogic.D4Completeness
  public import Cslib.Logics.Modal.Metalogic.D5Soundness
  public import Cslib.Logics.Modal.Metalogic.D5Completeness
  public import Cslib.Logics.Modal.Metalogic.D45Soundness
  public import Cslib.Logics.Modal.Metalogic.D45Completeness
  public import Cslib.Logics.Modal.Metalogic.DBSoundness
  public import Cslib.Logics.Modal.Metalogic.DBCompleteness
  public import Cslib.Logics.Modal.Metalogic.TBSoundness
  public import Cslib.Logics.Modal.Metalogic.TBCompleteness
  public import Cslib.Logics.Modal.Metalogic.KB5Soundness
  public import Cslib.Logics.Modal.Metalogic.KB5Completeness
  ```
- [ ] Update module docstring to list all 15 modal systems
- [ ] Run `lake build Cslib.Logics.Modal.Metalogic` (full module build)
- [ ] Run `lake build` (full project build) to verify no regressions
- [ ] Verify with `lean_verify` that no `sorry` or axioms are used in any of the new theorems

**Timing**: 1.5 hours

**Depends on**: 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic.lean` -- add 20 new imports + update docstring

**Verification**:
- `lake build` succeeds with no errors
- All 10 soundness theorems and 10 completeness theorems exist without `sorry`
- Module aggregator imports are complete

## Testing & Validation

- [ ] `lake build Cslib.Logics.Modal.Metalogic` passes
- [ ] `lake build` (full project) passes with no regressions
- [ ] Each of the 10 `*_axiom_sound` theorems compiles without `sorry`
- [ ] Each of the 10 `*_soundness_derivable` theorems compiles without `sorry`
- [ ] Each of the 10 `*_completeness` theorems compiles without `sorry`
- [ ] `canonical_symm` compiles without `sorry`
- [ ] `canonical_eucl_from_5` compiles without `sorry`
- [ ] All 10 bundled class instances resolve correctly (check with `#check ModalBHilbert Modal.HilbertB`)

## Artifacts & Outputs

- `Cslib/Foundations/Logic/ProofSystem.lean` -- modified (10 tag types + 10 bundled classes)
- `Cslib/Logics/Modal/ProofSystem/Instances.lean` -- modified (10 axiom predicates + instances)
- `Cslib/Logics/Modal/Metalogic/Completeness.lean` -- modified (`canonical_symm` + `canonical_eucl_from_5`)
- `Cslib/Logics/Modal/Metalogic/MCS.lean` -- possibly modified (`mcs_five_eucl` helper)
- 20 new files in `Cslib/Logics/Modal/Metalogic/`:
  - `BSoundness.lean`, `BCompleteness.lean`
  - `K4Soundness.lean`, `K4Completeness.lean`
  - `K5Soundness.lean`, `K5Completeness.lean`
  - `K45Soundness.lean`, `K45Completeness.lean`
  - `D4Soundness.lean`, `D4Completeness.lean`
  - `D5Soundness.lean`, `D5Completeness.lean`
  - `D45Soundness.lean`, `D45Completeness.lean`
  - `DBSoundness.lean`, `DBCompleteness.lean`
  - `TBSoundness.lean`, `TBCompleteness.lean`
  - `KB5Soundness.lean`, `KB5Completeness.lean`
- `Cslib/Logics/Modal/Metalogic.lean` -- modified (20 new imports)

## Rollback/Contingency

All changes are additive (new files + appended content to existing files). No existing definitions are modified.

- **If `canonical_symm` fails**: Fall back to proving symmetry from B+T (reflexivity + B implies symmetry in the classical setting). This narrows B completeness to require axiom T, making it equivalent to TB. Mark B-only as [BLOCKED] and proceed with TB, D4, D5, D45, K4, K5, K45.
- **If `canonical_eucl_from_5` fails**: Fall back to the existing `canonical_eucl` (from T+4+B) for S5-contained logics. Mark K5, D5, K45, D45, KB5 as [BLOCKED] and proceed with B, K4, TB, D4, DB (5 systems that do not need axiom 5 alone).
- **If both fail**: The remaining logics B, K4, D4, TB, DB (5 systems) can still proceed using only existing canonical lemmas (`canonical_refl`, `canonical_trans`, `canonical_serial`). This gives 5 of 10 logics with no new mathematical content required.
- **Partial completion**: Each soundness/completeness pair is independently useful and can be committed separately.
