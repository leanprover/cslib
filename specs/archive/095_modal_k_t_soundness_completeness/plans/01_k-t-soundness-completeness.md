# Implementation Plan: Task #95

- **Task**: 95 - Establish soundness and completeness for modal logics K and T
- **Status**: [NOT STARTED]
- **Effort**: 5 hours
- **Dependencies**: Task 93 (modal S5 preservation + Instances.lean) -- completed
- **Research Inputs**: specs/095_modal_k_t_soundness_completeness/reports/01_k-t-soundness-completeness.md
- **Artifacts**: plans/01_k-t-soundness-completeness.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: true

## Overview

Implement sorry-free soundness and completeness theorems for modal logics K and T, following the standard canonical model construction from the literature (Hebert 2020, Platzer 2010, Sergot 2008). The existing parameterized infrastructure from tasks 92-93 (CanonicalWorld, CanonicalModel, truth_lemma, mcs_box_witness, derive_box_from_box_context) handles T completeness with minimal adaptation. K completeness requires a new K-specific box witness that avoids the axiom T dependency in `derive_box_from_inconsistency`. Four new Lean files are created in flat naming convention to avoid module hierarchy conflicts with existing Soundness.lean and Completeness.lean.

### Research Integration

The research report (01_k-t-soundness-completeness.md) identified:
- All existing infrastructure is parameterized over `Axioms` -- fully reusable for both K and T
- KAxiom (5 constructors) and TAxiom (6 constructors) already exist in Instances.lean
- The parameterized `soundness` theorem accepts a generic `h_ax_sound` callback
- The existing `mcs_box_witness` and `truth_lemma` take explicit `h_T` -- usable for T but not K
- The `derive_box_from_inconsistency` else-branch (lines 349-354 of MCS.lean) uses `mcs_box_closure` with `h_T` to show all elements of L are in S -- this is the ONLY h_T dependency that K must avoid
- K-specific fix: when all L elements have box-versions in S, derive `box phi` via `derive_box_from_box_context` using EFQ to get `L |- phi` from `L |- bot`, then box-lift

The literature proof structure reference (references/literature-proof-structure.md) documents the exact step ordering that all four files must follow.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md found.

## Goals & Non-Goals

**Goals**:
- Prove K soundness: every KAxiom is valid on all frames (no frame conditions)
- Prove K completeness: if phi is valid on all frames then phi is K-derivable
- Prove T soundness: every TAxiom is valid on reflexive frames
- Prove T completeness: if phi is valid on all reflexive frames then phi is T-derivable
- Zero sorry occurrences across all four files
- Flat file naming (KSoundness.lean, etc.) to avoid Lean module conflicts

**Non-Goals**:
- Modifying existing Soundness.lean or Completeness.lean (S5 files remain unchanged)
- Modifying MCS.lean (K-specific helpers are defined locally in KCompleteness.lean)
- D or S4 soundness/completeness (tasks 96-97)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| K box witness else-branch encoding | H | M | Follow EFQ + derive_box_from_box_context pattern from research; the mathematical argument is standard and well-analyzed |
| truth_lemma recursive calls require careful parameter threading | M | L | K truth_lemma follows identical structure to existing S5 truth_lemma, substituting k_mcs_box_witness for mcs_box_witness |
| Module hierarchy conflict with existing Soundness/Completeness files | H | L | Flat naming (KSoundness.lean) confirmed to avoid conflicts per research analysis |
| Lean universe polymorphism in completeness theorem quantifiers | M | L | Follow exact pattern from existing S5 completeness (universe u annotation) |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2 | -- |
| 2 | 3, 4 | 1, 2 respectively |
| 3 | 5 | 3, 4 |

Phases within the same wave can execute in parallel.

---

### Phase 1: K Soundness [NOT STARTED]

**Goal**: Prove every KAxiom is valid on arbitrary frames (no frame conditions needed).

**Tasks**:
- [ ] Create `Cslib/Logics/Modal/Metalogic/KSoundness.lean` with copyright header, module declaration, and imports
- [ ] Define `k_axiom_sound`: case split on `h_ax : KAxiom phi`, prove each constructor valid on all frames
  - `implyK`: `intro h_phi _; exact h_phi`
  - `implyS`: `intro h1 h2 h3; exact h1 h3 (h2 h3)`
  - `efq`: `intro h; exact absurd h id`
  - `peirce`: `intro h; by_contra h_not; exact h_not (h (fun h_phi => absurd h_phi h_not))`
  - `modalK`: `intro h_box_imp h_box_phi w' hr; exact h_box_imp w' hr (h_box_phi w' hr)`
- [ ] Define `k_soundness`: instantiate parameterized `soundness` with `k_axiom_sound`
- [ ] Define `k_soundness_derivable`: instantiate parameterized `soundness_derivable` with `k_axiom_sound`
- [ ] Verify with `lake build Cslib.Logics.Modal.Metalogic.KSoundness`

**Timing**: 0.75 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/KSoundness.lean` -- NEW, ~80 lines

**Verification**:
- File compiles with zero errors and zero sorries
- `k_axiom_sound`, `k_soundness`, `k_soundness_derivable` all type-check

---

### Phase 2: T Soundness [NOT STARTED]

**Goal**: Prove every TAxiom is valid on reflexive frames.

**Tasks**:
- [ ] Create `Cslib/Logics/Modal/Metalogic/TSoundness.lean` with copyright header, module declaration, and imports
- [ ] Define `t_axiom_sound`: case split on `h_ax : TAxiom phi`, prove each constructor
  - Propositional cases (implyK, implyS, efq, peirce): identical to K
  - `modalK`: identical to K
  - `modalT`: `intro h_box; exact h_box w (h_refl w)` (uses reflexivity hypothesis)
- [ ] Define `t_soundness`: instantiate parameterized `soundness` with `t_axiom_sound`
- [ ] Define `t_soundness_derivable`: instantiate parameterized `soundness_derivable` with `t_axiom_sound`
- [ ] Verify with `lake build Cslib.Logics.Modal.Metalogic.TSoundness`

**Timing**: 0.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/TSoundness.lean` -- NEW, ~60 lines

**Verification**:
- File compiles with zero errors and zero sorries
- `t_axiom_sound`, `t_soundness`, `t_soundness_derivable` all type-check

---

### Phase 3: K Completeness [NOT STARTED]

**Goal**: Prove K completeness via canonical model with a K-specific box witness that avoids axiom T.

This is the most complex phase. The existing `derive_box_from_inconsistency` and `mcs_box_witness` both take `h_T`, which K does not have. This phase creates K-specific versions.

**Tasks**:
- [ ] Create `Cslib/Logics/Modal/Metalogic/KCompleteness.lean` with copyright header, module declaration, imports (MCS, Soundness, Completeness for CanonicalWorld/CanonicalModel)
- [ ] Define `k_derive_box_from_inconsistency` -- K-specific version of `derive_box_from_inconsistency` (NO `h_T` parameter)
  - The `neg phi in L` branch is IDENTICAL to the existing version (does not use h_T)
  - The `neg phi not in L` branch (the KEY change): all elements of L have box-versions in S; from `d_bot : L |- bot`, use EFQ axiom to build `L |- phi` (via `bot -> phi` then MP), then use `derive_box_from_box_context` to get `box phi in S`, contradicting `h_not_box`
- [ ] Define `k_mcs_box_witness` -- K-specific box witness using `k_derive_box_from_inconsistency`
  - Same structure as existing `mcs_box_witness` but calls K version of inconsistency helper
  - Signature: takes `h_implyK h_implyS h_efq h_peirce h_K` (NO `h_T`)
  - Returns: `exists T, MCS T /\ (forall psi, box psi in S -> psi in T) /\ phi not in T`
- [ ] Define `k_truth_lemma` -- K-specific truth lemma
  - Same structure as existing `truth_lemma` in Completeness.lean
  - All cases identical except `.box phi` case which calls `k_mcs_box_witness` instead of `mcs_box_witness`
  - Signature: takes `h_implyK h_implyS h_efq h_peirce h_K` (NO `h_T`)
- [ ] Define `k_completeness` -- K completeness theorem
  - Statement: `(forall World m w, Satisfies m w phi) -> Derivable KAxiom phi`
  - Proof structure: contrapositive, `{neg phi}` is K-consistent, extend to MCS by Lindenbaum, canonical model has no frame conditions needed, truth lemma gives `M, w |= neg phi`, but phi is valid on all frames (including canonical model) giving `M, w |= phi`, contradiction
  - Follow EXACT pattern of existing S5 `completeness` in Completeness.lean (lines 250-323)
- [ ] Verify with `lake build Cslib.Logics.Modal.Metalogic.KCompleteness`

**Timing**: 2 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/KCompleteness.lean` -- NEW, ~250 lines

**Verification**:
- File compiles with zero errors and zero sorries
- `k_derive_box_from_inconsistency`, `k_mcs_box_witness`, `k_truth_lemma`, `k_completeness` all type-check
- `lean_verify` confirms no sorry or axiom usage

---

### Phase 4: T Completeness [NOT STARTED]

**Goal**: Prove T completeness via canonical model with reflexive frame, reusing existing parameterized infrastructure.

**Tasks**:
- [ ] Create `Cslib/Logics/Modal/Metalogic/TCompleteness.lean` with copyright header, module declaration, imports
- [ ] Define `t_canonical_refl` -- instantiate existing `canonical_refl` at TAxiom
  - `canonical_refl (fun phi psi => .implyK phi psi) (fun phi psi chi => .implyS phi psi chi) (fun phi => .modalT phi)`
- [ ] Define `t_truth_lemma` -- instantiate existing `truth_lemma` at TAxiom
  - Pass all six axiom hypotheses from TAxiom constructors
  - The existing truth_lemma takes h_T, which TAxiom.modalT provides
- [ ] Define `t_completeness` -- T completeness theorem
  - Statement: `(forall World m, (forall w, m.r w w) -> forall w, Satisfies m w phi) -> Derivable TAxiom phi`
  - Proof structure: contrapositive, `{neg phi}` is T-consistent, extend to MCS by Lindenbaum, canonical model is reflexive (by t_canonical_refl), truth lemma gives `M, w |= neg phi`, but phi is valid on reflexive frames and canonical model is reflexive giving `M, w |= phi`, contradiction
  - Simpler than S5 completeness: only reflexivity needed, no transitivity or Euclideanness
- [ ] Verify with `lake build Cslib.Logics.Modal.Metalogic.TCompleteness`

**Timing**: 1 hour

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/TCompleteness.lean` -- NEW, ~150 lines

**Verification**:
- File compiles with zero errors and zero sorries
- `t_canonical_refl`, `t_truth_lemma`, `t_completeness` all type-check

---

### Phase 5: Module Integration and Final Verification [NOT STARTED]

**Goal**: Wire all four new files into the module graph and verify the entire project builds.

**Tasks**:
- [ ] Add imports to `Cslib/Logics/Modal/Metalogic.lean` aggregator:
  - `public import Cslib.Logics.Modal.Metalogic.KSoundness`
  - `public import Cslib.Logics.Modal.Metalogic.TSoundness`
  - `public import Cslib.Logics.Modal.Metalogic.KCompleteness`
  - `public import Cslib.Logics.Modal.Metalogic.TCompleteness`
- [ ] Add imports to `Cslib.lean` root file (after existing Modal Metalogic entries):
  - `public import Cslib.Logics.Modal.Metalogic.KSoundness`
  - `public import Cslib.Logics.Modal.Metalogic.KCompleteness`
  - `public import Cslib.Logics.Modal.Metalogic.TSoundness`
  - `public import Cslib.Logics.Modal.Metalogic.TCompleteness`
- [ ] Run `lake build` (full project) to verify zero regressions
- [ ] Run `grep -r sorry Cslib/Logics/Modal/Metalogic/KSoundness.lean Cslib/Logics/Modal/Metalogic/TSoundness.lean Cslib/Logics/Modal/Metalogic/KCompleteness.lean Cslib/Logics/Modal/Metalogic/TCompleteness.lean` to confirm zero sorries
- [ ] Verify existing S5 Soundness.lean and Completeness.lean still compile unchanged

**Timing**: 0.75 hours

**Depends on**: 3, 4

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic.lean` -- add 4 new imports
- `Cslib.lean` -- add 4 new imports (after line 291)

**Verification**:
- Full `lake build` passes with zero errors
- No regressions in existing modal metalogic files
- `grep -r sorry` across all four new files returns empty

---

## Testing & Validation

- [ ] Each new file compiles individually via `lake build Cslib.Logics.Modal.Metalogic.{K,T}{Soundness,Completeness}`
- [ ] Full project build (`lake build`) passes with zero errors
- [ ] Zero `sorry` across all four new files (grep verification)
- [ ] `lean_verify` on key theorems confirms no axiom usage beyond `propext`, `Classical.choice`, `Quot.sound`
- [ ] Existing S5 soundness and completeness unaffected (no imports or definitions changed)

## Artifacts & Outputs

- `Cslib/Logics/Modal/Metalogic/KSoundness.lean` -- K soundness (~80 lines)
- `Cslib/Logics/Modal/Metalogic/TSoundness.lean` -- T soundness (~60 lines)
- `Cslib/Logics/Modal/Metalogic/KCompleteness.lean` -- K completeness (~250 lines)
- `Cslib/Logics/Modal/Metalogic/TCompleteness.lean` -- T completeness (~150 lines)
- `Cslib/Logics/Modal/Metalogic.lean` -- updated aggregator
- `Cslib.lean` -- updated root imports

## Rollback/Contingency

All changes are additive: 4 new files + 8 new import lines. To revert:
1. Delete the four new `.lean` files
2. Remove the added import lines from `Metalogic.lean` and `Cslib.lean`
3. No existing files are modified in content

If K box witness proves difficult to encode, the phase can be marked [PARTIAL] and the three other files (KSoundness, TSoundness, TCompleteness) can still be completed independently. The K completeness file is the only one with medium risk.
