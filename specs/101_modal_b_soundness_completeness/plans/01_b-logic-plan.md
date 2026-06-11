# Implementation Plan: Task #101

- **Task**: 101 - Modal B Soundness and Completeness
- **Status**: [NOT STARTED]
- **Effort**: 2 hours
- **Dependencies**: Task 100 (modal_cube_shared_infrastructure) for BAxiom, HilbertB, canonical_symm
- **Research Inputs**: specs/101_modal_b_soundness_completeness/reports/01_b-logic-research.md
- **Artifacts**: plans/01_b-logic-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: true

## Overview

Prove soundness and completeness for modal logic B (K + axiom B) over symmetric Kripke frames. This involves creating two new files: BSoundness.lean following the KSoundness/DSoundness pattern with an additional `modalB` case using symmetry, and BCompleteness.lean following the KCompleteness pattern (using `k_truth_lemma`, NOT `truth_lemma`) with `canonical_symm` from task 100 for the frame property.

### Research Integration

Key findings from the research report:
- **Critical design decision**: B lacks axiom T, so completeness MUST use `k_truth_lemma` (from KCompleteness.lean), not `truth_lemma` (from Completeness.lean which requires axiom T).
- **No new truth lemma needed**: Unlike D completeness (which needed `truth_lemma_d`), B completeness directly reuses `k_truth_lemma` since the K box witness machinery (EFQ + `derive_box_from_box_context`) works for any system with K, EFQ, and Peirce.
- **Soundness modalB case**: 3-line proof -- `intro hphi w' hr h_box_neg; exact h_box_neg w (h_symm w w' hr) hphi`. Uses explicit symmetry hypothesis, not `Std.Symm` typeclass.
- **Completeness structure**: Contrapositive via BRV Proposition 4.12 + Theorem 4.28 clause 2. Consistency argument is boilerplate from k_completeness. The novelty is instantiating `canonical_symm` and connecting it to `h_valid`.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md found.

## Goals & Non-Goals

**Goals**:
- Create `Cslib/Logics/Modal/Metalogic/BSoundness.lean` with `b_axiom_sound`, `b_soundness`, `b_soundness_derivable`
- Create `Cslib/Logics/Modal/Metalogic/BCompleteness.lean` with `b_completeness`
- Both files compile without `sorry` and build cleanly with `lake build`

**Non-Goals**:
- Modifying Instances.lean or ProofSystem.lean (task 100 scope)
- Creating new truth lemmas or box witnesses (reuse from KCompleteness.lean)
- Proving canonical_symm (task 100 scope)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Task 100 not yet complete (BAxiom, canonical_symm unavailable) | H | H | Write code assuming task 100 API. Files will compile once task 100 lands. Verify against expected signatures from research report. |
| canonical_symm signature mismatch | M | L | Research report analyzed existing patterns (canonical_refl, canonical_trans, canonical_eucl) and predicted signature. Low risk since pattern is well-established. |
| diamond unfolding complexity in modalB case | L | L | Research report traced the exact unfolding: `diamond phi = (box(phi.imp bot)).imp bot`, leading to `intro hphi w' hr h_box_neg; exact h_box_neg w (h_symm w w' hr) hphi`. Verified against existing `canonical_eucl` modalB case. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |

Phases within the same wave can execute in parallel.

### Phase 1: BSoundness.lean [COMPLETED]

**Goal**: Create soundness theorem for modal logic B over symmetric frames.

**Tasks**:
- [x] Create `Cslib/Logics/Modal/Metalogic/BSoundness.lean` with module header, imports, and copyright
- [x] Implement `b_axiom_sound`: case analysis on BAxiom constructors
  - Propositional cases (implyK, implyS, efq, peirce): identical to KSoundness
  - modalK case: identical to KSoundness
  - modalB case: `intro hphi w' hr h_box_neg; exact h_box_neg w (h_symm w w' hr) hphi`
- [x] Implement `b_soundness`: wrapper using parameterized `soundness` with `b_axiom_sound`
- [x] Implement `b_soundness_derivable`: wrapper using `soundness_derivable` with `b_axiom_sound`
- [x] Verify with `lake build Cslib.Logics.Modal.Metalogic.BSoundness`

**Timing**: 0.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/BSoundness.lean` - NEW: soundness for B over symmetric frames (~60 lines)

**Verification**:
- File compiles with `lake build Cslib.Logics.Modal.Metalogic.BSoundness` (no errors, no sorry)
- `lean_verify` confirms no axiom usage beyond the expected

**Implementation Details**:

Imports:
```
public import Cslib.Logics.Modal.Metalogic.Soundness
public import Cslib.Logics.Modal.ProofSystem.Instances
```

Symmetry hypothesis style (matching DSoundness pattern with `Relation.Serial`):
```lean
theorem b_axiom_sound {World : Type*} {phi : Proposition Atom}
    (h_ax : BAxiom phi) (m : Model World Atom)
    (h_symm : forall w1 w2, m.r w1 w2 -> m.r w2 w1)
    (w : World) : Satisfies m w phi
```

The `b_soundness` and `b_soundness_derivable` wrappers pass `h_symm` through, following the exact pattern of `d_soundness`/`d_soundness_derivable` with `h_serial`.

---

### Phase 2: BCompleteness.lean [COMPLETED]

**Goal**: Create completeness theorem for modal logic B over symmetric frames.

**Tasks**:
- [x] Create `Cslib/Logics/Modal/Metalogic/BCompleteness.lean` with module header, imports, and copyright
- [x] Implement `b_completeness` theorem:
  - Validity hypothesis: `forall (World : Type u) (m : Model World Atom), (forall w1 w2, m.r w1 w2 -> m.r w2 w1) -> forall w, Satisfies m w phi`
  - Step 1: `by_contra h_not_deriv` + consistency of `{neg phi}` (boilerplate from k_completeness)
  - Step 2: Lindenbaum extension to MCS M
  - Step 3: Instantiate `canonical_symm` at BAxiom constructors (implyK, implyS, modalK, modalB)
  - Step 4: Apply `k_truth_lemma` instantiated at BAxiom constructors (implyK, implyS, efq, peirce, modalK)
  - Step 5: Contradiction via `mcs_not_mem_of_neg`
- [x] Verify with `lake build Cslib.Logics.Modal.Metalogic.BCompleteness`

**Timing**: 1.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/BCompleteness.lean` - NEW: completeness for B over symmetric frames (~80 lines)

**Verification**:
- File compiles with `lake build Cslib.Logics.Modal.Metalogic.BCompleteness` (no errors, no sorry)
- `lean_verify` confirms no axiom usage beyond the expected

**Implementation Details**:

Imports:
```
public import Cslib.Logics.Modal.Metalogic.KCompleteness
public import Cslib.Logics.Modal.Metalogic.Completeness
public import Cslib.Logics.Modal.ProofSystem.Instances
```

Note: Import KCompleteness for `k_truth_lemma`. Import Completeness for `CanonicalModel`, `CanonicalWorld`, `canonical_symm`. Do NOT import BSoundness (soundness and completeness are independent).

The consistency argument (lines ~20-50) is mechanical boilerplate identical to `k_completeness`. The key novelty is the symmetry proof and truth lemma application (lines ~50-80):

```lean
-- Step 3: canonical model is symmetric
have h_symm : forall (S T : CanonicalWorld (@BAxiom Atom)),
    (CanonicalModel (@BAxiom Atom)).r S T ->
    (CanonicalModel (@BAxiom Atom)).r T S :=
  fun S T hST => canonical_symm
    (fun phi psi => .implyK phi psi)
    (fun phi psi chi => .implyS phi psi chi)
    (fun phi => .modalB phi)
    (fun phi psi => .modalK phi psi)
    S T hST

-- Step 4: contradiction via k_truth_lemma + h_valid
exact mcs_not_mem_of_neg
  (fun phi psi => .implyK phi psi)
  (fun phi psi chi => .implyS phi psi chi)
  hM_mcs (hM_sup (Set.mem_singleton _))
  ((k_truth_lemma
    (fun phi psi => .implyK phi psi)
    (fun phi psi chi => .implyS phi psi chi)
    (fun phi => .efq phi)
    (fun phi psi => .peirce phi psi)
    (fun phi psi => .modalK phi psi)
    w phi).mp
    (h_valid (CanonicalWorld (@BAxiom Atom))
      (CanonicalModel (@BAxiom Atom))
      (fun w1 w2 hw => h_symm w1 w2 hw)
      w))
```

The `canonical_symm` instantiation pattern depends on task 100's exact signature. If `canonical_symm` takes `(S T : CanonicalWorld Axioms)` as explicit arguments (like `canonical_trans`), use the pattern above. If it takes them implicitly, adjust accordingly.

---

## Testing & Validation

- [ ] `lake build Cslib.Logics.Modal.Metalogic.BSoundness` compiles without errors
- [ ] `lake build Cslib.Logics.Modal.Metalogic.BCompleteness` compiles without errors
- [ ] No `sorry` in either file
- [ ] `lean_verify` on `b_axiom_sound`, `b_soundness`, `b_soundness_derivable`, `b_completeness` -- all pass
- [ ] Full `lake build` passes (after task 100 is complete)

## Artifacts & Outputs

- `Cslib/Logics/Modal/Metalogic/BSoundness.lean` - Soundness for B over symmetric frames
- `Cslib/Logics/Modal/Metalogic/BCompleteness.lean` - Completeness for B over symmetric frames
- `specs/101_modal_b_soundness_completeness/plans/01_b-logic-plan.md` - This plan
- `specs/101_modal_b_soundness_completeness/summaries/01_b-logic-summary.md` - Implementation summary (created after implementation)

## Rollback/Contingency

If task 100 is not yet complete:
- BSoundness.lean and BCompleteness.lean can be written but will not compile until BAxiom and canonical_symm are available from task 100.
- Mark task [BLOCKED] on task 100 and proceed when unblocked.
- No existing files are modified, so rollback is simply deleting the two new files.

If canonical_symm signature differs from prediction:
- Adjust the instantiation pattern in BCompleteness.lean step 3.
- The proof structure remains the same; only the function call syntax changes.
