# Research Report: Modal K4 Soundness and Completeness

**Task**: 102 -- Modal K4 Soundness and Completeness
**Date**: 2026-06-10
**Literature**: Blackburn, de Rijke, Venema, "Modal Logic" (2002), Chapter 4

---

## 1. Executive Summary

K4 = K + axiom 4 is the normal modal logic over transitive frames. Soundness and completeness proofs follow directly from existing infrastructure with minimal new code. The key insight is that K4 lacks axiom T, so completeness must use `k_truth_lemma` (from `KCompleteness.lean`) rather than `truth_lemma` (from `Completeness.lean`), combined with `canonical_trans` (from `Completeness.lean`) for transitivity of the canonical frame.

**Estimated implementation effort**: Low. Both files are close copies of existing patterns.

---

## 2. Literature Proof Structure

### Source
Blackburn, de Rijke, Venema, "Modal Logic" (2002):
- **Theorem 4.27** (K4 completeness / transitivity is canonical)
- **Table 4.1** (K4 is complete w.r.t. transitive frames)
- **Definition 4.9** (Soundness criterion)

### Strategy
- **Soundness**: Verify each K4 axiom is valid on transitive frames (direct semantic argument)
- **Completeness**: Completeness-via-canonicity. Show canonical frame of K4 is transitive (Theorem 4.27), then apply canonical model theorem (Theorem 4.22)

### Step Map

1. **Define K4Axiom predicate** -- 6 constructors (4 propositional + modalK + modalFour)
2. **Soundness: k4_axiom_sound** -- Case-split on K4Axiom; modalFour uses transitivity hypothesis
3. **Soundness wrappers** -- k4_soundness, k4_soundness_derivable via parametric `soundness`
4. **Completeness: k4_completeness** -- Contrapositive: assume not derivable, build canonical model, show it is transitive via `canonical_trans`, apply `k_truth_lemma`, derive contradiction

### Dependencies
- Step 2 depends on Step 1
- Step 3 depends on Step 2
- Step 4 depends on Step 1 (K4Axiom defined), and uses existing `k_truth_lemma` + `canonical_trans`

### Potential Formalization Challenges
- **None significant**: All required infrastructure exists. The proof is mechanical adaptation of existing patterns.

---

## 3. K4Axiom Predicate Design

### Current State

K4Axiom does **not** exist yet. Task 100 (shared infrastructure) is supposed to add it to `Instances.lean`, but task 100 is `[NOT STARTED]`.

### Recommended Approach

Define `K4Axiom` directly in `Instances.lean` as part of this task (or define it locally in the soundness/completeness files). The predicate has 6 constructors:

```lean
inductive K4Axiom : Proposition Atom -> Prop where
  | implyK (phi psi) : K4Axiom (phi.imp (psi.imp phi))
  | implyS (phi psi chi) : K4Axiom ((phi.imp (psi.imp chi)).imp ((phi.imp psi).imp (phi.imp chi)))
  | efq (phi) : K4Axiom (Proposition.bot.imp phi)
  | peirce (phi psi) : K4Axiom (((phi.imp psi).imp phi).imp phi)
  | modalK (phi psi) : K4Axiom ((Proposition.box (phi.imp psi)).imp ((Proposition.box phi).imp (Proposition.box psi)))
  | modalFour (phi) : K4Axiom ((Proposition.box phi).imp (Proposition.box (Proposition.box phi)))
```

**Comparison with other axiom predicates**:
| System | Constructors | Difference from K |
|--------|-------------|-------------------|
| KAxiom | 5 (propositional + modalK) | baseline |
| TAxiom | 6 (+ modalT) | + reflexivity |
| DAxiom | 6 (+ modalD) | + seriality |
| **K4Axiom** | **6 (+ modalFour)** | **+ transitivity** |
| S4Axiom | 7 (+ modalT + modalFour) | + reflexivity + transitivity |

### Tag Type and Bundled Class

Also needed (part of task 100 infrastructure):
```lean
opaque Modal.HilbertK4 : Type := Empty

class ModalK4Hilbert (S : Type*) ... extends ModalHilbert S, HasAxiom4 S
```

Plus instance registrations for `HilbertK4` binding `K4Axiom` to `DerivationTree`.

**Decision**: Since task 100 is not started, the implementation plan for task 102 should either:
- (A) Include adding K4Axiom + HilbertK4 + instances as a preliminary phase, OR
- (B) Depend on task 100 being completed first

Recommendation: Option (A) -- add K4-specific infrastructure inline, since it is minimal (one inductive type, one tag type, one class, ~15 instance registrations). The planner should decide.

---

## 4. Soundness Strategy (K4Soundness.lean)

### Pattern: Follow S4Soundness.lean

The file structure mirrors `S4Soundness.lean` exactly, with the reflexivity constraint removed.

### Key theorem: k4_axiom_sound

```
theorem k4_axiom_sound {World : Type*} {phi : Proposition Atom}
    (h_ax : K4Axiom phi) (m : Model World Atom)
    (h_trans : forall w1 w2 w3, m.r w1 w2 -> m.r w2 w3 -> m.r w1 w3)
    (w : World) : Satisfies m w phi
```

**Case analysis** (6 cases):
- `implyK`, `implyS`, `efq`, `peirce`, `modalK`: Identical to KSoundness/S4Soundness (valid on all frames)
- `modalFour`: Identical to S4Soundness.lean line 77-78:
  ```lean
  | modalFour phi =>
    intro h_box w1 hr1 w2 hr2
    exact h_box w2 (h_trans w w1 w2 hr1 hr2)
  ```

### Wrapper theorems

- `k4_soundness`: Uses parametric `soundness` with `k4_axiom_sound`
- `k4_soundness_derivable`: Uses parametric `soundness_derivable` with `k4_axiom_sound`

Both take `h_trans` but NOT `h_refl`.

### Imports needed
```lean
public import Cslib.Logics.Modal.Metalogic.Soundness
public import Cslib.Logics.Modal.ProofSystem.Instances  -- for K4Axiom
```

---

## 5. Completeness Strategy (K4Completeness.lean)

### Pattern: Hybrid of KCompleteness.lean + S4Completeness.lean

The critical insight from BRV Theorem 4.27: K4 has axiom 4 but NOT axiom T. Therefore:
- **Cannot** use `truth_lemma` (from `Completeness.lean`) because it requires `h_T`
- **Must** use `k_truth_lemma` (from `KCompleteness.lean`) which uses `k_mcs_box_witness` instead of `mcs_box_witness`
- **Can** use `canonical_trans` (from `Completeness.lean`) because it only requires `h_4`

### Key theorem: k4_completeness

```
theorem k4_completeness (phi : Proposition Atom)
    (h_valid : forall (World : Type u) (m : Model World Atom),
      (forall w1 w2 w3, m.r w1 w2 -> m.r w2 w3 -> m.r w1 w3) ->
      forall w, Satisfies m w phi) :
    Derivable (@K4Axiom Atom) phi
```

### Proof Architecture (BRV Theorem 4.27)

1. **Contrapositive**: Assume `phi` is not K4-derivable
2. **Consistency**: Show `{neg phi}` is K4-consistent (standard DNE argument via Peirce + EFQ)
3. **Lindenbaum**: Extend to K4-MCS `M` containing `neg phi`
4. **Canonical world**: `w = (M, hM_mcs) : CanonicalWorld K4Axiom`
5. **Truth lemma**: Apply `k_truth_lemma` (NOT `truth_lemma`) instantiated at K4Axiom constructors
6. **Frame property**: Apply `canonical_trans` (from Completeness.lean) instantiated at `.modalFour`
7. **Contradiction**: `phi in M` (from truth lemma + validity) and `neg phi in M` (from step 3) contradict MCS consistency

### Instantiation Details

The `k_truth_lemma` call:
```lean
k_truth_lemma
  (fun phi psi => .implyK phi psi)        -- h_implyK
  (fun phi psi chi => .implyS phi psi chi) -- h_implyS
  (fun phi => .efq phi)                    -- h_efq
  (fun phi psi => .peirce phi psi)         -- h_peirce
  (fun phi psi => .modalK phi psi)         -- h_K
  w phi
```

The `canonical_trans` call:
```lean
canonical_trans
  (fun phi psi => .implyK phi psi)
  (fun phi psi chi => .implyS phi psi chi)
  (fun phi => .modalFour phi)              -- h_4 from K4Axiom
```

### Validity hypothesis instantiation:
```lean
h_valid (CanonicalWorld (@K4Axiom Atom))
  (CanonicalModel (@K4Axiom Atom))
  (canonical_trans ...)  -- transitive canonical frame
  w
```

### Imports needed
```lean
public import Cslib.Logics.Modal.Metalogic.KCompleteness  -- for k_truth_lemma
public import Cslib.Logics.Modal.Metalogic.Completeness    -- for canonical_trans
public import Cslib.Logics.Modal.ProofSystem.Instances      -- for K4Axiom
```

Note: `KCompleteness.lean` already imports `MCS.lean`, `Soundness.lean`, and `Completeness.lean`.

---

## 6. Existing Infrastructure Verification

### Verified Available (no modifications needed)

| Component | Location | Used For |
|-----------|----------|----------|
| `Satisfies.four` | `Basic.lean:301` | Semantic validity reference (not directly called in Hilbert proof) |
| `k_truth_lemma` | `KCompleteness.lean:168` | K4 completeness (box case without axiom T) |
| `k_mcs_box_witness` | `KCompleteness.lean:132` | Used internally by k_truth_lemma |
| `k_derive_box_from_inconsistency` | `KCompleteness.lean:51` | Used internally by k_mcs_box_witness |
| `canonical_trans` | `Completeness.lean:78` | K4 canonical frame transitivity |
| `mcs_box_box` | `MCS.lean:151` | Used internally by canonical_trans |
| `soundness` | `Soundness.lean:85` | Parametric soundness theorem |
| `soundness_derivable` | `Soundness.lean:110` | Parametric derivable soundness |
| `modal_lindenbaum` | `MCS.lean:59` | Lindenbaum's Lemma |
| `mcs_not_mem_of_neg` | `MCS.lean:206` | Contradiction: phi and neg phi in MCS |
| `deductionTheorem` | `DeductionTheorem.lean` | Used in consistency proof |

### NOT Available (needs creation)

| Component | Location | Notes |
|-----------|----------|-------|
| `K4Axiom` | `Instances.lean` | Inductive type, 6 constructors |
| `Modal.HilbertK4` | `ProofSystem.lean` | Opaque tag type |
| `ModalK4Hilbert` | `ProofSystem.lean` | Bundled class |
| Instance registrations | `Instances.lean` | ~15 instances for HilbertK4 |

---

## 7. File Structure

### K4Soundness.lean (~50 lines)

```
module
public import Cslib.Logics.Modal.Metalogic.Soundness
public import Cslib.Logics.Modal.ProofSystem.Instances

-- k4_axiom_sound (6 cases, transitivity-only frame condition)
-- k4_soundness (wrapper)
-- k4_soundness_derivable (wrapper)
```

### K4Completeness.lean (~120 lines)

```
module
public import Cslib.Logics.Modal.Metalogic.KCompleteness
public import Cslib.Logics.Modal.Metalogic.Completeness
public import Cslib.Logics.Modal.ProofSystem.Instances

-- k4_completeness (contrapositive + k_truth_lemma + canonical_trans)
```

### Metalogic.lean (add imports)

Add:
```lean
public import Cslib.Logics.Modal.Metalogic.K4Soundness
public import Cslib.Logics.Modal.Metalogic.K4Completeness
```

---

## 8. Comparison with Related Systems

| Aspect | K | T | D | **K4** | S4 |
|--------|---|---|---|--------|-----|
| Axioms beyond K | none | T | D | **4** | T+4 |
| Frame class | all | reflexive | serial | **transitive** | refl+trans |
| Truth lemma | k_truth_lemma | truth_lemma | truth_lemma_d | **k_truth_lemma** | truth_lemma |
| Box witness | k_mcs_box_witness | mcs_box_witness | mcs_box_witness_d | **k_mcs_box_witness** | mcs_box_witness |
| Frame property | none | canonical_refl | canonical_serial | **canonical_trans** | canonical_refl + canonical_trans |
| Soundness conditions | none | h_refl | h_serial | **h_trans** | h_refl + h_trans |

Key observation: **K4 reuses the K truth lemma exactly**, because both lack axiom T. The only addition over K is `canonical_trans` for the frame property argument.

---

## 9. Risk Assessment

### No Blockers Identified

All required infrastructure exists. The implementation is mechanical:
- Soundness: direct case-split (copy of S4 minus reflexivity)
- Completeness: combine existing k_truth_lemma + canonical_trans (both already proven)

### Dependency on Task 100

Task 100 should define K4Axiom, HilbertK4, and instances. If task 100 is not completed first, these can be added as part of task 102's implementation (adds ~40 lines to Instances.lean and ~5 lines to ProofSystem.lean). The planner should decide whether to include this or mark it as a prerequisite.

### Consistency proof boilerplate

The `h_cons` (consistency of `{neg phi}`) proof in the completeness theorem is ~25 lines of boilerplate, identical across K, T, D, S4, and S5 (modulo axiom constructor names). This is copied verbatim with only the axiom constructor names changed from `.implyK`/etc. to `K4Axiom` constructors.

---

## 10. Recommendations for Implementation Plan

1. **Phase 0 (if task 100 not done)**: Add K4Axiom to Instances.lean, HilbertK4 to ProofSystem.lean, register instances
2. **Phase 1**: Create K4Soundness.lean following S4Soundness.lean pattern (remove h_refl, keep h_trans)
3. **Phase 2**: Create K4Completeness.lean using k_truth_lemma + canonical_trans
4. **Phase 3**: Add imports to Metalogic.lean, verify with `lake build`
5. **Verification**: `lake build Cslib.Logics.Modal.Metalogic.K4Soundness` and `lake build Cslib.Logics.Modal.Metalogic.K4Completeness`
