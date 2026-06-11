# Research Report: Modal TB Soundness and Completeness

**Task**: 105 -- Prove soundness and completeness for modal logic TB (K + T + B)
**Date**: 2026-06-10
**Literature**: Blackburn, de Rijke, Venema "Modal Logic" (2002), Chapter 4

---

## Literature Proof Structure

**Source**: BRV "Modal Logic", Ch. 4, Theorems 4.22, 4.28, 4.29
**Strategy**: Completeness via canonicity (contrapositive + canonical model)

### Step Map

1. **TB Axiom Predicate** -- Define `TBAxiom` with 7 constructors (4 propositional + K + T + B)
2. **TB Soundness** -- Verify each axiom valid on reflexive + symmetric frames (BRV Def 4.9)
   - Axiom T: `box phi -> phi` uses reflexivity (BRV Thm 4.28 cl.1)
   - Axiom B: `phi -> box(diamond phi)` uses symmetry (BRV Thm 4.28 cl.2)
3. **Canonical Symmetry** -- Prove `canonical_symm`: canonical frame for TB is symmetric (BRV Thm 4.28 cl.2)
4. **TB Completeness** -- If phi valid on all reflexive + symmetric frames, then TB-derivable (BRV Thm 4.29 pattern)
   - Uses `truth_lemma` (T-based, from `Completeness.lean`)
   - Uses `canonical_refl` (from axiom T, existing)
   - Uses `canonical_symm` (from axiom B, new -- task 100 dependency)

### Dependencies

- Step 4 depends on Step 3 (canonical_symm)
- Step 3 depends on Step 1 (TBAxiom must include axiom B)
- Step 4 depends on `truth_lemma` and `canonical_refl` (both existing in Completeness.lean)

---

## 1. TBAxiom Predicate

TB = K + T + B. The axiom predicate has 7 constructors:

```lean
inductive TBAxiom : Proposition Atom -> Prop where
  | implyK (phi psi : Proposition Atom) :
      TBAxiom (phi.imp (psi.imp phi))
  | implyS (phi psi chi : Proposition Atom) :
      TBAxiom ((phi.imp (psi.imp chi)).imp ((phi.imp psi).imp (phi.imp chi)))
  | efq (phi : Proposition Atom) :
      TBAxiom (Proposition.bot.imp phi)
  | peirce (phi psi : Proposition Atom) :
      TBAxiom (((phi.imp psi).imp phi).imp phi)
  | modalK (phi psi : Proposition Atom) :
      TBAxiom ((Proposition.box (phi.imp psi)).imp
        ((Proposition.box phi).imp (Proposition.box psi)))
  | modalT (phi : Proposition Atom) :
      TBAxiom ((Proposition.box phi).imp phi)
  | modalB (phi : Proposition Atom) :
      TBAxiom (phi.imp (Proposition.box (Proposition.diamond phi)))
```

This is identical to `TAxiom` plus `modalB`. It is also `ModalAxiom` minus `modalFour`.

### Location

Define `TBAxiom` in `ProofSystem/Instances.lean` alongside the existing `KAxiom`, `TAxiom`, `DAxiom`, `S4Axiom`. Also need:
- Tag type: `opaque Modal.HilbertTB : Type := Empty` in `ProofSystem.lean`
- Bundled class: `class ModalTBHilbert` extending `ModalTHilbert` + `HasAxiomB` in `ProofSystem.lean`
- All typeclass instances in `Instances.lean`

**IMPORTANT**: These definitions are part of task 100's scope (shared infrastructure). Task 105 depends on them existing. If task 100 is not yet implemented, task 105 must either wait or include these definitions itself.

---

## 2. TB Soundness

### Architecture

Create `TBSoundness.lean` following the pattern of `TSoundness.lean` and `S4Soundness.lean`.

### `tb_axiom_sound`

Proves each of the 7 TB axiom schemata is valid over reflexive + symmetric frames. The proof follows `s4_axiom_sound` but replaces `modalFour` with `modalB`:

```lean
theorem tb_axiom_sound {World : Type*} {phi : Proposition Atom}
    (h_ax : TBAxiom phi) (m : Model World Atom)
    (h_refl : forall w, m.r w w)
    (h_symm : forall w1 w2, m.r w1 w2 -> m.r w2 w1)
    (w : World) : Satisfies m w phi
```

Case analysis on `h_ax`:
- `implyK`, `implyS`, `efq`, `peirce`, `modalK`: Identical to all existing soundness proofs (valid on all frames).
- `modalT phi`: `intro h_box; exact h_box w (h_refl w)` -- uses reflexivity.
- `modalB phi`: The proof for axiom B validity on symmetric frames is:
  ```
  intro h_phi w' hr
  -- Need: Satisfies m w' (diamond phi)
  -- i.e., exists w'', m.r w' w'' /\ Satisfies m w'' phi
  -- By symmetry: m.r w' w
  -- Witness: w with h_phi
  exact diamond_iff.mpr (Exists.intro w (And.intro (h_symm w w' hr) h_phi))
  ```
  This exactly matches the existing `Satisfies.b` proof in `Basic.lean` (line 276-282).

### `tb_soundness` and `tb_soundness_derivable`

Standard wrappers delegating to parameterized `soundness`:

```lean
theorem tb_soundness {World : Type*}
    {Gamma : List (Proposition Atom)} {phi : Proposition Atom}
    (d : DerivationTree (@TBAxiom Atom) Gamma phi)
    (m : Model World Atom)
    (h_refl : forall w, m.r w w)
    (h_symm : forall w1 w2, m.r w1 w2 -> m.r w2 w1)
    (w : World)
    (h_ctx : forall psi in Gamma, Satisfies m w psi) : Satisfies m w phi :=
  soundness d m (fun psi h_ax w => tb_axiom_sound h_ax m h_refl h_symm w) w h_ctx
```

### Imports

```lean
public import Cslib.Logics.Modal.Metalogic.Soundness
public import Cslib.Logics.Modal.ProofSystem.Instances
```

---

## 3. Canonical Symmetry (`canonical_symm`)

### BRV Reference

BRV Theorem 4.28, clause 2: The canonical frame for KB is symmetric.

### Proof Strategy

**Given**: `R S T` (i.e., `forall phi, box phi in S.val -> phi in T.val`)
**Goal**: `R T S` (i.e., `forall phi, box phi in T.val -> phi in S.val`)

Proof by contradiction for each `phi`:
1. Assume `box phi in T` and `phi not in S`.
2. By MCS: `neg phi in S`.
3. By axiom B: `neg phi -> box(diamond(neg phi))`, so `box(diamond(neg phi)) in S`.
4. Since `R S T`: `diamond(neg phi) in T`.
5. `diamond(neg phi) = neg(box(neg(neg phi)))`, so `box(neg(neg phi)) not in T`.
6. But from `box phi in T`, derive `box(neg(neg phi)) in T` using K + propositional tautology `phi -> neg(neg phi)`.
7. Contradiction with step 5.

### Lean Signature

```lean
theorem canonical_symm
    {Axioms : Proposition Atom -> Prop}
    (h_implyK : forall (phi psi : Proposition Atom), Axioms (phi.imp (psi.imp phi)))
    (h_implyS : forall (phi psi chi : Proposition Atom),
      Axioms ((phi.imp (psi.imp chi)).imp ((phi.imp psi).imp (phi.imp chi))))
    (h_B : forall (phi : Proposition Atom),
      Axioms (phi.imp (Proposition.box (Proposition.diamond phi))))
    (h_K : forall (phi psi : Proposition Atom),
      Axioms ((Proposition.box (phi.imp psi)).imp
        ((Proposition.box phi).imp (Proposition.box psi))))
    (S T : CanonicalWorld Axioms) :
    (CanonicalModel Axioms).r S T ->
    (CanonicalModel Axioms).r T S
```

### Key Helper Needed

The proof of step 6 needs to show that `box phi in T -> box(neg(neg phi)) in T`, which requires:
- Derive `phi -> neg(neg phi)` as a propositional tautology
- Use necessitation to get `box(phi -> neg(neg phi))`
- Use axiom K to get `box phi -> box(neg(neg phi))`
- Apply in MCS T to get `box(neg(neg phi)) in T`

This is accomplished by `mcs_box_mp` combined with `modal_closed_under_derivation` (deriving `box(phi -> neg(neg phi))` in T's MCS from empty context).

### Location

This theorem should go in `Completeness.lean` alongside `canonical_refl`, `canonical_trans`, `canonical_eucl`. It is parameterized over `Axioms` and takes explicit `h_B` and `h_K` hypotheses.

**CRITICAL**: This is task 100's deliverable. Task 105 depends on `canonical_symm` existing in `Completeness.lean`.

---

## 4. TB Completeness

### Architecture

Create `TBCompleteness.lean` following the pattern of `S4Completeness.lean` and `TCompleteness.lean`.

### Key Insight: T-based Truth Lemma

TB includes axiom T, so we use the T-based `truth_lemma` (from `Completeness.lean`), NOT `k_truth_lemma`. The T-based `truth_lemma` requires:
- `h_implyK`, `h_implyS`, `h_efq`, `h_peirce` (propositional axioms)
- `h_K` (axiom K)
- `h_T` (axiom T) -- required for `mcs_box_witness`

The `truth_lemma` uses `mcs_box_witness` internally, which needs axiom T. Since `TBAxiom` includes `modalT`, this works directly.

### `tb_truth_lemma`

Thin wrapper instantiating `truth_lemma` at `TBAxiom`:

```lean
theorem tb_truth_lemma
    (S : CanonicalWorld (@TBAxiom Atom))
    (phi : Proposition Atom) :
    (Satisfies (CanonicalModel (@TBAxiom Atom)) S phi <-> phi in S.val) :=
  truth_lemma
    (fun phi psi => .implyK phi psi)
    (fun phi psi chi => .implyS phi psi chi)
    (fun phi => .efq phi)
    (fun phi psi => .peirce phi psi)
    (fun phi psi => .modalK phi psi)
    (fun phi => .modalT phi)
    S phi
```

### `tb_canonical_refl`

Thin wrapper instantiating `canonical_refl` at `TBAxiom`:

```lean
theorem tb_canonical_refl
    (S : CanonicalWorld (@TBAxiom Atom)) :
    (CanonicalModel (@TBAxiom Atom)).r S S :=
  canonical_refl
    (fun phi psi => .implyK phi psi)
    (fun phi psi chi => .implyS phi psi chi)
    (fun phi => .modalT phi)
    S
```

### `tb_canonical_symm`

Thin wrapper instantiating `canonical_symm` at `TBAxiom`:

```lean
theorem tb_canonical_symm
    (S T : CanonicalWorld (@TBAxiom Atom)) :
    (CanonicalModel (@TBAxiom Atom)).r S T ->
    (CanonicalModel (@TBAxiom Atom)).r T S :=
  canonical_symm
    (fun phi psi => .implyK phi psi)
    (fun phi psi chi => .implyS phi psi chi)
    (fun phi => .modalB phi)
    (fun phi psi => .modalK phi psi)
    S T
```

### `tb_completeness`

The main completeness theorem:

```lean
theorem tb_completeness (phi : Proposition Atom)
    (h_valid : forall (World : Type u) (m : Model World Atom),
      (forall w, m.r w w) ->
      (forall w1 w2, m.r w1 w2 -> m.r w2 w1) ->
      forall w, Satisfies m w phi) :
    Derivable (@TBAxiom Atom) phi
```

The proof follows S4Completeness exactly, with two frame properties instead of two:
1. Contrapositive: assume not derivable.
2. `{neg phi}` is TB-consistent (same boilerplate pattern as all other completeness proofs).
3. Lindenbaum extension to MCS M.
4. Canonical world `w = (M, hM_mcs)`.
5. Apply `h_valid` to canonical model with `tb_canonical_refl` and `tb_canonical_symm`.
6. Use `tb_truth_lemma` to convert satisfaction to membership.
7. Contradiction via `mcs_not_mem_of_neg`.

### Imports

```lean
public import Cslib.Logics.Modal.Metalogic.Completeness
public import Cslib.Logics.Modal.ProofSystem.Instances
```

---

## 5. Typeclass Instances (in ProofSystem/Instances.lean)

Following the existing pattern for K, T, D, S4, S5:

```lean
-- Tag type (in ProofSystem.lean)
opaque Modal.HilbertTB : Type := Empty

-- Bundled class (in ProofSystem.lean)
class ModalTBHilbert (S : Type*) [HasBot F] [HasImp F] [HasBox F]
    [InferenceSystem S F]
    extends ModalTHilbert S (F := F),
            HasAxiomB S (F := F)

-- Instance registrations (in Instances.lean)
instance : InferenceSystem Modal.HilbertTB (Modal.Proposition Atom) where
  derivation phi := Modal.DerivationTree (@Modal.TBAxiom Atom) [] phi

instance : ModusPonens Modal.HilbertTB (F := Modal.Proposition Atom) where ...
instance : Necessitation Modal.HilbertTB (F := Modal.Proposition Atom) where ...
instance : HasAxiomImplyK Modal.HilbertTB (F := Modal.Proposition Atom) where ...
instance : HasAxiomImplyS Modal.HilbertTB (F := Modal.Proposition Atom) where ...
instance : HasAxiomEFQ Modal.HilbertTB (F := Modal.Proposition Atom) where ...
instance : HasAxiomPeirce Modal.HilbertTB (F := Modal.Proposition Atom) where ...
instance : HasAxiomK Modal.HilbertTB (F := Modal.Proposition Atom) where ...
instance : HasAxiomT Modal.HilbertTB (F := Modal.Proposition Atom) where ...
instance : HasAxiomB Modal.HilbertTB (F := Modal.Proposition Atom) where ...
instance : ModalHilbert Modal.HilbertTB (F := Modal.Proposition Atom) where
instance : ModalTHilbert Modal.HilbertTB (F := Modal.Proposition Atom) where
instance : ModalTBHilbert Modal.HilbertTB (F := Modal.Proposition Atom) where
```

**IMPORTANT**: `ModalTBHilbert` extends `ModalTHilbert` + `HasAxiomB`. This means TB gets T's reflexivity axiom AND B's symmetry axiom, which is exactly the correct combination.

---

## 6. File Plan

### New Files

| File | Contents | Depends On |
|------|----------|------------|
| `Metalogic/TBSoundness.lean` | `tb_axiom_sound`, `tb_soundness`, `tb_soundness_derivable` | `Soundness.lean`, `Instances.lean` |
| `Metalogic/TBCompleteness.lean` | `tb_truth_lemma`, `tb_canonical_refl`, `tb_canonical_symm`, `tb_completeness` | `Completeness.lean`, `Instances.lean` |

### Modified Files

| File | Changes |
|------|---------|
| `ProofSystem.lean` | Add `Modal.HilbertTB` tag, `ModalTBHilbert` class |
| `ProofSystem/Instances.lean` | Add `TBAxiom` inductive, all TB typeclass instances |
| `Completeness.lean` | Add `canonical_symm` (parameterized) |
| `Metalogic.lean` | Add imports for `TBSoundness` and `TBCompleteness` |

### Dependency Graph

```
Task 100 (shared infra):
  - canonical_symm in Completeness.lean
  - TBAxiom in Instances.lean
  - HilbertTB tag + ModalTBHilbert class in ProofSystem.lean
  - TB typeclass instances in Instances.lean

Task 105 (this task):
  - TBSoundness.lean (depends on: TBAxiom, Soundness.lean)
  - TBCompleteness.lean (depends on: TBAxiom, canonical_symm, canonical_refl, truth_lemma)
```

---

## 7. Dependencies on Task 100

Task 105 depends on the following deliverables from task 100:

| Deliverable | File | Status |
|-------------|------|--------|
| `TBAxiom` inductive | `Instances.lean` | NOT STARTED |
| `Modal.HilbertTB` tag | `ProofSystem.lean` | NOT STARTED |
| `ModalTBHilbert` class | `ProofSystem.lean` | NOT STARTED |
| TB typeclass instances | `Instances.lean` | NOT STARTED |
| `canonical_symm` | `Completeness.lean` | NOT STARTED |

Task 100 is [NOT STARTED]. If task 105 is to proceed without task 100, it must define `TBAxiom`, `canonical_symm`, and the tag/class/instances itself. However, the task description says these are task 100's scope.

**Recommendation**: Task 105 should include the `TBAxiom` definition, `canonical_symm`, and TB-specific infrastructure inline if task 100 is not completed first. This avoids blocking. The planner should note that if task 100 runs first, these definitions should be reused rather than duplicated.

---

## 8. Proof Complexity Assessment

| Component | Complexity | Risk | Notes |
|-----------|-----------|------|-------|
| TBAxiom predicate | Low | None | Copy TAxiom + add modalB |
| TB soundness | Low | None | Direct case analysis, all cases follow existing patterns |
| canonical_symm | Medium | Low | Requires propositional reasoning in MCS, similar to canonical_eucl |
| TB truth_lemma | Low | None | Thin wrapper around existing truth_lemma |
| TB canonical_refl | Low | None | Thin wrapper around existing canonical_refl |
| TB completeness proof | Medium | Low | Boilerplate from S4Completeness with symm instead of trans |
| Typeclass instances | Low | None | Mechanical, following existing patterns |

### Potential Formalization Challenges

1. **canonical_symm proof step 6**: Deriving `box(neg(neg phi)) in T` from `box phi in T` requires constructing the propositional tautology `phi -> neg(neg phi)` as a `DerivationTree`, then using necessitation and K distribution. This involves explicit derivation tree construction, similar to what appears in `derive_box_from_inconsistency`. The pattern is well-established in the codebase.

2. **Double negation handling**: The diamond connective is `neg(box(neg phi))`, so `diamond(neg phi) = neg(box(neg(neg phi)))`. The membership `diamond(neg phi) in T` unfolds to `neg(box(neg(neg phi))) in T`, which means `box(neg(neg phi)) not in T`. We need `box(neg(neg phi)) in T` from `box phi in T`. This requires the propositional equivalence `phi <-> neg(neg phi)` lifted through the box modality.

3. **Alternative approach**: Instead of working with double negation, one can use the direct BRV proof more carefully. Given `R S T` and `box phi in T`, suppose `phi not in S`. Then `neg phi in S`. By axiom B on `neg phi`: `box(diamond(neg phi)) in S`. Since `R S T`: `diamond(neg phi) in T`. Unfolding: `neg(box(phi)) in T` (since `neg(neg phi)` in the inner position... no, `diamond(neg phi) = neg(box(neg(neg phi)))`, not `neg(box phi)`).

   The cleaner approach: Rather than going through double negation, establish a general lemma `canonical_symm_helper`: if `R S T` and `neg phi in S`, then `neg(box(neg(neg phi))) in T`, then show this contradicts `box phi in T` by showing `box(neg(neg phi))` and `box phi` are equivalent modulo MCS membership.

   **Even cleaner**: Use `mcs_box_mp` to derive `box(neg(neg phi))` from `box phi` and `box(phi -> neg(neg phi))`. The latter comes from `modal_closed_under_derivation` applied to the empty-context derivation of `phi -> neg(neg phi)` (a propositional tautology in classical logic, derivable from implyK, implyS, efq, peirce).

---

## 9. Tactic Survey Results

Based on analysis of existing proofs in the codebase:

| Goal | Tactic | Expected Result | Notes |
|------|--------|-----------------|-------|
| Axiom case analysis (soundness) | `cases h_ax with` | success | Standard pattern |
| Reflexivity case (T) | `intro h_box; exact h_box w (h_refl w)` | success | Identical to TSoundness |
| Symmetry case (B) | manual diamond_iff + symmetry | success | Matches Satisfies.b pattern |
| Consistency proof (completeness) | boilerplate from S4Completeness | success | Large but mechanical |
| canonical_symm core | `by_contra` + `mcs_box_diamond` + `mcs_not_mem_of_neg` | likely success | New but follows canonical_eucl pattern |
| Truth lemma instantiation | direct function application | success | Wrapper only |

---

## 10. Summary

TB soundness and completeness follow established codebase patterns closely. The main new mathematical content is `canonical_symm` (symmetry is canonical for axiom B), which is BRV Theorem 4.28 clause 2.

Key architectural decisions:
- TB uses T-based `truth_lemma` (NOT `k_truth_lemma`) because TBAxiom includes axiom T
- Completeness takes reflexivity + symmetry as frame conditions (not equivalence)
- `canonical_symm` is parameterized and goes in `Completeness.lean` (task 100's scope)
- TBSoundness.lean and TBCompleteness.lean are the two new files (task 105's scope)
- All typeclass infrastructure follows existing K/T/D/S4/S5 patterns mechanically
