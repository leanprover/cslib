/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.Completeness
public import Cslib.Logics.Modal.Metalogic.Systems.K.Completeness
public import Cslib.Logics.Modal.ProofSystem.Instances

/-! # Completeness Theorem for K45 Modal Logic

This module proves completeness for K45 modal logic (= K + 4 + 5) via the canonical
Kripke model construction: if a formula is valid on all transitive, Euclidean frames,
then it is K45-derivable.

The proof follows Blackburn, de Rijke, Venema "Modal Logic" (2002) Chapter 4:

- **Theorem 4.27** (transitivity is canonical): The canonical frame of any normal
  logic containing the 4 axiom is transitive, via `canonical_trans`.

- **Axiom 5 canonical for Euclideanness**: The canonical frame of any normal logic
  containing axiom 5 is Euclidean, via `canonical_eucl_from_5`.

- Since K45 has NO axiom T, the proof uses `k_truth_lemma` (BRV Lemma 4.21 for K)
  instead of `truth_lemma` (which requires axiom T).

## Main Results

- `k45_completeness`: If `phi` is valid over all transitive, Euclidean frames,
  then `phi` is K45-derivable.

## References

* Blackburn, de Rijke, Venema - Modal Logic (Ch. 4, Theorems 4.22, 4.27, Definition 4.30)
* Cslib/Logics/Modal/Metalogic/Completeness.lean -- canonical model, canonical_trans,
  canonical_eucl_from_5
* Cslib/Logics/Modal/Metalogic/KCompleteness.lean -- k_truth_lemma (no axiom T)
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

universe u
variable {Atom : Type u}

/-! ## K45 Completeness (Blackburn Theorem 4.29 pattern) -/

/-- **Completeness Theorem for K45 Modal Logic**:

If `phi` is valid over all transitive, Euclidean frames, then `phi` is derivable
from the K45 axiom set.

The proof is by contrapositive (Canonical Model Theorem, Blackburn Theorem 4.22):
assume `phi` is not K45-derivable, then `{neg phi}` is K45-consistent, extend it to
an MCS via Lindenbaum's Lemma (Lemma 4.17), and show `neg phi` is satisfied in the
canonical model. The canonical frame is transitive (Theorem 4.27, from axiom 4) and
Euclidean (from axiom 5 via `canonical_eucl_from_5`), so `h_valid` applies and gives
satisfaction of `phi` at the same world -- contradiction.

Note: K45 has NO axiom T, so this proof uses `k_truth_lemma` (which requires only
implyK, implyS, efq, peirce, modalK) instead of `truth_lemma` (which requires T). -/
theorem k45_completeness (φ : Proposition Atom)
    (h_valid : ∀ (World : Type u) (m : Model World Atom),
      (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃) →
      (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃) →
      ∀ w, Satisfies m w φ) :
    Derivable (@K45Axiom Atom) φ := by
  -- Step 1: Contrapositive setup
  by_contra h_not_deriv
  -- Step 2: Show {neg(phi)} is K45-consistent (prerequisite for Lindenbaum, Lemma 4.17)
  have h_cons := neg_consistent_of_not_derivable
    (fun φ ψ => .implyK φ ψ)
    (fun φ ψ χ => .implyS φ ψ χ)
    (fun φ => .efq φ)
    (fun φ ψ => .peirce φ ψ)
    h_not_deriv
  -- Step 3: Lindenbaum extension (Lemma 4.17)
  obtain ⟨M, hM_sup, hM_mcs⟩ := modal_lindenbaum h_cons
  -- Step 4: Canonical world
  let w : CanonicalWorld (@K45Axiom Atom) := ⟨M, hM_mcs⟩
  -- Steps 5-7: k_truth_lemma + frame properties + contradiction
  -- Step 5: k_truth_lemma (Lemma 4.21 for K) instantiated at K45Axiom constructors
  -- Step 6: Frame properties:
  --   canonical_trans from axiom 4 (Thm 4.27)
  --   canonical_eucl_from_5 from axiom 5
  -- Step 7: Contradiction via mcs_not_mem_of_neg
  exact mcs_not_mem_of_neg
    (fun φ ψ => .implyK φ ψ)
    (fun φ ψ χ => .implyS φ ψ χ)
    hM_mcs (hM_sup (Set.mem_singleton _))
    ((k_truth_lemma
      (fun φ ψ => .implyK φ ψ)
      (fun φ ψ χ => .implyS φ ψ χ)
      (fun φ => .efq φ)
      (fun φ ψ => .peirce φ ψ)
      (fun φ ψ => .modalK φ ψ)
      w φ).mp
      (h_valid (CanonicalWorld (@K45Axiom Atom))
        (CanonicalModel (@K45Axiom Atom))
        (canonical_trans
          (fun φ ψ => .implyK φ ψ)
          (fun φ ψ χ => .implyS φ ψ χ)
          (fun φ => .modalFour φ))
        (canonical_eucl_from_5
          (fun φ ψ => .implyK φ ψ)
          (fun φ ψ χ => .implyS φ ψ χ)
          (fun φ ψ => .modalK φ ψ)
          (fun φ => .modalFive φ))
        w))

end Cslib.Logic.Modal
