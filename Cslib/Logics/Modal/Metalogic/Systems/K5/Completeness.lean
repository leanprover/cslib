/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.Completeness
public import Cslib.Logics.Modal.Metalogic.Systems.K.Completeness

/-! # Completeness Theorem for Modal Logic K5

This module proves completeness for modal logic K5 (K + axiom 5) over Euclidean
Kripke frames via the canonical model construction (completeness-via-canonicity).

## Main Results

- `k5_completeness`: Completeness for K5 over Euclidean frames.

## Strategy

K5 has NO axiom T, so it uses `k_truth_lemma` (from KCompleteness.lean), not
`truth_lemma` (which requires axiom T). The canonical frame is shown Euclidean
via `canonical_eucl_from_5` (from Completeness.lean), which uses only axiom 5.

## References

* Blackburn, de Rijke, Venema, "Modal Logic" (2002), Chapter 4
  - Theorem 4.29 pattern (completeness-via-canonicity with frame property proof)
  - Lemma 4.21 (Truth Lemma)
  - Proposition 4.12 (Completeness criterion)
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

universe u
variable {Atom : Type u}

/-! ## Completeness Theorem for K5 -/

/-- **Completeness Theorem for Modal Logic K5**:

If `phi` is valid over all Euclidean frames, then `phi` is derivable from the
empty context in the K5 proof system.

This follows BRV Proposition 4.12 + Theorem 4.29 pattern:
1. Assume phi is not derivable.
2. Then {neg phi} is consistent.
3. By Lindenbaum, extend to MCS M containing neg phi.
4. The canonical model is Euclidean (canonical_eucl_from_5, axiom 5).
5. By validity hypothesis, phi is satisfied at M in the canonical model.
6. By k_truth_lemma, phi in M.
7. But neg phi in M, contradiction. -/
theorem k5_completeness (φ : Proposition Atom)
    (h_valid : ∀ (World : Type u) (m : Model World Atom),
      (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃) →
      ∀ w, Satisfies m w φ) :
    Derivable (@K5Axiom Atom) φ := by
  by_contra h_not_deriv
  have h_cons := neg_consistent_of_not_derivable
    (fun φ ψ => .implyK φ ψ)
    (fun φ ψ χ => .implyS φ ψ χ)
    (fun φ => .efq φ)
    (fun φ ψ => .peirce φ ψ)
    h_not_deriv
  obtain ⟨M, hM_sup, hM_mcs⟩ := modal_lindenbaum h_cons
  let w : CanonicalWorld (@K5Axiom Atom) := ⟨M, hM_mcs⟩
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
      (h_valid (CanonicalWorld (@K5Axiom Atom))
        (CanonicalModel (@K5Axiom Atom))
        (canonical_eucl_from_5
          (fun φ ψ => .implyK φ ψ)
          (fun φ ψ χ => .implyS φ ψ χ)
          (fun φ ψ => .modalK φ ψ)
          (fun φ => .modalFive φ))
        w))

end Cslib.Logic.Modal
