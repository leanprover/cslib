/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.Completeness
public import Cslib.Logics.Modal.ProofSystem.Instances

/-! # Completeness Theorem for Modal Logic S5

This module proves completeness for modal logic S5: every formula valid
over all S5 frames (reflexive, transitive, Euclidean) is derivable from
`ModalAxiom`.

## Main Results

- `s5_completeness`: If `phi` is valid over all S5 frames, then `phi`
  is S5-derivable from the empty context.

## References

* Blackburn, de Rijke, Venema - Modal Logic (Ch. 4, Canonical Models)
* Cslib/Logics/Modal/Metalogic/Completeness.lean -- parameterized infrastructure
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

universe u
variable {Atom : Type u}

/-! ## S5 Completeness Theorem -/

/-- **Completeness Theorem for S5 Modal Logic**:

If `phi` is valid over all S5 frames (reflexive, transitive, Euclidean), then `phi`
is derivable from the empty context. -/
theorem s5_completeness (φ : Proposition Atom)
    (h_valid : ∀ (World : Type u) (m : Model World Atom),
      (∀ w, m.r w w) →
      (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃) →
      (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃) →
      ∀ w, Satisfies m w φ) :
    Derivable (@ModalAxiom Atom) φ := by
  by_contra h_not_deriv
  have h_cons := neg_consistent_of_not_derivable
    (fun φ ψ => .implyK φ ψ)
    (fun φ ψ χ => .implyS φ ψ χ)
    (fun φ => .efq φ)
    (fun φ ψ => .peirce φ ψ)
    h_not_deriv
  obtain ⟨M, hM_sup, hM_mcs⟩ := modal_lindenbaum h_cons
  let w : CanonicalWorld (@ModalAxiom Atom) := ⟨M, hM_mcs⟩
  exact mcs_not_mem_of_neg
    (fun φ ψ => .implyK φ ψ)
    (fun φ ψ χ => .implyS φ ψ χ)
    hM_mcs (hM_sup (Set.mem_singleton _))
    ((truth_lemma
      (fun φ ψ => .implyK φ ψ)
      (fun φ ψ χ => .implyS φ ψ χ)
      (fun φ => .efq φ)
      (fun φ ψ => .peirce φ ψ)
      (fun φ ψ => .modalK φ ψ)
      (fun φ => .modalT φ)
      w φ).mp
      (h_valid (CanonicalWorld (@ModalAxiom Atom))
        (CanonicalModel (@ModalAxiom Atom))
        (canonical_refl
          (fun φ ψ => .implyK φ ψ)
          (fun φ ψ χ => .implyS φ ψ χ)
          (fun φ => .modalT φ))
        (canonical_trans
          (fun φ ψ => .implyK φ ψ)
          (fun φ ψ χ => .implyS φ ψ χ)
          (fun φ => .modalFour φ))
        (canonical_eucl
          (fun φ ψ => .implyK φ ψ)
          (fun φ ψ χ => .implyS φ ψ χ)
          (fun φ => .modalT φ)
          (fun φ => .modalFour φ)
          (fun φ => .modalB φ)
          (fun φ ψ => .modalK φ ψ))
        w))

/-- Backward-compatible alias for `s5_completeness`. -/
abbrev completeness := @s5_completeness

end Cslib.Logic.Modal
