/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.KCompleteness
public import Cslib.Logics.Modal.Metalogic.Completeness
public import Cslib.Logics.Modal.ProofSystem.Instances

/-! # Completeness Theorem for Modal Logic B (KB)

This module proves completeness for modal logic B over symmetric Kripke frames
via the canonical model construction (completeness-via-canonicity).

B = K + axiom B (`φ → □◇φ`). Crucially, B does NOT include axiom T (`□φ → φ`),
so this proof uses `k_truth_lemma` (from KCompleteness.lean) rather than `truth_lemma`
(from Completeness.lean which requires axiom T).

## Main Results

- `b_completeness`: If `φ` is valid over all symmetric frames, then `φ` is
  B-derivable from the empty context.

## References

* Blackburn, de Rijke, Venema, "Modal Logic" (2002), Chapter 4
  - Theorem 4.28 clause 2 (KB symmetry is canonical)
  - Lemma 4.21 (Truth Lemma, K-specific version)
  - Proposition 4.12 (Completeness criterion)
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

universe u
variable {Atom : Type u}

/-! ## Completeness Theorem for B -/

/-- **Completeness Theorem for Modal Logic B**:

If `φ` is valid over all symmetric frames, then `φ` is derivable from the empty
context in the B proof system.

This follows Blackburn Proposition 4.12 + Theorem 4.28 clause 2:
1. Assume `φ` is not derivable.
2. Then `{¬φ}` is consistent.
3. By Lindenbaum, extend to MCS `M` containing `¬φ`.
4. The canonical model is symmetric (`canonical_symm`, Theorem 4.28 clause 2).
5. By validity hypothesis, `φ` is satisfied at `M` in the canonical model.
6. By `k_truth_lemma`, `φ ∈ M`.
7. But `¬φ ∈ M`, contradiction. -/
theorem b_completeness (φ : Proposition Atom)
    (h_valid : ∀ (World : Type u) (m : Model World Atom),
      (∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁) →
      ∀ w, Satisfies m w φ) :
    Derivable (@BAxiom Atom) φ := by
  by_contra h_not_deriv
  have h_cons := neg_consistent_of_not_derivable
    (fun φ ψ => .implyK φ ψ)
    (fun φ ψ χ => .implyS φ ψ χ)
    (fun φ => .efq φ)
    (fun φ ψ => .peirce φ ψ)
    h_not_deriv
  obtain ⟨M, hM_sup, hM_mcs⟩ := modal_lindenbaum h_cons
  let w : CanonicalWorld (@BAxiom Atom) := ⟨M, hM_mcs⟩
  -- Show canonical model is symmetric using canonical_symm (BRV Theorem 4.28 clause 2)
  have h_symm : ∀ (S T : CanonicalWorld (@BAxiom Atom)),
      (CanonicalModel (@BAxiom Atom)).r S T →
      (CanonicalModel (@BAxiom Atom)).r T S :=
    canonical_symm
      (fun φ ψ => .implyK φ ψ)
      (fun φ ψ χ => .implyS φ ψ χ)
      (fun φ ψ => .modalK φ ψ)
      (fun φ => .modalB φ)
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
      (h_valid (CanonicalWorld (@BAxiom Atom))
        (CanonicalModel (@BAxiom Atom))
        (fun S T hST => h_symm S T hST)
        w))

end Cslib.Logic.Modal
