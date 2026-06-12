/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.Systems.K.Completeness
public import Cslib.Logics.Modal.Metalogic.Completeness
public import Cslib.Logics.Modal.ProofSystem.Instances

/-! # Completeness Theorem for KB5 Modal Logic

This module proves completeness for KB5 modal logic (= K + B + 5) via the canonical
Kripke model construction: if a formula is valid on all symmetric, Euclidean frames,
then it is KB5-derivable.

KB5 is the first logic in the modal cube that combines BOTH new canonical lemmas
from task 100: `canonical_symm` (symmetry from axiom B alone) and
`canonical_eucl_from_5` (Euclideanness from axiom 5 alone).

**Key distinction**: KB5 does NOT contain axiom T, so the completeness proof uses
`k_truth_lemma` (K-style, no reflexivity hypothesis) rather than `truth_lemma`
(which requires axiom T for the box witness / existence lemma).

The proof follows Blackburn, de Rijke, Venema "Modal Logic" (2002) Chapter 4:

- **Theorem 4.28, clause 2** (symmetry is canonical): Uses axiom B (`φ → □◇φ`)
  via `canonical_symm`.

- **Axiom 5 canonicity** (Euclideanness is canonical): Uses axiom 5 (`◇φ → □◇φ`)
  via `canonical_eucl_from_5`.

## Main Results

- `kb5_completeness`: If `phi` is valid over all symmetric, Euclidean frames,
  then `phi` is KB5-derivable.

## References

* Blackburn, de Rijke, Venema - Modal Logic (Ch. 4, Theorems 4.22, 4.23, 4.28)
* Cslib/Logics/Modal/Metalogic/Completeness.lean -- canonical_symm, canonical_eucl_from_5
* Cslib/Logics/Modal/Metalogic/KCompleteness.lean -- k_truth_lemma (no axiom T)
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

universe u
variable {Atom : Type u}

/-! ## KB5 Completeness (Blackburn Theorem 4.22 pattern) -/

/-- **Completeness Theorem for KB5 Modal Logic**:

If `phi` is valid over all symmetric, Euclidean frames, then `phi` is derivable
from the KB5 axiom set.

The proof is by contrapositive (Canonical Model Theorem, Blackburn Theorem 4.22):
assume `phi` is not KB5-derivable, then `{neg phi}` is KB5-consistent, extend it to
an MCS via Lindenbaum's Lemma (Lemma 4.17), and show `neg phi` is satisfied in the
canonical model. The canonical frame is symmetric (Theorem 4.28, clause 2, from
axiom B) and Euclidean (from axiom 5), so `h_valid` applies and gives satisfaction
of `phi` at the same world -- contradiction.

Uses `k_truth_lemma` (not `truth_lemma`) since KB5 lacks axiom T. -/
theorem kb5_completeness (φ : Proposition Atom)
    (h_valid : ∀ (World : Type u) (m : Model World Atom),
      (∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁) →
      (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃) →
      ∀ w, Satisfies m w φ) :
    Derivable (@KB5Axiom Atom) φ := by
  -- Step 1: Contrapositive setup
  by_contra h_not_deriv
  -- Step 2: Show {neg(phi)} is KB5-consistent (prerequisite for Lindenbaum, Lemma 4.17)
  have h_cons := neg_consistent_of_not_derivable
    (fun φ ψ => .implyK φ ψ)
    (fun φ ψ χ => .implyS φ ψ χ)
    (fun φ => .efq φ)
    (fun φ ψ => .peirce φ ψ)
    h_not_deriv
  -- Step 3: Lindenbaum extension (Lemma 4.17)
  obtain ⟨M, hM_sup, hM_mcs⟩ := modal_lindenbaum h_cons
  -- Step 4: Canonical world
  let w : CanonicalWorld (@KB5Axiom Atom) := ⟨M, hM_mcs⟩
  -- Steps 5-7: k_truth_lemma (no axiom T!) + frame properties + contradiction
  -- Step 5: k_truth_lemma (Lemma 4.21 for K) instantiated at KB5Axiom constructors
  -- Step 6: Frame properties:
  --   canonical_symm from axiom B (Thm 4.28, clause 2)
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
      (h_valid (CanonicalWorld (@KB5Axiom Atom))
        (CanonicalModel (@KB5Axiom Atom))
        (canonical_symm
          (fun φ ψ => .implyK φ ψ)
          (fun φ ψ χ => .implyS φ ψ χ)
          (fun φ ψ => .modalK φ ψ)
          (fun φ => .modalB φ))
        (canonical_eucl_from_5
          (fun φ ψ => .implyK φ ψ)
          (fun φ ψ χ => .implyS φ ψ χ)
          (fun φ ψ => .modalK φ ψ)
          (fun φ => .modalFive φ))
        w))

end Cslib.Logic.Modal
