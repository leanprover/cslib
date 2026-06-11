/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.MCS
public import Cslib.Logics.Modal.Metalogic.Soundness
public import Cslib.Logics.Modal.Metalogic.Completeness
public import Cslib.Logics.Modal.ProofSystem.Instances

/-! # Completeness Theorem for Modal Logic T

This module proves completeness for modal logic T via the canonical Kripke model
construction, following Blackburn, de Rijke, Venema "Modal Logic" (2002),
Theorem 4.28, clause 1.

The key insight is that the canonical frame for T is reflexive (Thm 4.28 cl.1),
and the existing parameterized `truth_lemma` and `mcs_box_witness` work directly
for T since `TAxiom` includes axiom T.

## Main Results

- `t_canonical_refl`: The canonical frame for T is reflexive (BRV Thm 4.28 cl.1).
- `t_truth_lemma`: T-specific Truth Lemma (reuses existing `truth_lemma`).
- `t_completeness`: T completeness theorem (BRV Thm 4.28 cl.1 + Thm 4.22).

## References

* Blackburn, de Rijke, Venema - Modal Logic (Ch. 4, Theorems 4.22, 4.28)
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

universe u
variable {Atom : Type u}

/-! ## T Canonical Frame Reflexivity (BRV Theorem 4.28, clause 1) -/

/-- **T Canonical Frame Reflexivity** (BRV Theorem 4.28, clause 1):
The canonical frame for T is reflexive. If `phi in w` and `w` is a T-MCS,
then `phi -> diamond(phi) in w` (axiom T), so `diamond(phi) in w`, thus R^T ww. -/
theorem t_canonical_refl
    (S : CanonicalWorld (@TAxiom Atom)) :
    (CanonicalModel (@TAxiom Atom)).r S S :=
  canonical_refl
    (fun φ ψ => .implyK φ ψ)
    (fun φ ψ χ => .implyS φ ψ χ)
    (fun φ => .modalT φ)
    S

/-! ## T Truth Lemma (BRV Lemma 4.21 for T) -/

/-- **T Truth Lemma** (BRV Lemma 4.21 for T):
Reuses the existing parameterized `truth_lemma` instantiated at `TAxiom`. -/
theorem t_truth_lemma
    (S : CanonicalWorld (@TAxiom Atom))
    (φ : Proposition Atom) :
    (Satisfies (CanonicalModel (@TAxiom Atom)) S φ ↔ φ ∈ S.val) :=
  truth_lemma
    (fun φ ψ => .implyK φ ψ)
    (fun φ ψ χ => .implyS φ ψ χ)
    (fun φ => .efq φ)
    (fun φ ψ => .peirce φ ψ)
    (fun φ ψ => .modalK φ ψ)
    (fun φ => .modalT φ)
    S φ

/-! ## T Completeness Theorem (BRV Theorem 4.28 cl.1 + Theorem 4.22) -/

/-- **Completeness Theorem for Modal Logic T** (BRV Thm 4.28 cl.1 + Thm 4.22):

If `phi` is valid over all reflexive frames, then `phi` is T-derivable
from the empty context. -/
theorem t_completeness (φ : Proposition Atom)
    (h_valid : ∀ (World : Type u) (m : Model World Atom),
      (∀ w, m.r w w) →
      ∀ w, Satisfies m w φ) :
    Derivable (@TAxiom Atom) φ := by
  by_contra h_not_deriv
  have h_cons : SetConsistent (@TAxiom Atom)
      ({Proposition.neg φ} : Set (Proposition Atom)) := by
    intro L hL
    unfold Metalogic.Consistent
    intro ⟨d⟩
    have d_weak : DerivationTree (@TAxiom Atom) [Proposition.neg φ]
        Proposition.bot :=
      .weakening L [Proposition.neg φ] .bot d (fun x hx => by
        have := hL x hx; simp only [Set.mem_singleton_iff] at this
        exact List.mem_cons.mpr (Or.inl this))
    have d_dne := deductionTheorem
      (fun φ ψ => .implyK φ ψ)
      (fun φ ψ χ => .implyS φ ψ χ)
      [] (Proposition.neg φ) .bot d_weak
    let neg_phi := Proposition.neg φ
    have efq_ax : DerivationTree (@TAxiom Atom) (Atom := Atom) []
        (Proposition.bot.imp φ) :=
      .ax [] _ (.efq φ)
    have ik : DerivationTree (@TAxiom Atom) (Atom := Atom) []
        ((Proposition.bot.imp φ).imp
          (neg_phi.imp (Proposition.bot.imp φ))) :=
      .ax [] _ (.implyK (Proposition.bot.imp φ) neg_phi)
    have step_k := DerivationTree.modus_ponens [] _ _ ik efq_ax
    have is_ax : DerivationTree (@TAxiom Atom) (Atom := Atom) []
        ((neg_phi.imp (Proposition.bot.imp φ)).imp
         ((neg_phi.imp Proposition.bot).imp (neg_phi.imp φ))) :=
      .ax [] _ (.implyS neg_phi Proposition.bot φ)
    have step_s := DerivationTree.modus_ponens [] _ _ is_ax step_k
    have step3 := DerivationTree.modus_ponens [] _ _ step_s d_dne
    have peirce_ax : DerivationTree (@TAxiom Atom) (Atom := Atom) []
        (((φ.imp Proposition.bot).imp φ).imp φ) :=
      .ax [] _ (.peirce φ Proposition.bot)
    have d_phi := DerivationTree.modus_ponens [] _ _ peirce_ax step3
    exact h_not_deriv ⟨d_phi⟩
  obtain ⟨M, hM_sup, hM_mcs⟩ := modal_lindenbaum h_cons
  let w : CanonicalWorld (@TAxiom Atom) := ⟨M, hM_mcs⟩
  exact mcs_not_mem_of_neg
    (fun φ ψ => .implyK φ ψ)
    (fun φ ψ χ => .implyS φ ψ χ)
    hM_mcs (hM_sup (Set.mem_singleton _))
    ((t_truth_lemma w φ).mp
      (h_valid (CanonicalWorld (@TAxiom Atom))
        (CanonicalModel (@TAxiom Atom))
        t_canonical_refl
        w))

end Cslib.Logic.Modal
