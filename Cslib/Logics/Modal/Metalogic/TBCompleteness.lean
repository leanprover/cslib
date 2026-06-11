/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.Completeness
public import Cslib.Logics.Modal.ProofSystem.Instances

/-! # Completeness Theorem for Modal Logic TB

This module proves completeness for TB modal logic (= KTB) via the canonical Kripke
model construction: if a formula is valid on all reflexive, symmetric frames, then
it is TB-derivable.

The proof follows Blackburn, de Rijke, Venema "Modal Logic" (2002) Chapter 4:

- **Theorem 4.28, clause 1** (reflexivity is canonical): Uses axiom T (`□φ → φ`)
  via `canonical_refl` and `mcs_box_closure`.

- **Theorem 4.28, clause 2** (symmetry is canonical): Uses axiom B (`φ → □◇φ`)
  via `canonical_symm`.

## Main Results

- `tb_canonical_refl`: The canonical frame for TB is reflexive (BRV Thm 4.28 cl.1).
- `tb_canonical_symm`: The canonical frame for TB is symmetric (BRV Thm 4.28 cl.2).
- `tb_truth_lemma`: TB-specific Truth Lemma (reuses existing `truth_lemma`).
- `tb_completeness`: If `phi` is valid over all reflexive, symmetric frames,
  then `phi` is TB-derivable (Blackburn Theorem 4.28 + Theorem 4.22).

## References

* Blackburn, de Rijke, Venema - Modal Logic (Ch. 4, Theorems 4.22, 4.28)
* Cslib/Logics/Modal/Metalogic/Completeness.lean -- parameterized canonical model
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

universe u
variable {Atom : Type u}

/-! ## TB Canonical Frame Properties (BRV Theorem 4.28) -/

/-- **TB Canonical Frame Reflexivity** (BRV Theorem 4.28, clause 1):
The canonical frame for TB is reflexive. -/
theorem tb_canonical_refl
    (S : CanonicalWorld (@TBAxiom Atom)) :
    (CanonicalModel (@TBAxiom Atom)).r S S :=
  canonical_refl
    (fun φ ψ => .implyK φ ψ)
    (fun φ ψ χ => .implyS φ ψ χ)
    (fun φ => .modalT φ)
    S

/-- **TB Canonical Frame Symmetry** (BRV Theorem 4.28, clause 2):
The canonical frame for TB is symmetric. -/
theorem tb_canonical_symm
    (S T : CanonicalWorld (@TBAxiom Atom)) :
    (CanonicalModel (@TBAxiom Atom)).r S T →
    (CanonicalModel (@TBAxiom Atom)).r T S :=
  canonical_symm
    (fun φ ψ => .implyK φ ψ)
    (fun φ ψ χ => .implyS φ ψ χ)
    (fun φ ψ => .modalK φ ψ)
    (fun φ => .modalB φ)
    S T

/-! ## TB Truth Lemma (BRV Lemma 4.21 for TB) -/

/-- **TB Truth Lemma** (BRV Lemma 4.21 for TB):
Reuses the existing parameterized `truth_lemma` instantiated at `TBAxiom`. -/
theorem tb_truth_lemma
    (S : CanonicalWorld (@TBAxiom Atom))
    (φ : Proposition Atom) :
    (Satisfies (CanonicalModel (@TBAxiom Atom)) S φ ↔ φ ∈ S.val) :=
  truth_lemma
    (fun φ ψ => .implyK φ ψ)
    (fun φ ψ χ => .implyS φ ψ χ)
    (fun φ => .efq φ)
    (fun φ ψ => .peirce φ ψ)
    (fun φ ψ => .modalK φ ψ)
    (fun φ => .modalT φ)
    S φ

/-! ## TB Completeness Theorem (BRV Theorem 4.28 + Theorem 4.22) -/

/-- **Completeness Theorem for TB Modal Logic** (BRV Thm 4.28 + Thm 4.22):

If `phi` is valid over all reflexive, symmetric frames, then `phi` is derivable
from the TB axiom set. -/
theorem tb_completeness (φ : Proposition Atom)
    (h_valid : ∀ (World : Type u) (m : Model World Atom),
      (∀ w, m.r w w) →
      (∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁) →
      ∀ w, Satisfies m w φ) :
    Derivable (@TBAxiom Atom) φ := by
  -- Step 1: Contrapositive setup
  by_contra h_not_deriv
  -- Step 2: Show {neg(phi)} is TB-consistent (prerequisite for Lindenbaum, Lemma 4.17)
  have h_cons : SetConsistent (@TBAxiom Atom)
      ({Proposition.neg φ} : Set (Proposition Atom)) := by
    intro L hL
    unfold Metalogic.Consistent
    intro ⟨d⟩
    have d_weak : DerivationTree (@TBAxiom Atom) [Proposition.neg φ]
        Proposition.bot :=
      .weakening L [Proposition.neg φ] .bot d (fun x hx => by
        have := hL x hx; simp only [Set.mem_singleton_iff] at this
        exact List.mem_cons.mpr (Or.inl this))
    have d_dne := deductionTheorem
      (fun φ ψ => .implyK φ ψ)
      (fun φ ψ χ => .implyS φ ψ χ)
      [] (Proposition.neg φ) .bot d_weak
    let neg_phi := Proposition.neg φ
    have efq_ax : DerivationTree (@TBAxiom Atom) (Atom := Atom) []
        (Proposition.bot.imp φ) :=
      .ax [] _ (.efq φ)
    have ik : DerivationTree (@TBAxiom Atom) (Atom := Atom) []
        ((Proposition.bot.imp φ).imp
          (neg_phi.imp (Proposition.bot.imp φ))) :=
      .ax [] _ (.implyK (Proposition.bot.imp φ) neg_phi)
    have step_k := DerivationTree.modus_ponens [] _ _ ik efq_ax
    have is_ax : DerivationTree (@TBAxiom Atom) (Atom := Atom) []
        ((neg_phi.imp (Proposition.bot.imp φ)).imp
         ((neg_phi.imp Proposition.bot).imp (neg_phi.imp φ))) :=
      .ax [] _ (.implyS neg_phi Proposition.bot φ)
    have step_s := DerivationTree.modus_ponens [] _ _ is_ax step_k
    have step3 := DerivationTree.modus_ponens [] _ _ step_s d_dne
    have peirce_ax : DerivationTree (@TBAxiom Atom) (Atom := Atom) []
        (((φ.imp Proposition.bot).imp φ).imp φ) :=
      .ax [] _ (.peirce φ Proposition.bot)
    have d_phi := DerivationTree.modus_ponens [] _ _ peirce_ax step3
    exact h_not_deriv ⟨d_phi⟩
  -- Step 3: Lindenbaum extension (Lemma 4.17)
  obtain ⟨M, hM_sup, hM_mcs⟩ := modal_lindenbaum h_cons
  -- Step 4: Canonical world
  let w : CanonicalWorld (@TBAxiom Atom) := ⟨M, hM_mcs⟩
  -- Steps 5-7: Truth Lemma + frame properties + contradiction
  exact mcs_not_mem_of_neg
    (fun φ ψ => .implyK φ ψ)
    (fun φ ψ χ => .implyS φ ψ χ)
    hM_mcs (hM_sup (Set.mem_singleton _))
    ((tb_truth_lemma w φ).mp
      (h_valid (CanonicalWorld (@TBAxiom Atom))
        (CanonicalModel (@TBAxiom Atom))
        tb_canonical_refl
        (fun w₁ w₂ h => tb_canonical_symm w₁ w₂ h)
        w))

end Cslib.Logic.Modal
