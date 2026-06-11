/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.Completeness
public import Cslib.Logics.Modal.ProofSystem.Instances

/-! # Completeness Theorem for S4 Modal Logic

This module proves completeness for S4 modal logic (= KT4) via the canonical Kripke
model construction: if a formula is valid on all reflexive, transitive frames, then
it is S4-derivable.

The proof follows Blackburn, de Rijke, Venema "Modal Logic" (2002) Chapter 4:

- **Theorem 4.29** (S4 completeness): S4 = KT4 contains both the T and 4 axioms.
  The proof of Theorem 4.27 shows the canonical frame of any normal logic containing
  the 4 axiom is transitive; the proof of Theorem 4.28, clause 1, shows the canonical
  frame of any normal logic containing the T axiom is reflexive. Since S4 contains
  both axioms, its canonical frame has both properties.

- **Theorem 4.27** (transitivity is canonical): Uses axiom 4 (`□φ → □□φ`) via
  `canonical_trans` and `mcs_box_box`.

- **Theorem 4.28, clause 1** (reflexivity is canonical): Uses axiom T (`□φ → φ`)
  via `canonical_refl` and `mcs_box_closure`.

## Main Results

- `s4_completeness`: If `phi` is valid over all reflexive, transitive frames,
  then `phi` is S4-derivable (Blackburn Theorem 4.29).

## References

* Blackburn, de Rijke, Venema - Modal Logic (Ch. 4, Theorems 4.22, 4.27, 4.28, 4.29)
* Cslib/Logics/Modal/Metalogic/Completeness.lean -- parameterized canonical model
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

universe u
variable {Atom : Type u}

/-! ## S4 Completeness (Blackburn Theorem 4.29) -/

/-- **Completeness Theorem for S4 Modal Logic** (Blackburn Theorem 4.29):

If `phi` is valid over all reflexive, transitive frames, then `phi` is derivable
from the S4 axiom set.

The proof is by contrapositive (Canonical Model Theorem, Blackburn Theorem 4.22):
assume `phi` is not S4-derivable, then `{neg phi}` is S4-consistent, extend it to
an MCS via Lindenbaum's Lemma (Lemma 4.17), and show `neg phi` is satisfied in the
canonical model. The canonical frame is reflexive (Theorem 4.28, clause 1, from
axiom T) and transitive (Theorem 4.27, from axiom 4), so `h_valid` applies and
gives satisfaction of `phi` at the same world -- contradiction. -/
theorem s4_completeness (φ : Proposition Atom)
    (h_valid : ∀ (World : Type u) (m : Model World Atom),
      (∀ w, m.r w w) →
      (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃) →
      ∀ w, Satisfies m w φ) :
    Derivable (@S4Axiom Atom) φ := by
  -- Step 1: Contrapositive setup
  by_contra h_not_deriv
  -- Step 2: Show {neg(phi)} is S4-consistent (prerequisite for Lindenbaum, Lemma 4.17)
  have h_cons : Modal.SetConsistent (@S4Axiom Atom)
      ({Proposition.neg φ} : Set (Proposition Atom)) := by
    intro L hL
    unfold Metalogic.Consistent
    intro ⟨d⟩
    have d_weak : DerivationTree (@S4Axiom Atom) [Proposition.neg φ]
        Proposition.bot :=
      .weakening L [Proposition.neg φ] .bot d (fun x hx => by
        have := hL x hx; simp at this
        exact List.mem_cons.mpr (Or.inl this))
    have d_dne := deductionTheorem
      (fun φ ψ => .implyK φ ψ)
      (fun φ ψ χ => .implyS φ ψ χ)
      [] (Proposition.neg φ) .bot d_weak
    let neg_phi := Proposition.neg φ
    have efq_ax : DerivationTree (@S4Axiom Atom) (Atom := Atom) []
        (Proposition.bot.imp φ) :=
      .ax [] _ (.efq φ)
    have ik : DerivationTree (@S4Axiom Atom) (Atom := Atom) []
        ((Proposition.bot.imp φ).imp
          (neg_phi.imp (Proposition.bot.imp φ))) :=
      .ax [] _ (.implyK (Proposition.bot.imp φ) neg_phi)
    have step_k := DerivationTree.modus_ponens [] _ _ ik efq_ax
    have is_ax : DerivationTree (@S4Axiom Atom) (Atom := Atom) []
        ((neg_phi.imp (Proposition.bot.imp φ)).imp
         ((neg_phi.imp Proposition.bot).imp (neg_phi.imp φ))) :=
      .ax [] _ (.implyS neg_phi Proposition.bot φ)
    have step_s := DerivationTree.modus_ponens [] _ _ is_ax step_k
    have step3 := DerivationTree.modus_ponens [] _ _ step_s d_dne
    have peirce_ax : DerivationTree (@S4Axiom Atom) (Atom := Atom) []
        (((φ.imp Proposition.bot).imp φ).imp φ) :=
      .ax [] _ (.peirce φ Proposition.bot)
    have d_phi := DerivationTree.modus_ponens [] _ _ peirce_ax step3
    exact h_not_deriv ⟨d_phi⟩
  -- Step 3: Lindenbaum extension (Lemma 4.17)
  obtain ⟨M, hM_sup, hM_mcs⟩ := modal_lindenbaum h_cons
  -- Step 4: Canonical world
  let w : CanonicalWorld (@S4Axiom Atom) := ⟨M, hM_mcs⟩
  -- Steps 5-7: Truth Lemma + frame properties + contradiction
  -- Step 5: truth_lemma (Lemma 4.21) instantiated at S4Axiom constructors
  -- Step 6: Frame properties via Theorems 4.27 + 4.28.1 (combined = Thm 4.29):
  --   canonical_refl from axiom T (Thm 4.28, clause 1)
  --   canonical_trans from axiom 4 (Thm 4.27)
  --   NO canonical_eucl needed (key simplification vs S5)
  -- Step 7: Contradiction via mcs_not_mem_of_neg
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
      (h_valid (CanonicalWorld (@S4Axiom Atom))
        (CanonicalModel (@S4Axiom Atom))
        (canonical_refl
          (fun φ ψ => .implyK φ ψ)
          (fun φ ψ χ => .implyS φ ψ χ)
          (fun φ => .modalT φ))
        (canonical_trans
          (fun φ ψ => .implyK φ ψ)
          (fun φ ψ χ => .implyS φ ψ χ)
          (fun φ => .modalFour φ))
        w))

end Cslib.Logic.Modal
