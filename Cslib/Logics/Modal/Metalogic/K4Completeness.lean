/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.KCompleteness
public import Cslib.Logics.Modal.Metalogic.Completeness
public import Cslib.Logics.Modal.ProofSystem.Instances

/-! # Completeness Theorem for K4 Modal Logic

This module proves completeness for K4 modal logic (= K + axiom 4) via the canonical
Kripke model construction: if a formula is valid on all transitive frames, then it is
K4-derivable.

The proof follows Blackburn, de Rijke, Venema "Modal Logic" (2002) Chapter 4:

- **Theorem 4.27** (transitivity is canonical): Uses axiom 4 (`□φ → □□φ`) via
  `canonical_trans` and `mcs_box_box`.

The key insight is that K4 lacks axiom T, so completeness must use `k_truth_lemma`
(from `KCompleteness.lean`) rather than `truth_lemma` (from `Completeness.lean`),
combined with `canonical_trans` (from `Completeness.lean`) for transitivity of
the canonical frame.

## Main Results

- `k4_completeness`: If `phi` is valid over all transitive frames,
  then `phi` is K4-derivable (Blackburn Theorem 4.27 + Theorem 4.22).

## References

* Blackburn, de Rijke, Venema - Modal Logic (Ch. 4, Theorems 4.22, 4.27)
* Cslib/Logics/Modal/Metalogic/KCompleteness.lean -- k_truth_lemma (no axiom T)
* Cslib/Logics/Modal/Metalogic/Completeness.lean -- canonical_trans (axiom 4)
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

universe u
variable {Atom : Type u}

/-! ## K4 Completeness (Blackburn Theorem 4.27 + Theorem 4.22) -/

/-- **Completeness Theorem for K4 Modal Logic** (Blackburn Theorem 4.27 + 4.22):

If `phi` is valid over all transitive frames, then `phi` is derivable
from the K4 axiom set.

The proof is by contrapositive (Canonical Model Theorem, Blackburn Theorem 4.22):
assume `phi` is not K4-derivable, then `{neg phi}` is K4-consistent, extend it to
an MCS via Lindenbaum's Lemma (Lemma 4.17), and show `neg phi` is satisfied in the
canonical model. The canonical frame is transitive (Theorem 4.27, from axiom 4),
so `h_valid` applies and gives satisfaction of `phi` at the same world --
contradiction.

Note: K4 lacks axiom T, so we use `k_truth_lemma` (from KCompleteness.lean) which
does not require axiom T, rather than `truth_lemma` (from Completeness.lean). -/
theorem k4_completeness (φ : Proposition Atom)
    (h_valid : ∀ (World : Type u) (m : Model World Atom),
      (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃) →
      ∀ w, Satisfies m w φ) :
    Derivable (@K4Axiom Atom) φ := by
  -- Step 1: Contrapositive setup
  by_contra h_not_deriv
  -- Step 2: Show {neg(phi)} is K4-consistent (prerequisite for Lindenbaum, Lemma 4.17)
  have h_cons : Modal.SetConsistent (@K4Axiom Atom)
      ({Proposition.neg φ} : Set (Proposition Atom)) := by
    intro L hL
    unfold Metalogic.Consistent
    intro ⟨d⟩
    have d_weak : DerivationTree (@K4Axiom Atom) [Proposition.neg φ]
        Proposition.bot :=
      .weakening L [Proposition.neg φ] .bot d (fun x hx => by
        have := hL x hx; simp at this
        exact List.mem_cons.mpr (Or.inl this))
    have d_dne := deductionTheorem
      (fun φ ψ => .implyK φ ψ)
      (fun φ ψ χ => .implyS φ ψ χ)
      [] (Proposition.neg φ) .bot d_weak
    let neg_phi := Proposition.neg φ
    have efq_ax : DerivationTree (@K4Axiom Atom) (Atom := Atom) []
        (Proposition.bot.imp φ) :=
      .ax [] _ (.efq φ)
    have ik : DerivationTree (@K4Axiom Atom) (Atom := Atom) []
        ((Proposition.bot.imp φ).imp
          (neg_phi.imp (Proposition.bot.imp φ))) :=
      .ax [] _ (.implyK (Proposition.bot.imp φ) neg_phi)
    have step_k := DerivationTree.modus_ponens [] _ _ ik efq_ax
    have is_ax : DerivationTree (@K4Axiom Atom) (Atom := Atom) []
        ((neg_phi.imp (Proposition.bot.imp φ)).imp
         ((neg_phi.imp Proposition.bot).imp (neg_phi.imp φ))) :=
      .ax [] _ (.implyS neg_phi Proposition.bot φ)
    have step_s := DerivationTree.modus_ponens [] _ _ is_ax step_k
    have step3 := DerivationTree.modus_ponens [] _ _ step_s d_dne
    have peirce_ax : DerivationTree (@K4Axiom Atom) (Atom := Atom) []
        (((φ.imp Proposition.bot).imp φ).imp φ) :=
      .ax [] _ (.peirce φ Proposition.bot)
    have d_phi := DerivationTree.modus_ponens [] _ _ peirce_ax step3
    exact h_not_deriv ⟨d_phi⟩
  -- Step 3: Lindenbaum extension (Lemma 4.17)
  obtain ⟨M, hM_sup, hM_mcs⟩ := modal_lindenbaum h_cons
  -- Step 4: Canonical world
  let w : CanonicalWorld (@K4Axiom Atom) := ⟨M, hM_mcs⟩
  -- Steps 5-7: k_truth_lemma + canonical_trans + contradiction
  -- Step 5: k_truth_lemma (no axiom T) instantiated at K4Axiom constructors
  -- Step 6: canonical_trans from axiom 4 (Thm 4.27)
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
      (h_valid (CanonicalWorld (@K4Axiom Atom))
        (CanonicalModel (@K4Axiom Atom))
        (canonical_trans
          (fun φ ψ => .implyK φ ψ)
          (fun φ ψ χ => .implyS φ ψ χ)
          (fun φ => .modalFour φ))
        w))

end Cslib.Logic.Modal
