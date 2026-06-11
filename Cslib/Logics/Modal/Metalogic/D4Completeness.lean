/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.Completeness
public import Cslib.Logics.Modal.Metalogic.DCompleteness

/-! # Completeness Theorem for Modal Logic D4 (KD4)

This module proves completeness for modal logic D4 over serial + transitive
Kripke frames via the canonical model construction (completeness-via-canonicity).

D4 = K + D + 4 contains axiom D (seriality) and axiom 4 (transitivity) but
NOT axiom T (reflexivity). Therefore this proof uses:
- `truth_lemma_d` (D-specific truth lemma, NOT `truth_lemma` which requires T)
- `canonical_serial` (from DCompleteness.lean, using axiom D)
- `canonical_trans` (from Completeness.lean, using axiom 4)

## Main Results

- `d4_completeness`: If `phi` is valid over all serial + transitive frames,
  then `phi` is D4-derivable (Blackburn Theorem 4.29 pattern applied to D+4).

## References

* Blackburn, de Rijke, Venema, "Modal Logic" (2002), Chapter 4
  - Theorem 4.27 (axiom 4 canonical for transitivity)
  - Theorem 4.28 clause 3 (axiom D canonical for seriality)
  - Theorem 4.29 pattern (combining canonical properties)
  - Lemma 4.21 (Truth Lemma)
  - Proposition 4.12 (Completeness criterion)
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

universe u
variable {Atom : Type u}

/-! ## D4 Completeness (Blackburn Theorem 4.29 pattern for D+4) -/

/-- **Completeness Theorem for Modal Logic D4** (Blackburn Theorem 4.29 pattern):

If `phi` is valid over all serial + transitive frames, then `phi` is derivable
from the D4 axiom set.

The proof is by contrapositive (Canonical Model Theorem, Blackburn Theorem 4.22):
assume `phi` is not D4-derivable, then `{neg phi}` is D4-consistent, extend it to
an MCS via Lindenbaum's Lemma (Lemma 4.17), and show `neg phi` is satisfied in the
canonical model. The canonical frame is serial (Theorem 4.28, clause 3, from
axiom D) and transitive (Theorem 4.27, from axiom 4), so `h_valid` applies and
gives satisfaction of `phi` at the same world -- contradiction.

CRITICAL: Uses `truth_lemma_d` (D-specific) because D4 lacks axiom T. -/
theorem d4_completeness (φ : Proposition Atom)
    (h_valid : ∀ (World : Type u) (m : Model World Atom),
      Relation.Serial m.r →
      (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃) →
      ∀ w, Satisfies m w φ) :
    Derivable (@D4Axiom Atom) φ := by
  -- Step 1: Contrapositive setup
  by_contra h_not_deriv
  -- Step 2: Show {neg(phi)} is D4-consistent (prerequisite for Lindenbaum, Lemma 4.17)
  have h_cons : Modal.SetConsistent (@D4Axiom Atom)
      ({Proposition.neg φ} : Set (Proposition Atom)) := by
    intro L hL
    unfold Metalogic.Consistent
    intro ⟨d⟩
    have d_weak : DerivationTree (@D4Axiom Atom) [Proposition.neg φ]
        Proposition.bot :=
      .weakening L [Proposition.neg φ] .bot d (fun x hx => by
        have := hL x hx; simp at this
        exact List.mem_cons.mpr (Or.inl this))
    have d_dne := deductionTheorem
      (fun φ ψ => .implyK φ ψ)
      (fun φ ψ χ => .implyS φ ψ χ)
      [] (Proposition.neg φ) .bot d_weak
    let neg_phi := Proposition.neg φ
    have efq_ax : DerivationTree (@D4Axiom Atom) (Atom := Atom) []
        (Proposition.bot.imp φ) :=
      .ax [] _ (.efq φ)
    have ik : DerivationTree (@D4Axiom Atom) (Atom := Atom) []
        ((Proposition.bot.imp φ).imp
          (neg_phi.imp (Proposition.bot.imp φ))) :=
      .ax [] _ (.implyK (Proposition.bot.imp φ) neg_phi)
    have step_k := DerivationTree.modus_ponens [] _ _ ik efq_ax
    have is_ax : DerivationTree (@D4Axiom Atom) (Atom := Atom) []
        ((neg_phi.imp (Proposition.bot.imp φ)).imp
         ((neg_phi.imp Proposition.bot).imp (neg_phi.imp φ))) :=
      .ax [] _ (.implyS neg_phi Proposition.bot φ)
    have step_s := DerivationTree.modus_ponens [] _ _ is_ax step_k
    have step3 := DerivationTree.modus_ponens [] _ _ step_s d_dne
    have peirce_ax : DerivationTree (@D4Axiom Atom) (Atom := Atom) []
        (((φ.imp Proposition.bot).imp φ).imp φ) :=
      .ax [] _ (.peirce φ Proposition.bot)
    have d_phi := DerivationTree.modus_ponens [] _ _ peirce_ax step3
    exact h_not_deriv ⟨d_phi⟩
  -- Step 3: Lindenbaum extension (Lemma 4.17)
  obtain ⟨M, hM_sup, hM_mcs⟩ := modal_lindenbaum h_cons
  -- Step 4: Canonical world
  let w : CanonicalWorld (@D4Axiom Atom) := ⟨M, hM_mcs⟩
  -- Steps 5-7: Truth Lemma + frame properties + contradiction
  -- Step 5: truth_lemma_d (D-specific, Lemma 4.21) instantiated at D4Axiom constructors
  -- Step 6: Frame properties via Theorems 4.27 + 4.28.3 (D+4 combination):
  --   canonical_serial from axiom D (Thm 4.28, clause 3)
  --   canonical_trans from axiom 4 (Thm 4.27)
  -- Step 7: Contradiction via mcs_not_mem_of_neg
  have h_serial : Relation.Serial (CanonicalModel (@D4Axiom Atom)).r := by
    constructor
    intro S
    exact canonical_serial
      (fun φ ψ => .implyK φ ψ)
      (fun φ ψ χ => .implyS φ ψ χ)
      (fun φ => .efq φ)
      (fun φ ψ => .modalK φ ψ)
      (fun φ => .modalD φ)
      S
  exact mcs_not_mem_of_neg
    (fun φ ψ => .implyK φ ψ)
    (fun φ ψ χ => .implyS φ ψ χ)
    hM_mcs (hM_sup (Set.mem_singleton _))
    ((truth_lemma_d
      (fun φ ψ => .implyK φ ψ)
      (fun φ ψ χ => .implyS φ ψ χ)
      (fun φ => .efq φ)
      (fun φ ψ => .peirce φ ψ)
      (fun φ ψ => .modalK φ ψ)
      (fun φ => .modalD φ)
      w φ).mp
      (h_valid (CanonicalWorld (@D4Axiom Atom))
        (CanonicalModel (@D4Axiom Atom))
        h_serial
        (canonical_trans
          (fun φ ψ => .implyK φ ψ)
          (fun φ ψ χ => .implyS φ ψ χ)
          (fun φ => .modalFour φ))
        w))

end Cslib.Logic.Modal
