/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Bimodal.Metalogic.Algebraic.LindenbaumQuotient
public import Mathlib.Order.BooleanAlgebra.Defs
public import Mathlib.Order.BooleanAlgebra.Basic

/-!
# Boolean Algebra Structure on Lindenbaum Algebra

This module proves that the Lindenbaum-Tarski algebra is a `BooleanAlgebra`.

## Main Results

- `LindenbaumAlg` is a `BooleanAlgebra`
- Order: `[phi] <= [psi] iff derives phi psi`
- Operations are well-defined on the quotient

## References

* Ported from BimodalLogic/Theories/Bimodal/Metalogic/Algebraic/BooleanStructure.lean
-/

set_option linter.style.emptyLine false
set_option linter.style.longLine false
set_option maxHeartbeats 400000

@[expose] public section

namespace Cslib.Logic.Bimodal.Metalogic.Algebraic.BooleanStructure

open Cslib.Logic.Bimodal
open Cslib.Logic.Bimodal.Metalogic.Algebraic.LindenbaumQuotient

variable {Atom : Type*}

/-!
## Order Structure

The order on the Lindenbaum algebra is defined by derivability.
-/

/-- Order on the Lindenbaum algebra: `⟦φ⟧ ≤ ⟦ψ⟧` iff `φ` derives `ψ`. -/
instance instLELindenbaumAlg : LE (LindenbaumAlg Atom) where
  le := Quotient.lift₂ (fun φ ψ => Derives φ ψ)
    (fun φ₁ φ₂ ψ₁ ψ₂ hφ hψ => by
      apply propext
      constructor
      · intro h
        exact derives_trans hφ.2 (derives_trans h hψ.1)
      · intro h
        exact derives_trans hφ.1 (derives_trans h hψ.2))

/-- Reflexivity of the Lindenbaum order. -/
theorem le_refl_quot (a : LindenbaumAlg Atom) : a ≤ a := by
  induction a using Quotient.ind
  exact derives_refl _

/-- Transitivity of the Lindenbaum order. -/
theorem le_trans_quot {a b c : LindenbaumAlg Atom} (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  induction a using Quotient.ind
  induction b using Quotient.ind
  induction c using Quotient.ind
  exact derives_trans hab hbc

/-- Antisymmetry of the Lindenbaum order: mutual derivability implies provable equivalence. -/
theorem le_antisymm_quot {a b : LindenbaumAlg Atom} (hab : a ≤ b) (hba : b ≤ a) : a = b := by
  induction a using Quotient.ind
  induction b using Quotient.ind
  exact Quotient.sound ⟨hab, hba⟩

instance : Preorder (LindenbaumAlg Atom) where
  le_refl := le_refl_quot
  le_trans := fun _ _ _ => le_trans_quot

instance : PartialOrder (LindenbaumAlg Atom) where
  le_antisymm := fun _ _ => le_antisymm_quot

/-!
## Lattice Structure
-/

/-- Top element of the Lindenbaum algebra lattice. -/
instance instTopLindenbaumAlg : Top (LindenbaumAlg Atom) where
  top := top_quot

/-- Bottom element of the Lindenbaum algebra lattice. -/
instance instBotLindenbaumAlg : Bot (LindenbaumAlg Atom) where
  bot := bot_quot

/-- Left projection for infimum: `a ∧ b ≤ a`. -/
theorem inf_le_left_quot (a b : LindenbaumAlg Atom) : and_quot a b ≤ a := by
  induction a using Quotient.ind
  induction b using Quotient.ind
  rename_i φ ψ
  show Derives (φ.and ψ) φ
  exact ⟨Metalogic.Core.deduction_theorem [] (φ.and ψ) φ
    (Theorems.Propositional.lce φ ψ)⟩

/-- Right projection for infimum: `a ∧ b ≤ b`. -/
theorem inf_le_right_quot (a b : LindenbaumAlg Atom) : and_quot a b ≤ b := by
  induction a using Quotient.ind
  induction b using Quotient.ind
  rename_i φ ψ
  show Derives (φ.and ψ) ψ
  exact ⟨Metalogic.Core.deduction_theorem [] (φ.and ψ) ψ
    (Theorems.Propositional.rce φ ψ)⟩

/-- Greatest lower bound property: if `a ≤ b` and `a ≤ c`, then `a ≤ b ∧ c`. -/
theorem le_inf_quot {a b c : LindenbaumAlg Atom} (hab : a ≤ b) (hac : a ≤ c) : a ≤ and_quot b c := by
  induction a using Quotient.ind
  induction b using Quotient.ind
  induction c using Quotient.ind
  rename_i φ ψ χ
  show Derives φ (ψ.and χ)
  have h_ab : Derives φ ψ := hab
  have h_ac : Derives φ χ := hac
  obtain ⟨d_ab⟩ := h_ab
  obtain ⟨d_ac⟩ := h_ac
  exact ⟨Theorems.Combinators.combine_imp_conj d_ab d_ac⟩

/-- Left injection for supremum: `a ≤ a ∨ b`. -/
theorem le_sup_left_quot (a b : LindenbaumAlg Atom) : a ≤ or_quot a b := by
  induction a using Quotient.ind
  induction b using Quotient.ind
  rename_i φ ψ
  show Derives φ (φ.or ψ)
  unfold Derives
  unfold Formula.or
  exact ⟨Theorems.Propositional.raa φ ψ⟩

/-- Right injection for supremum: `b ≤ a ∨ b`. -/
theorem le_sup_right_quot (a b : LindenbaumAlg Atom) : b ≤ or_quot a b := by
  induction a using Quotient.ind
  induction b using Quotient.ind
  rename_i φ ψ
  show Derives ψ (φ.or ψ)
  unfold Derives
  have d_s : DerivationTree FrameClass.Base [] (ψ.imp (φ.neg.imp ψ)) :=
    DerivationTree.axiom [] _ (Axiom.imp_s ψ φ.neg) trivial
  exact ⟨d_s⟩

/-- Least upper bound property: if `a ≤ c` and `b ≤ c`, then `a ∨ b ≤ c`. -/
theorem sup_le_quot {a b c : LindenbaumAlg Atom} (hac : a ≤ c) (hbc : b ≤ c) : or_quot a b ≤ c := by
  induction a using Quotient.ind
  induction b using Quotient.ind
  induction c using Quotient.ind
  rename_i φ ψ χ
  show Derives (φ.or ψ) χ
  have h_ac : Derives φ χ := hac
  have h_bc : Derives ψ χ := hbc
  obtain ⟨d_ac⟩ := h_ac
  obtain ⟨d_bc⟩ := h_bc
  unfold Derives Formula.or
  have b1 : DerivationTree FrameClass.Base [] ((ψ.imp χ).imp ((φ.neg.imp ψ).imp (φ.neg.imp χ))) :=
    Theorems.Combinators.b_combinator
  have neg_phi_to_chi_given_disj : DerivationTree FrameClass.Base [] ((φ.neg.imp ψ).imp (φ.neg.imp χ)) :=
    DerivationTree.modus_ponens [] _ _ b1 d_bc
  have cm : DerivationTree FrameClass.Base [] ((φ.imp χ).imp ((φ.neg.imp χ).imp χ)) :=
    Theorems.Propositional.classical_merge φ χ
  have step1 : DerivationTree FrameClass.Base [] ((φ.neg.imp χ).imp χ) :=
    DerivationTree.modus_ponens [] _ _ cm d_ac
  have b2 : DerivationTree FrameClass.Base [] (((φ.neg.imp χ).imp χ).imp (((φ.neg.imp ψ).imp (φ.neg.imp χ)).imp ((φ.neg.imp ψ).imp χ))) :=
    Theorems.Combinators.b_combinator
  have step2 : DerivationTree FrameClass.Base [] (((φ.neg.imp ψ).imp (φ.neg.imp χ)).imp ((φ.neg.imp ψ).imp χ)) :=
    DerivationTree.modus_ponens [] _ _ b2 step1
  exact ⟨DerivationTree.modus_ponens [] _ _ step2 neg_phi_to_chi_given_disj⟩

/-- Bottom is below everything: `⊥ ≤ a` (via EFQ). -/
theorem bot_le_quot (a : LindenbaumAlg Atom) : ⊥ ≤ a := by
  induction a using Quotient.ind
  rename_i φ
  show Derives Formula.bot φ
  exact ⟨DerivationTree.axiom [] _ (Axiom.efq φ) trivial⟩

/-- Everything is below top: `a ≤ ⊤`. -/
theorem le_top_quot (a : LindenbaumAlg Atom) : a ≤ ⊤ := by
  induction a using Quotient.ind
  rename_i φ
  show Derives φ (Formula.bot.imp Formula.bot)
  have d_id : DerivationTree FrameClass.Base [] ((Formula.bot : Formula Atom).imp Formula.bot) :=
    Theorems.Combinators.identity Formula.bot
  have d_s : DerivationTree FrameClass.Base (Atom := Atom) [] (((Formula.bot).imp Formula.bot).imp (φ.imp ((Formula.bot).imp Formula.bot))) :=
    DerivationTree.axiom [] _ (Axiom.imp_s ((Formula.bot : Formula Atom).imp Formula.bot) φ) trivial
  exact ⟨DerivationTree.modus_ponens [] _ _ d_s d_id⟩

/-- Distributivity: `(a ∨ b) ∧ (a ∨ c) ≤ a ∨ (b ∧ c)`. -/
theorem le_sup_inf_quot (a b c : LindenbaumAlg Atom) :
    and_quot (or_quot a b) (or_quot a c) ≤ or_quot a (and_quot b c) := by
  induction a using Quotient.ind
  induction b using Quotient.ind
  induction c using Quotient.ind
  rename_i φ ψ χ
  show Derives ((φ.or ψ).and (φ.or χ)) (φ.or (ψ.and χ))
  unfold Derives
  -- We inline what was P and Q in the source
  -- P = (φ.or ψ).and (φ.or χ), Q = φ.or (ψ.and χ)
  have di_left : DerivationTree FrameClass.Base [] (φ.imp (φ.or (ψ.and χ))) :=
    Metalogic.Core.deduction_theorem [] φ (φ.or (ψ.and χ)) (Theorems.Propositional.ldi φ (ψ.and χ))

  have di_right_conj : DerivationTree FrameClass.Base [] ((ψ.and χ).imp (φ.or (ψ.and χ))) :=
    Metalogic.Core.deduction_theorem [] (ψ.and χ) (φ.or (ψ.and χ)) (Theorems.Propositional.rdi φ (ψ.and χ))

  have lce_p : DerivationTree FrameClass.Base [] (((φ.or ψ).and (φ.or χ)).imp (φ.or ψ)) :=
    Theorems.Propositional.lce_imp (φ.or ψ) (φ.or χ)
  have rce_p : DerivationTree FrameClass.Base [] (((φ.or ψ).and (φ.or χ)).imp (φ.or χ)) :=
    Theorems.Propositional.rce_imp (φ.or ψ) (φ.or χ)

  -- lce_p : P → (¬φ → ψ) and rce_p : P → (¬φ → χ) via or definition
  have p_to_neg_phi_psi := lce_p
  have p_to_neg_phi_chi := rce_p

  have h_ctx : DerivationTree FrameClass.Base [φ.neg, (φ.or ψ).and (φ.or χ)] (ψ.and χ) := by
    have h_p : DerivationTree FrameClass.Base [φ.neg, (φ.or ψ).and (φ.or χ)] ((φ.or ψ).and (φ.or χ)) :=
      DerivationTree.assumption _ _ (by simp)
    have h_neg_phi : DerivationTree FrameClass.Base [φ.neg, (φ.or ψ).and (φ.or χ)] φ.neg :=
      DerivationTree.assumption _ _ (by simp)
    have h1 : DerivationTree FrameClass.Base [φ.neg, (φ.or ψ).and (φ.or χ)] (((φ.or ψ).and (φ.or χ)).imp (φ.neg.imp ψ)) :=
      DerivationTree.weakening [] _ _ p_to_neg_phi_psi (List.nil_subset _)
    have h2 : DerivationTree FrameClass.Base [φ.neg, (φ.or ψ).and (φ.or χ)] (φ.neg.imp ψ) :=
      DerivationTree.modus_ponens _ _ _ h1 h_p
    have h_psi : DerivationTree FrameClass.Base [φ.neg, (φ.or ψ).and (φ.or χ)] ψ :=
      DerivationTree.modus_ponens _ _ _ h2 h_neg_phi
    have h3 : DerivationTree FrameClass.Base [φ.neg, (φ.or ψ).and (φ.or χ)] (((φ.or ψ).and (φ.or χ)).imp (φ.neg.imp χ)) :=
      DerivationTree.weakening [] _ _ p_to_neg_phi_chi (List.nil_subset _)
    have h4 : DerivationTree FrameClass.Base [φ.neg, (φ.or ψ).and (φ.or χ)] (φ.neg.imp χ) :=
      DerivationTree.modus_ponens _ _ _ h3 h_p
    have h_chi : DerivationTree FrameClass.Base [φ.neg, (φ.or ψ).and (φ.or χ)] χ :=
      DerivationTree.modus_ponens _ _ _ h4 h_neg_phi
    have pair : DerivationTree FrameClass.Base [] (ψ.imp (χ.imp (ψ.and χ))) :=
      Theorems.Combinators.pairing ψ χ
    have pair_ctx : DerivationTree FrameClass.Base [φ.neg, (φ.or ψ).and (φ.or χ)] (ψ.imp (χ.imp (ψ.and χ))) :=
      DerivationTree.weakening [] _ _ pair (List.nil_subset _)
    have step1 : DerivationTree FrameClass.Base [φ.neg, (φ.or ψ).and (φ.or χ)] (χ.imp (ψ.and χ)) :=
      DerivationTree.modus_ponens _ _ _ pair_ctx h_psi
    exact DerivationTree.modus_ponens _ _ _ step1 h_chi

  have h_ctx2 : DerivationTree FrameClass.Base [(φ.or ψ).and (φ.or χ)] (φ.neg.imp (ψ.and χ)) :=
    Metalogic.Core.deduction_theorem [(φ.or ψ).and (φ.or χ)] φ.neg (ψ.and χ) h_ctx

  have di_right_ctx : DerivationTree FrameClass.Base [(φ.or ψ).and (φ.or χ)] ((ψ.and χ).imp (φ.or (ψ.and χ))) :=
    DerivationTree.weakening [] _ _ di_right_conj (List.nil_subset _)
  have b_inst : DerivationTree FrameClass.Base [] (((ψ.and χ).imp (φ.or (ψ.and χ))).imp ((φ.neg.imp (ψ.and χ)).imp (φ.neg.imp (φ.or (ψ.and χ))))) :=
    Theorems.Combinators.b_combinator
  have b_ctx : DerivationTree FrameClass.Base [(φ.or ψ).and (φ.or χ)] (((ψ.and χ).imp (φ.or (ψ.and χ))).imp ((φ.neg.imp (ψ.and χ)).imp (φ.neg.imp (φ.or (ψ.and χ))))) :=
    DerivationTree.weakening [] _ _ b_inst (List.nil_subset _)
  have step2 : DerivationTree FrameClass.Base [(φ.or ψ).and (φ.or χ)] ((φ.neg.imp (ψ.and χ)).imp (φ.neg.imp (φ.or (ψ.and χ)))) :=
    DerivationTree.modus_ponens _ _ _ b_ctx di_right_ctx
  have h_neg_phi_Q : DerivationTree FrameClass.Base [(φ.or ψ).and (φ.or χ)] (φ.neg.imp (φ.or (ψ.and χ))) :=
    DerivationTree.modus_ponens _ _ _ step2 h_ctx2

  have di_left_ctx : DerivationTree FrameClass.Base [(φ.or ψ).and (φ.or χ)] (φ.imp (φ.or (ψ.and χ))) :=
    DerivationTree.weakening [] _ _ di_left (List.nil_subset _)

  have cm : DerivationTree FrameClass.Base [] ((φ.imp (φ.or (ψ.and χ))).imp ((φ.neg.imp (φ.or (ψ.and χ))).imp (φ.or (ψ.and χ)))) :=
    Theorems.Propositional.classical_merge φ (φ.or (ψ.and χ))
  have cm_ctx : DerivationTree FrameClass.Base [(φ.or ψ).and (φ.or χ)] ((φ.imp (φ.or (ψ.and χ))).imp ((φ.neg.imp (φ.or (ψ.and χ))).imp (φ.or (ψ.and χ)))) :=
    DerivationTree.weakening [] _ _ cm (List.nil_subset _)
  have step3 : DerivationTree FrameClass.Base [(φ.or ψ).and (φ.or χ)] ((φ.neg.imp (φ.or (ψ.and χ))).imp (φ.or (ψ.and χ))) :=
    DerivationTree.modus_ponens _ _ _ cm_ctx di_left_ctx
  have h_Q : DerivationTree FrameClass.Base [(φ.or ψ).and (φ.or χ)] (φ.or (ψ.and χ)) :=
    DerivationTree.modus_ponens _ _ _ step3 h_neg_phi_Q

  exact ⟨Metalogic.Core.deduction_theorem [] ((φ.or ψ).and (φ.or χ)) (φ.or (ψ.and χ)) h_Q⟩

/-!
## Complement and Boolean Algebra
-/

/-- Complement axiom: `a ∧ ¬a ≤ ⊥`. -/
theorem inf_compl_le_bot_quot (a : LindenbaumAlg Atom) : and_quot a (neg_quot a) ≤ ⊥ := by
  induction a using Quotient.ind
  rename_i φ
  show Derives (φ.and φ.neg) Formula.bot
  unfold Derives
  have h_conj_ctx : DerivationTree FrameClass.Base [φ.and φ.neg] (φ.and φ.neg) := by
    apply DerivationTree.assumption
    simp
  have h_phi : DerivationTree FrameClass.Base [φ.and φ.neg] φ := by
    apply DerivationTree.modus_ponens [φ.and φ.neg] _ _
    · apply DerivationTree.weakening [] [φ.and φ.neg]
      · exact Theorems.Propositional.lce_imp φ φ.neg
      · intro; simp
    · exact h_conj_ctx
  have h_neg_phi : DerivationTree FrameClass.Base [φ.and φ.neg] φ.neg := by
    apply DerivationTree.modus_ponens [φ.and φ.neg] _ _
    · apply DerivationTree.weakening [] [φ.and φ.neg]
      · exact Theorems.Propositional.rce_imp φ φ.neg
      · intro; simp
    · exact h_conj_ctx
  have h_bot : DerivationTree FrameClass.Base [φ.and φ.neg] Formula.bot :=
    DerivationTree.modus_ponens [φ.and φ.neg] φ Formula.bot h_neg_phi h_phi
  exact ⟨Metalogic.Core.deduction_theorem [] (φ.and φ.neg) Formula.bot h_bot⟩

/-- Complement axiom: `⊤ ≤ a ∨ ¬a` (law of excluded middle). -/
theorem top_le_sup_compl_quot (a : LindenbaumAlg Atom) : ⊤ ≤ or_quot a (neg_quot a) := by
  induction a using Quotient.ind
  rename_i φ
  show Derives (Formula.bot.imp Formula.bot) (φ.or φ.neg)
  unfold Derives
  have h_lem : DerivationTree FrameClass.Base [] (φ.or φ.neg) := Theorems.Propositional.lem φ
  have h_s : DerivationTree FrameClass.Base [] ((φ.or φ.neg).imp ((Formula.bot.imp Formula.bot).imp (φ.or φ.neg))) :=
    DerivationTree.axiom [] _ (Axiom.imp_s (φ.or φ.neg) (Formula.bot.imp Formula.bot)) trivial
  exact ⟨DerivationTree.modus_ponens [] _ _ h_s h_lem⟩

/-- Commutativity of disjunction in the Lindenbaum algebra. -/
theorem sup_comm_quot (a b : LindenbaumAlg Atom) : or_quot a b = or_quot b a := by
  apply le_antisymm
  · apply sup_le_quot
    · exact le_sup_right_quot b a
    · exact le_sup_left_quot b a
  · apply sup_le_quot
    · exact le_sup_right_quot a b
    · exact le_sup_left_quot a b

noncomputable instance : BooleanAlgebra (LindenbaumAlg Atom) where
  sup := or_quot
  inf := and_quot
  compl := neg_quot
  sdiff := fun a b => and_quot a (neg_quot b)
  himp := fun a b => or_quot (neg_quot a) b
  le_sup_left := le_sup_left_quot
  le_sup_right := le_sup_right_quot
  sup_le := fun _ _ _ => sup_le_quot
  inf_le_left := inf_le_left_quot
  inf_le_right := inf_le_right_quot
  le_inf := fun _ _ _ => le_inf_quot
  le_top := le_top_quot
  bot_le := bot_le_quot
  le_sup_inf := le_sup_inf_quot
  inf_compl_le_bot := inf_compl_le_bot_quot
  top_le_sup_compl := top_le_sup_compl_quot
  sdiff_eq := fun _ _ => rfl
  himp_eq := fun a b => sup_comm_quot _ _

end Cslib.Logic.Bimodal.Metalogic.Algebraic.BooleanStructure
