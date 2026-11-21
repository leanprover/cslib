/-
Copyright (c) 2026 Maximiliano Onofre Martínez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maximiliano Onofre Martínez
-/

module

public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.StandardReduction

/-! # The Leftmost Reduction Theorem

## Reference

* [M. Copes, *A machine-checked proof of the Standardization Theorem in λ-calculus*][Copes2018]

-/

@[expose] public section

set_option linter.unusedDecidableInType false

namespace Cslib

universe u

variable {Var : Type u}

namespace LambdaCalculus.LocallyNameless.Untyped.Term

/-- A term is in normal form when it contains no β-redexes. -/
@[grind]
def BetaNormal (m : Term Var) : Prop := countRedexes m = 0

/-- Leftmost reduction: a β-reduction contracting the redex at position 0. -/
@[reduction_sys "ℓ"]
abbrev Leftmost : Term Var → Term Var → Prop := BetaAt 0

variable {L L' M M' N : Term Var} {i : Nat}

/-- In a normal-form application, both sides are normal and the operator is not an
    abstraction. -/
lemma BetaNormal.app_inv (h : BetaNormal (app L M)) :
    ¬IsAbs L ∧ BetaNormal L ∧ BetaNormal M := by
  cases L <;> grind [countRedexes]

/-- The body of a normal-form abstraction opens to a normal form. -/
lemma BetaNormal.abs_open {x : Var} (h : BetaNormal (abs M)) : BetaNormal (M ^ fvar x) := by
  rw [BetaNormal, countRedexes_open_fvar]
  exact h

/-- The left side of a leftmost reduction step is locally closed. -/
@[scoped grind →]
lemma Leftmost.step_lc_l (h : M ⭢ℓ N) : LC M :=
  BetaAt.lc_l h

/-- Leftmost reduction preserves being an abstraction. -/
lemma Leftmost.steps_isAbs_r (h : M ↠ℓ N) (ha : IsAbs M) : IsAbs N := by
  induction h with
  | refl => exact ha
  | tail _ step ih => exact step.isAbs_r ih

/-- Left congruence for leftmost reduction, provided the target is not an abstraction. -/
lemma Leftmost.steps_app_l_cong (h : L ↠ℓ L') (lc : LC M) (hna : ¬IsAbs L') :
    app L M ↠ℓ app L' M := by
  induction h
  case refl => rfl
  case tail P _ _ step ih =>
    have hnb : ¬IsAbs P := mt step.isAbs_r hna
    exact (ih hnb).tail (step.appNoAbsL lc hnb)

/-- Reducing the operand across a non-abstraction normal form keeps the position. -/
lemma BetaAt.app_r_cong (h : BetaAt i M M') (lc : LC L) (hL : BetaNormal L) (hna : ¬IsAbs L) :
    BetaAt i (app L M) (app L M') := by
  have := h.appNoAbsR lc hna
  rwa [hL] at this

/-- Right congruence for leftmost reduction, provided the operator is a non-abstraction
    normal form. -/
lemma Leftmost.steps_app_r_cong (h : M ↠ℓ M') (lc : LC L) (hL : BetaNormal L) (hna : ¬IsAbs L) :
    app L M ↠ℓ app L M' := by
  induction h with
  | refl => rfl
  | tail _ step ih => exact ih.tail (step.app_r_cong lc hL hna)

/-- Call-by-Name reduction is contained in leftmost reduction. -/
lemma Leftmost.of_cbn (h : M ↠ₙ N) : M ↠ℓ N := by
  induction h with
  | refl => rfl
  | tail _ step ih => exact ih.tail (BetaAt.of_cbn_step step)

variable [HasFresh Var]

/-- The right side of a leftmost reduction step is locally closed. -/
@[scoped grind →]
lemma Leftmost.step_lc_r (h : M ⭢ℓ N) : LC N :=
  BetaAt.lc_r h

/-- Either both endpoints of a leftmost reduction are locally closed, or they are equal. -/
lemma Leftmost.steps_lc_or_rfl (h : M ↠ℓ M') : (LC M ∧ LC M') ∨ M = M' := by
  induction h with
  | refl => exact .inr rfl
  | tail _ step ih =>
    rcases ih with ⟨lc_M, _⟩ | rfl
    · exact .inl ⟨lc_M, step.lc_r⟩
    · exact .inl ⟨step.lc_l, step.lc_r⟩

/-- Leftmost reduction preserves local closure. -/
lemma Leftmost.steps_lc_r (h : M ↠ℓ M') (lc : LC M) : LC M' := by
  induction h with
  | refl => exact lc
  | tail _ step _ => exact step.lc_r

/-- Congruence for leftmost reduction on applications whose reduced operator is a
    non-abstraction normal form. -/
lemma Leftmost.steps_app_cong (hL : L ↠ℓ L') (hM : M ↠ℓ M')
    (lc_L : LC L) (lc_M : LC M) (hnf : BetaNormal L') (hna : ¬IsAbs L') :
    app L M ↠ℓ app L' M' :=
  (steps_app_l_cong hL lc_M hna).trans (steps_app_r_cong hM (steps_lc_r hL lc_L) hnf hna)

variable [DecidableEq Var]

/-- Leftmost reduction is preserved by closing a variable and abstracting. -/
lemma Leftmost.steps_abs_close {x : Var} (h : M ↠ℓ M') :
    (M⟦0 ↜ x⟧.abs) ↠ℓ (M'⟦0 ↜ x⟧.abs) := by
  induction h with
  | refl => rfl
  | tail _ step ih => exact ih.tail step.abs_close

/-- Cofinite congruence rule for leftmost reduction under an abstraction. -/
lemma Leftmost.steps_abs_cong (xs : Finset Var)
    (cofin : ∀ x ∉ xs, (M ^ fvar x) ↠ℓ (M' ^ fvar x)) :
    abs M ↠ℓ abs M' := by
  have ⟨w, _⟩ := fresh_exists <| free_union [fv] Var
  rw [open_close w M 0 (by grind), open_close w M' 0 (by grind)]
  exact steps_abs_close (cofin w (by grind))

/-- A standard reduction to a normal form is a leftmost reduction. -/
theorem Leftmost.of_standard (h : M ⭢ₛ N) (hn : BetaNormal N) : M ↠ℓ N := by
  induction h
  case fvar x => rfl
  case app std_L std_M ihL ihM =>
    have ⟨hna, hL', hM'⟩ := hn.app_inv
    exact steps_app_cong (ihL hL') (ihM hM') std_L.lc_l std_M.lc_l hL' hna
  case abs xs _ ih =>
    apply steps_abs_cong xs
    intro x hx
    exact ih x hx hn.abs_open
  case rdx M N M' _ lc_M lc_N cbn std_P ih =>
    have s1 : M.app N ↠ℓ M'.abs.app N := of_cbn (CBN.steps_app_l_cong cbn lc_N)
    have s2 : M'.abs.app N ⭢ℓ M' ^ N := .outer (CBN.steps_lc_r lc_M cbn) lc_N
    exact (s1.tail s2).trans (ih hn)

/-- The leftmost reduction theorem: if a term β-reduces to a normal form, then leftmost
    reduction reaches it. -/
theorem Leftmost.normalization (lc : LC M) (h : M ↠βᶠ N) (hn : BetaNormal N) : M ↠ℓ N :=
  of_standard (.standardization lc h) hn

end LambdaCalculus.LocallyNameless.Untyped.Term

end Cslib
