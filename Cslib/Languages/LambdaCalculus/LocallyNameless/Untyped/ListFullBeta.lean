/-
Copyright (c) 2025 David Wegmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wegmann
-/


module

public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta

/-! Multiple application for untyped lambda calculus. -/

set_option linter.unusedDecidableInType false

@[expose] public section

namespace Cslib

universe u

variable {Var : Type u}

namespace LambdaCalculus.LocallyNameless.Untyped.Term

/-- A list of arguments performs a single reduction step

    [x₁, ..., xᵢ ..., xₙ] ⭢βᶠ [x₁, ..., xᵢ', ..., xₙ]

    if one of the arguments performs a single step xᵢ ⭢βᶠ xᵢ'
    and the rest of the arguments are locally closed. -/
@[scoped grind, reduction_sys "lβᶠ"]
inductive ListFullBeta : List (Term Var) → List (Term Var) → Prop where
/-- head of the list performs a single reduction step, the rest are locally closed -/
| step : N ⭢βᶠ N' → (∀ N ∈ Ns, LC N) → ListFullBeta (N :: Ns) (N' :: Ns)
/-- given a list that already contains a step, we can add locally closed terms to the front -/
| cons : LC N → ListFullBeta Ns Ns' → ListFullBeta (N :: Ns) (N :: Ns')

variable {M M' : Term Var} {Ns Ns' : List (Term Var)}

/-- A term resulting from a multi-application is locally closed if
    and only if the leftmost term and all arguments applied to it are locally closed -/
@[scoped grind ←]
lemma multiApp_lc : LC (Ns.foldl app M) ↔ LC M ∧ (∀ N ∈ Ns, LC N) := by
  induction Ns generalizing M with grind [cases LC]

/-- Just like ordinary beta reduction, the left-hand side
    of a multi-application step is locally closed -/
@[scoped grind ←]
lemma step_multiApp_l (steps : M ⭢βᶠ M') (lc_Ns : ∀ N ∈ Ns, LC N) :
    Ns.foldl app M ⭢βᶠ Ns.foldl app M' := by
  induction Ns generalizing M M' with grind

/-- Congruence lemma for multi reduction of the left most term of a multi-application -/
lemma steps_multiApp_l (steps : M ↠βᶠ M') (lc_Ns : ∀ N ∈ Ns, LC N) :
    Ns.foldl app M ↠βᶠ Ns.foldl app M' := by
  induction steps <;> grind

/-- Congruence lemma for single reduction of one of the arguments of a multi-application -/
@[scoped grind ←]
lemma step_multiApp_r (steps : Ns ⭢lβᶠ Ns') (lc_M : LC M) :
    Ns.foldl app M ⭢βᶠ Ns'.foldl app M := by
  induction steps generalizing M <;> grind

/-- Congruence lemma for multiple reduction of one of the arguments of a multi-application -/
lemma steps_multiApp_r (steps : Ns ↠lβᶠ Ns') (lc_M : LC M) :
  Ns.foldl app M ↠βᶠ Ns'.foldl app M := by
  induction steps <;> grind

lemma listFullBeta_cons_r (h : Ns ⭢lβᶠ Ns') (h_lc : ∀ M ∈ l, LC M) : (l ++ Ns) ⭢lβᶠ (l ++ Ns') := by
  induction l using List.reverseRecOn generalizing Ns Ns' with grind

lemma listFullBeta_cons_l (h : Ns ⭢lβᶠ Ns') (h_lc : ∀ M ∈ l, LC M) : (Ns ++ l) ⭢lβᶠ (Ns' ++ l) := by
  induction h with grind

set_option linter.tacticAnalysis.verifyGrindOnly false in
/-- If a term (λ M) N P_1 ... P_n reduces in a single step to Q, then
    Q must be one of the following forms:

    Q = (λ M') N P₁ ... Pₙ where M ⭢βᶠ M' or
    Q = (λ M) N' P₁ ... Pₙ where N ⭢βᶠ N' or
    Q = (λ M) N P₁' ... Pₙ' where P_i ⭢βᶠ P_i' for some i or
    Q = (M ^ N) P₁ ... Pₙ -/
lemma invert_abs_multiApp_st {Ps} {M N Q : Term Var}
  (h_red : Ps.foldl app (M.abs.app N) ⭢βᶠ Q) :
    (∃ M', M.abs ⭢βᶠ Term.abs M' ∧ Q = Ps.foldl app (M'.abs.app N)) ∨
    (∃ N', N ⭢βᶠ N' ∧ Q = Ps.foldl app (M.abs.app N')) ∨
    (∃ Ps', Ps ⭢lβᶠ Ps' ∧ Q = Ps'.foldl app (M.abs.app N)) ∨
    (Q = Ps.foldl app (M ^ N)) := by
  induction Ps using List.reverseRecOn generalizing M N Q with
  | nil => cases h_red with
            | base _ => grind
            | appL _ _ => grind
            | @appR _ _ M' _ h => cases h with
              | base h => cases h
              | @abs _ M' xs h => left
                                  exists M'
                                  apply Xi.abs at h
                                  grind
  | append_singleton Ps P ih =>
    rw [List.foldl_concat] at h_red
    cases h_red with
    | @appL _ _ P' _ P_P' =>
      have : (Ps ++ [P]) ⭢lβᶠ Ps ++ [P'] := by apply listFullBeta_cons_r (.step P_P' ?_) <;> grind
      grind
    | appR _ h =>
      have {Ps'} (h : Ps ⭢lβᶠ Ps') : (Ps ++ [P]) ⭢lβᶠ Ps' ++ [P] := listFullBeta_cons_l h (by grind)
      grind
    | base => induction Ps using List.reverseRecOn with grind


/-- If a term (λ M) N P₁ ... Pₙ reduces in multiple steps to Q, then either Q if of the form

      Q = (λ M') N' P'₁ ... P'ₙ

      or

    we first reach an intermediate term of this shape,

      (λ M) N P₁ ... Pₙ ↠βᶠ (λ M') N' P'₁ ... P'ₙ

      then perform a beta reduction and reduce further to Q

      (λ M') N' P'₁ ... P'ₙ ↠βᶠ M' ^ N' P'_₁ ... P'_ₙ ↠βᶠ Q

   where M ↠βᶠ M' and N ↠βᶠ N' and P_i ↠βᶠ P_i' for all i -/
lemma invert_abs_multiApp_mst {Ps} {M N Q : Term Var}
  (h_red : Ps.foldl app (M.abs.app N) ↠βᶠ Q) :
    ∃ M' N' Ns', M.abs ↠βᶠ Term.abs M' ∧ N ↠βᶠ N' ∧ Ps ↠lβᶠ Ns' ∧
                 (Q = Ns'.foldl app (M'.abs.app N') ∨
     (Ps.foldl app (M.abs.app N) ↠βᶠ Ns'.foldl app (M' ^ N') ∧
                                      Ns'.foldl app (M' ^ N') ↠βᶠ Q)) := by
  induction h_red with
  | refl => grind
  | tail _ step ih =>
    obtain ⟨_, _, _, _, _, _, h⟩ := ih
    rcases h with heq | _
    · subst heq
      grind [invert_abs_multiApp_st step]
    · grind [Relation.ReflTransGen.single]

variable [DecidableEq Var] [HasFresh Var]

/-- Just like ordinary beta reduction, the right-hand side
    of a multi-application step is locally closed -/
lemma multiApp_step_lc_r (step : Ns ⭢lβᶠ Ns') : ∀ N ∈ Ns', LC N := by
  induction step <;> grind [FullBeta.step_lc_r]

/-- Just like ordinary beta reduction, multiple steps of a argument list preserves local closure -/
lemma multiApp_steps_lc (step : Ns ↠lβᶠ Ns') (H : ∀ N ∈ Ns, LC N) : ∀ N ∈ Ns', LC N := by
  induction step <;> grind [FullBeta.step_lc_r, multiApp_step_lc_r]

end LambdaCalculus.LocallyNameless.Untyped.Term

end Cslib
