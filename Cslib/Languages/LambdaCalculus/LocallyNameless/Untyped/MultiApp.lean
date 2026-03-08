/-
Copyright (c) 2025 David Wegmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wegmann
-/


module


public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta

set_option linter.unusedDecidableInType false

@[expose] public section

namespace Cslib

universe u

variable {Var : Type u}

namespace LambdaCalculus.LocallyNameless.Untyped.Term

/-
  multiApp f [x₁, x₂, ..., xₙ] applies the arguments x₁, x₂, ..., xₙ
  to f in left-associative order, i.e. as (((f x₁) x₂) ... xₙ).
-/
@[simp, scoped grind =]
def multiApp (f : Term Var) : List (Term Var) → Term Var
| []      => f
| a :: as => Term.app (multiApp f as) a

/-
  A list of arguments performs a single reduction step

  [x₁, ..., xᵢ ..., xₙ] ⭢βᶠ [x₁, ..., xᵢ', ..., xₙ]

  if one of the arguments performs a single step xᵢ ⭢βᶠ xᵢ'
  and the rest of the arguments are locally closed.
-/
@[scoped grind, reduction_sys "lβᶠ"]
inductive ListFullBeta : List (Term Var) → List (Term Var) → Prop where
| step : N ⭢βᶠ N' → (∀ N ∈ Ns, LC N) → ListFullBeta (N :: Ns) (N' :: Ns)
| cons : LC N → ListFullBeta Ns Ns' → ListFullBeta (N :: Ns) (N :: Ns')

variable {M M' : Term Var} {Ns Ns' : List (Term Var)}

/- A term resulting from a multi-application is locally closed if
   and only if the leftmost term and all arguments applied to it are locally closed -/
@[scoped grind ←]
lemma multiApp_lc : LC (M.multiApp Ns) ↔ LC M ∧ (∀ N ∈ Ns, LC N) := by
  constructor
  · induction Ns with
    | nil  => grind [multiApp]
    | cons => intro h_lc; cases h_lc; grind
  · induction Ns <;> grind [multiApp, LC.app]

/- Just like ordinary beta reduction, the left-hand side
   of a multi-application step is locally closed -/
@[scoped grind ←]
lemma step_multiApp_l (steps : M ⭢βᶠ M') (lc_Ns : ∀ N ∈ Ns, LC N) :
    M.multiApp Ns ⭢βᶠ M'.multiApp Ns := by
  induction Ns <;> grind [multiApp, FullBeta.appR]

/- Congruence lemma for multi reduction of the left most term of a multi-application -/
@[scoped grind ←]
lemma steps_multiApp_l (steps : M ↠βᶠ M') (lc_Ns : ∀ N ∈ Ns, LC N) :
    M.multiApp Ns ↠βᶠ M'.multiApp Ns := by
  induction steps <;> grind

/- Congruence lemma for single reduction of one of the arguments of a multi-application -/
@[scoped grind ←]
lemma step_multiApp_r (steps : Ns ⭢lβᶠ Ns') (lc_M : LC M) : M.multiApp Ns ⭢βᶠ M.multiApp Ns' := by
  induction steps <;> grind [multiApp, FullBeta.appL, FullBeta.appR]

/- Congruence lemma for multiple reduction of one of the arguments of a multi-application -/
@[scoped grind ←]
lemma steps_multiApp_r (steps : Ns ↠lβᶠ Ns') (lc_M : LC M) : M.multiApp Ns ↠βᶠ M.multiApp Ns' := by
  induction steps <;> grind [multiApp, FullBeta.appL, FullBeta.appR]

variable [DecidableEq Var] [HasFresh Var]

/- Just like ordinary beta reduction, the right-hand side
   of a multi-application step is locally closed -/
lemma multiApp_step_lc_r (step : Ns ⭢lβᶠ Ns') : ∀ N ∈ Ns', LC N := by
  induction step <;> grind [FullBeta.step_lc_r]

/- Just like ordinary beta reduction, multiple steps of a argument list preserves local closure -/
lemma multiApp_steps_lc (step : Ns ↠lβᶠ Ns') (H : ∀ N ∈ Ns, LC N) : ∀ N ∈ Ns', LC N := by
  induction step <;> grind [FullBeta.step_lc_r, multiApp_step_lc_r]

/- If a term (λ M) N P_1 ... P_n reduces in a single step to Q, then
   Q must be one of the following forms:

    Q = (λ M') N P₁ ... Pₙ where M ⭢βᶠ M' or
    Q = (λ M) N' P₁ ... Pₙ where N ⭢βᶠ N' or
    Q = (λ M) N P₁' ... Pₙ' where P_i ⭢βᶠ P_i' for some i or
    Q = (M ^ N) P₁ ... Pₙ
-/
lemma invert_abs_multiApp_st {Ps} {M N Q : Term Var}
  (h_red : multiApp (M.abs.app N) Ps ⭢βᶠ Q) :
    (∃ M', M.abs ⭢βᶠ Term.abs M' ∧ Q = multiApp (M'.abs.app N) Ps) ∨
    (∃ N', N ⭢βᶠ N' ∧ Q = multiApp (M.abs.app N') Ps) ∨
    (∃ Ps', Ps ⭢lβᶠ Ps' ∧ Q = multiApp (M.abs.app N) Ps') ∨
    (Q = multiApp (M ^ N) Ps) := by
  induction Ps generalizing M N Q with
  | nil =>
    rw [multiApp] at h_red
    rw [multiApp]
    cases h_red
    · case beta abs_lc n_lc => grind
    · case appL M N' lc_z h_red => grind
    · case appR M M' lc_z h_red =>
        left
        cases lc_z
        · case abs M' xs h_lc =>
            exists M'
            constructor
            · apply FullBeta.step_abs_cong
              assumption
            · rfl
  | cons P Ps ih =>
    have h_lc := (FullBeta.step_lc_l h_red)
    rw [multiApp] at h_red
    generalize Heq : (M.abs.app N).multiApp Ps = Q'
    rw [Heq] at h_red
    cases h_red
    · case beta abs_lc n_lc => cases Ps <;> contradiction
    · case appL Y M P' lc_z h_red =>
        right; right; left
        exists (P' :: Ps); grind
    · case appR M Q'' h_red P_lc =>
        rw [←Heq] at h_red
        match (ih h_red) with
        | .inl ⟨ M', st, Heq' ⟩                => grind
        | .inr (.inl ⟨ N', st, Heq' ⟩)         => grind
        | .inr (.inr (.inl ⟨ Ps', st, Heq' ⟩)) =>
          right; right; left
          exists (P :: Ps');grind
        | .inr (.inr (.inr Heq'))              => grind

/- If a term (λ M) N P₁ ... Pₙ reduces in multiple steps to Q, then either Q if of the form

    Q = (λ M') N' P'₁ ... P'ₙ

   or

    we first reach an intermediate term of this shape,

    (λ M) N P₁ ... Pₙ ↠βᶠ (λ M') N' P'₁ ... P'ₙ

    then perform a beta reduction and reduce further to Q

    (λ M') N' P'₁ ... P'ₙ ↠βᶠ M' ^ N' P'_₁ ... P'_ₙ ↠βᶠ Q

   where M ↠βᶠ M' and N ↠βᶠ N' and P_i ↠βᶠ P_i' for all i,
-/
lemma invert_abs_multiApp_mst {Ps} {M N Q : Term Var}
  (h_red : multiApp (M.abs.app N) Ps ↠βᶠ Q) :
    ∃ M' N' Ns', M.abs ↠βᶠ M'.abs ∧ N ↠βᶠ N' ∧ Ps ↠lβᶠ Ns' ∧
                 (Q = multiApp (M'.abs.app N') Ns' ∨
     (multiApp (M.abs.app N) Ps ↠βᶠ multiApp (M' ^ N') Ns' ∧
                                     multiApp (M' ^ N') Ns' ↠βᶠ Q)) := by
  induction h_red
  · case refl => grind
  · case tail Q' Q'' steps step ih =>
    match ih with
    | ⟨ M', N', Ps', st_M, st_N, st_Ps, Cases ⟩ =>
      match Cases with
      | .inl Heq =>
        rw [Heq] at step
        match (invert_abs_multiApp_st step) with
        | .inl ⟨ M'', st, HeqM'' ⟩             => grind
        | .inr (.inl ⟨ N', st, Heq' ⟩)         => grind
        | .inr (.inr (.inl ⟨ Ps', st, Heq' ⟩)) => grind
        | .inr (.inr (.inr Heq'))              => grind
      | .inr ⟨ steps1, steps2 ⟩ => grind [Relation.ReflTransGen.single]

end LambdaCalculus.LocallyNameless.Untyped.Term

end Cslib
