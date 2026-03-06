module

public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta

@[expose] public section

namespace Cslib

universe u

variable {Var : Type u} [DecidableEq Var] [HasFresh Var]

namespace LambdaCalculus.LocallyNameless.Untyped.Term

@[simp]
def multiApp (f : Term Var) (args : List (Term Var)) :=
  match args with
  | []      => f
  | a :: as => Term.app (multiApp f as) a

@[reduction_sys "βᶠ"]
inductive multiApp_full_beta : List (Term Var) → List (Term Var) → Prop where
| step : N ⭢βᶠ N' → (∀ N ∈ Ns, LC N) → multiApp_full_beta (N :: Ns) (N' :: Ns)
| cons : LC N → multiApp_full_beta Ns Ns' → multiApp_full_beta (N :: Ns) (N :: Ns')

attribute [scoped grind .] multiApp_full_beta.step multiApp_full_beta.cons

lemma multiApp_step_lc_r {Ns Ns' : List (Term Var)}
  (step : Ns ⭢βᶠ Ns')
  : (∀ N ∈ Ns', LC N) := by
  induction step <;> grind[FullBeta.step_lc_r]

lemma multiApp_steps_lc {Ns Ns' : List (Term Var)}
  (step : Ns ↠βᶠ Ns') (H : ∀ N ∈ Ns, LC N)
  : (∀ N ∈ Ns', LC N) := by
  induction step <;> grind[FullBeta.step_lc_r, multiApp_step_lc_r]

@[scoped grind ←]
lemma multiApp_lc {M : Term Var} {Ns : List (Term Var)} :
  LC (M.multiApp Ns) ↔ LC M ∧ (∀ N ∈ Ns, LC N)
   := by
  constructor
  · induction Ns
    · case nil => grind[multiApp]
    · case cons N Ns ih => intro h_lc; cases h_lc; grind
  · induction Ns <;> grind[multiApp, LC.app]

@[scoped grind ←]
lemma step_multiApp_l {M M' : Term Var} {Ns : List (Term Var)} :
  M ⭢βᶠ M' →
  (∀ N ∈ Ns, LC N) →
  M.multiApp Ns ⭢βᶠ M'.multiApp Ns := by
  induction Ns <;> grind[multiApp, FullBeta.appR]

@[scoped grind ←]
lemma steps_multiApp_l {M M' : Term Var} {Ns : List (Term Var)}
  (steps : M ↠βᶠ M')
  (lc_Ns : ∀ N ∈ Ns, LC N)
  : M.multiApp Ns ↠βᶠ M'.multiApp Ns := by
  induction steps <;> grind

@[scoped grind ←]
lemma step_multiApp_r {M : Term Var} {Ns Ns' : List (Term Var)}
  (steps : Ns ⭢βᶠ Ns')
  (lc_M : LC M)
  : M.multiApp Ns ⭢βᶠ M.multiApp Ns' := by
  induction steps <;> grind[multiApp,FullBeta.appL,FullBeta.appR]

@[scoped grind ←]
lemma steps_multiApp_r {M : Term Var} {Ns Ns' : List (Term Var)}
  (steps : Ns ↠βᶠ Ns')
  (lc_M : LC M)
  : M.multiApp Ns ↠βᶠ M.multiApp Ns' := by
  induction steps <;> grind[multiApp,FullBeta.appL,FullBeta.appR]

lemma invert_multiApp_st {Ps} {M N Q : Term Var}
  (h_red : multiApp (M.abs.app N) Ps ⭢βᶠ Q) :
  (∃ M', M.abs ⭢βᶠ Term.abs M' ∧ Q = multiApp (M'.abs.app N) Ps) ∨
  (∃ N', N ⭢βᶠ N' ∧ Q = multiApp (M.abs.app N') Ps) ∨
  (∃ Ps', Ps ⭢βᶠ Ps' ∧ Q = multiApp (M.abs.app N) Ps') ∨
  (Q = multiApp (M ^ N) Ps) := by
  revert M N Q h_red
  induction Ps with
  | nil =>
    intro N N P h_red
    rw[multiApp] at h_red
    rw[multiApp]
    cases h_red
    · case beta abs_lc n_lc => aesop
    · case appL M N' lc_z h_red => aesop
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
    intro M N Q h_red
    have h_lc := (FullBeta.step_lc_l h_red)
    rw [multiApp] at h_red
    generalize Heq : (M.abs.app N).multiApp Ps = Q'
    rw[Heq] at h_red
    cases h_red
    · case beta abs_lc n_lc => cases Ps <;> contradiction
    · case appL Y M P' lc_z h_red =>
        right; right; left
        exists (P' :: Ps)
        simp
        grind
    · case appR M Q'' h_red P_lc =>
        rw[←Heq] at h_red
        match (ih h_red) with
        | .inl ⟨ M', st, Heq' ⟩                => aesop
        | .inr (.inl ⟨ N', st, Heq' ⟩)         => aesop
        | .inr (.inr (.inl ⟨ Ps', st, Heq' ⟩)) =>
          right; right; left
          exists (P :: Ps')
          simp
          grind
        | .inr (.inr (.inr Heq'))              => aesop


lemma invert_multiApp_mst {Ps} {M N Q : Term Var}
  (h_red : multiApp (M.abs.app N) Ps ↠βᶠ Q) :
  ∃ M' N' Ns', M.abs ↠βᶠ M'.abs ∧ N ↠βᶠ N' ∧ Ps ↠βᶠ Ns' ∧
    (Q = multiApp (M'.abs.app N') Ns' ∨
     (multiApp (M.abs.app N) Ps ↠βᶠ multiApp (M'^ N') Ns' ∧
                                      multiApp (M'^ N') Ns' ↠βᶠ Q)) := by
  induction h_red
  · case refl => grind
  · case tail Q' Q'' steps step ih =>
    match ih with
    | ⟨ M', N', Ps', st_M, st_N, st_Ps, Cases ⟩ =>
      match Cases with
      | .inl Heq =>
        rw[Heq] at step
        match (invert_multiApp_st step) with
        | .inl ⟨ M'', st, HeqM'' ⟩             => grind
        | .inr (.inl ⟨ N', st, Heq' ⟩)         => grind
        | .inr (.inr (.inl ⟨ Ps', st, Heq' ⟩)) => grind
        | .inr (.inr (.inr Heq'))              => grind
      | .inr ⟨ steps1, steps2 ⟩ => grind[Relation.ReflTransGen.single]

end LambdaCalculus.LocallyNameless.Untyped.Term

end Cslib
