/-
Copyright (c) 2025 Yichen Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yichen Xu.
-/

/-
# Properties of parallel substitution for System F<:

This module establishes the fundamental algebraic properties of parallel substitution
that are essential for the metatheory of System F<:.
-/

import Cslib.Computability.LambdaCalculus.WellScoped.FSub.Substitution.Core
import Cslib.Computability.LambdaCalculus.WellScoped.FSub.Syntax.Subst

/-- Composition of substitutions. If σ₁ maps s₁ to s₂ and σ₂ maps s₂ to s₃,
    then their composition maps s₁ to s₃ by first applying σ₁ then σ₂. -/
def Subst.comp (σ1 : Subst s1 s2) (σ2 : Subst s2 s3) : Subst s1 s3 :=
  { var := fun x => (σ1.var x).subst σ2
    tvar := fun X => (σ1.tvar X).subst σ2 }

/-- Shows that lifting a substitution for term variables preserves type variable mappings
    by renaming with succVar. -/
theorem Subst.tvar_there_var_liftVar {σ : Subst s1 s2} :
  (σ.liftVar.tvar (.there_var X)) = (σ.tvar X).rename Rename.succVar := rfl

/-- Shows that lifting a substitution for type variables preserves older type variable mappings
    by renaming with succTVar. -/
theorem Subst.tvar_there_tvar_liftTVar {σ : Subst s1 s2} :
  (σ.liftTVar.tvar (.there_tvar X)) = (σ.tvar X).rename Rename.succTVar := rfl

/-- Shows that lifting a substitution for type variables preserves term variable mappings
    by renaming with succTVar. -/
theorem Subst.var_there_tvar_liftTVar {σ : Subst s1 s2} :
  (σ.liftTVar.var (.there_tvar x)) = (σ.var x).rename Rename.succTVar := rfl

/-- For type variables, substitution followed by term variable weakening equals
    term variable weakening followed by substitution with a lifted substitution. -/
theorem Ty.tvar_subst_succVar_comm {X : TVar (s1 ++ s0)} (σ : Subst s1 s2) :
  ((tvar X).subst (σ.lift s0)).rename (Rename.succVar.lift s0) =
    ((tvar X).rename (Rename.succVar.lift s0)).subst (σ.liftVar.lift s0) := by
  induction s0
  case empty => rfl
  case push_var s0 ih =>
    cases X
    case there_var X0 =>
      simp only [Subst.lift, Ty.subst]
      conv => lhs; simp only [Subst.liftVar]
      conv => rhs; simp only [Subst.tvar_there_var_liftVar]
      simp only [Rename.lift, ←Ty.rename_succVar_comm]
      congr; exact (ih (X:=X0))
  case push_tvar s0 ih =>
    cases X <;> try rfl
    case there_tvar X0 =>
      conv => lhs; simp only [Subst.lift, Ty.subst]
      conv => lhs; simp only [Subst.liftTVar, Rename.lift]
      simp only [←Ty.rename_succTVar_comm]
      congr; exact (ih (X:=X0))

/-- Proves that substitution commutes with type variable weakening for type variables. -/
theorem Ty.tvar_subst_succTVar_comm {X : TVar (s1 ++ s0)} (σ : Subst s1 s2) :
  ((tvar X).subst (σ.lift s0)).rename (Rename.succTVar.lift s0) =
    ((tvar X).rename (Rename.succTVar.lift s0)).subst (σ.liftTVar.lift s0) := by
  induction s0
  case empty => rfl
  case push_var s0 ih =>
    cases X
    case there_var X0 =>
      conv => lhs; simp only [Subst.lift, Ty.subst]
      conv => lhs; simp only [Subst.liftVar, Rename.lift]
      simp only [←Ty.rename_succVar_comm]
      congr; exact (ih (X:=X0))
  case push_tvar s0 ih =>
    cases X <;> try rfl
    case there_tvar X0 =>
      conv => lhs; simp only [Subst.lift, Ty.subst]
      conv => lhs; simp only [Subst.liftTVar, Rename.lift]
      simp only [←Ty.rename_succTVar_comm]
      congr; exact (ih (X:=X0))

/-- Proves that substitution commutes with term variable weakening for types. -/
theorem Ty.subst_succVar_comm {T : Ty (s1 ++ s0)} (σ : Subst s1 s2) :
  (T.subst (σ.lift s0)).rename (Rename.succVar.lift s0) =
    (T.rename (Rename.succVar.lift s0)).subst (σ.liftVar.lift s0) := by
  match T with
  | .top => rfl
  | .tvar X => simp [Ty.tvar_subst_succVar_comm]
  | .arrow T1 T2 =>
    have ih1 := Ty.subst_succVar_comm (T:=T1) (σ:=σ)
    have ih2 := Ty.subst_succVar_comm (T:=T2) (σ:=σ)
    grind [Ty.subst, Ty.rename]
  | .poly T1 T2 =>
    have ih1 := Ty.subst_succVar_comm (T:=T1) (σ:=σ)
    have ih2 := Ty.subst_succVar_comm (s0:=s0,X) (T:=T2) (σ:=σ)
    simp [Ty.subst, Ty.rename, ih1]; exact ih2

/-- Proves that substitution commutes with type variable weakening for types. -/
theorem Ty.subst_succTVar_comm {T : Ty (s1 ++ s0)} (σ : Subst s1 s2) :
  (T.subst (σ.lift s0)).rename (Rename.succTVar.lift s0) =
    (T.rename (Rename.succTVar.lift s0)).subst (σ.liftTVar.lift s0) := by
  match T with
  | .top => rfl
  | .tvar X => simp [Ty.tvar_subst_succTVar_comm]
  | .arrow T1 T2 =>
    have ih1 := Ty.subst_succTVar_comm (T:=T1) (σ:=σ)
    have ih2 := Ty.subst_succTVar_comm (T:=T2) (σ:=σ)
    grind [Ty.subst, Ty.rename]
  | .poly T1 T2 =>
    have ih1 := Ty.subst_succTVar_comm (T:=T1) (σ:=σ)
    have ih2 := Ty.subst_succTVar_comm (s0:=s0,X) (T:=T2) (σ:=σ)
    simp [Ty.subst, Ty.rename, ih1]; exact ih2

/-- Base case of substitution commuting with term variable weakening. -/
theorem Ty.subst_succVar_comm_base {T : Ty s1} (σ : Subst s1 s2) :
  (T.subst σ).rename Rename.succVar = (T.rename Rename.succVar).subst (σ.liftVar) := by
  exact Ty.subst_succVar_comm (T:=T) (σ:=σ) (s0:=Sig.empty)

/-- Base case of substitution commuting with type variable weakening. -/
theorem Ty.subst_succTVar_comm_base {T : Ty s1} (σ : Subst s1 s2) :
  (T.subst σ).rename Rename.succTVar = (T.rename Rename.succTVar).subst (σ.liftTVar) := by
  exact Ty.subst_succTVar_comm (T:=T) (σ:=σ) (s0:=Sig.empty)

/-- Shows that renaming an expression commutes with type variable weakening. -/
theorem Exp.rename_succTVar_comm {e : Exp s1} {f : Rename s1 s2} :
  (e.rename f).rename Rename.succTVar =
    (e.rename Rename.succTVar).rename f.liftTVar := by
  simp [Exp.rename_comp, Rename.rename_succTVar_comm]

/-- Shows that renaming an expression commutes with term variable weakening. -/
theorem Exp.rename_succVar_comm {e : Exp s1} {f : Rename s1 s2} :
  (e.rename f).rename Rename.succVar =
    (e.rename Rename.succVar).rename f.liftVar := by
  simp [Exp.rename_comp, Rename.rename_succVar_comm]

/-- Proves that substitution commutes with type variable weakening for variables. -/
theorem Exp.var_subst_succTVar_comm {x : Var (s1 ++ s0)} (σ : Subst s1 s2) :
  ((var x).subst (σ.lift s0)).rename (Rename.succTVar.lift s0) =
    ((var x).rename (Rename.succTVar.lift s0)).subst (σ.liftTVar.lift s0) := by
  induction s0 <;> try rfl
  case push_var s0 ih =>
    cases x <;> try rfl
    case there_var x0 =>
      conv => lhs; simp only [Subst.lift, Exp.subst]
      conv => lhs; simp only [Subst.liftVar, Rename.lift]
      simp only [←Exp.rename_succVar_comm]
      congr; exact (ih (x:=x0))
  case push_tvar s0 ih =>
    cases x
    case there_tvar x0 =>
      conv => lhs; simp only [Subst.liftVar, Subst.lift, Rename.lift]
      conv => lhs; simp only [Exp.subst, Subst.liftTVar]
      simp only [←Exp.rename_succTVar_comm]
      congr; exact (ih (x:=x0))

/-- Proves that substitution commutes with term variable weakening for variables. -/
theorem Exp.var_subst_succVar_comm {x : Var (s1 ++ s0)} (σ : Subst s1 s2) :
  ((var x).subst (σ.lift s0)).rename (Rename.succVar.lift s0) =
    ((var x).rename (Rename.succVar.lift s0)).subst (σ.liftVar.lift s0) := by
  induction s0 <;> try rfl
  case push_var s0 ih =>
    cases x <;> try rfl
    case there_var x0 =>
      conv => lhs; simp only [Subst.lift, Exp.subst, Subst.liftVar, Rename.lift]
      simp only [←Exp.rename_succVar_comm]
      congr; exact (ih (x:=x0))
  case push_tvar s0 ih =>
    cases x
    case there_tvar x0 =>
      conv => lhs; simp only [Subst.lift, Exp.subst, Subst.liftTVar, Rename.lift]
      simp only [←Exp.rename_succTVar_comm]
      congr; exact (ih (x:=x0))

/-- Proves that substitution commutes with type variable weakening for expressions. -/
theorem Exp.subst_succTVar_comm {e : Exp (s1 ++ s0)} (σ : Subst s1 s2) :
  (e.subst (σ.lift s0)).rename (Rename.succTVar.lift s0) =
    (e.rename (Rename.succTVar.lift s0)).subst (σ.liftTVar.lift s0) := by
  match e with
  | .var x => simp [Exp.var_subst_succTVar_comm]
  | .abs A t =>
    have ih1 := Ty.subst_succTVar_comm (T:=A) (σ:=σ)
    have ih2 := Exp.subst_succTVar_comm (s0:=s0,x) (e:=t) (σ:=σ)
    simp only [Exp.subst, Exp.rename, ih1]; congr
  | .tabs A t =>
    have ih1 := Ty.subst_succTVar_comm (T:=A) (σ:=σ)
    have ih2 := Exp.subst_succTVar_comm (s0:=s0,X) (e:=t) (σ:=σ)
    simp only [Exp.subst, Exp.rename, ih1]; congr
  | .app t1 t2 =>
    have ih1 := Exp.subst_succTVar_comm (e:=t1) (σ:=σ)
    have ih2 := Exp.subst_succTVar_comm (e:=t2) (σ:=σ)
    simp [Exp.subst, Exp.rename, ih1, ih2]
  | .tapp t A =>
    have ih1 := Ty.subst_succTVar_comm (T:=A) (σ:=σ)
    have ih2 := Exp.subst_succTVar_comm (s0:=s0) (e:=t) (σ:=σ)
    simp [Exp.subst, Exp.rename, ih1, ih2]

/-- Proves that substitution commutes with term variable weakening for expressions. -/
theorem Exp.subst_succVar_comm {e : Exp (s1 ++ s0)} (σ : Subst s1 s2) :
  (e.subst (σ.lift s0)).rename (Rename.succVar.lift s0) =
    (e.rename (Rename.succVar.lift s0)).subst (σ.liftVar.lift s0) := by
  match e with
  | .var x => simp [Exp.var_subst_succVar_comm]
  | .abs A t =>
    have ih1 := Ty.subst_succVar_comm (T:=A) (σ:=σ)
    have ih2 := Exp.subst_succVar_comm (s0:=s0,x) (e:=t) (σ:=σ)
    simp only [Exp.subst, Exp.rename, ih1]; congr
  | .tabs A t =>
    have ih1 := Ty.subst_succVar_comm (T:=A) (σ:=σ)
    have ih2 := Exp.subst_succVar_comm (s0:=s0,X) (e:=t) (σ:=σ)
    simp only [Exp.subst, Exp.rename, ih1]; congr
  | .app t1 t2 =>
    have ih1 := Exp.subst_succVar_comm (e:=t1) (σ:=σ)
    have ih2 := Exp.subst_succVar_comm (e:=t2) (σ:=σ)
    simp [Exp.subst, Exp.rename, ih1, ih2]
  | .tapp t A =>
    have ih1 := Ty.subst_succVar_comm (T:=A) (σ:=σ)
    have ih2 := Exp.subst_succVar_comm (s0:=s0) (e:=t) (σ:=σ)
    simp [Exp.subst, Exp.rename, ih1, ih2]

/-- Proves that lifting a substitution for type variables commutes with composition. -/
theorem Subst.liftTVar_comp {σ1 : Subst s1 s2} {σ2 : Subst s2 s3} :
  (σ1.comp σ2).liftTVar = σ1.liftTVar.comp σ2.liftTVar := by
  apply Subst.funext
  case var =>
    intro x; cases x
    case there_tvar x0 =>
      simp [Subst.comp, Subst.liftTVar]
      simpa [Subst.lift, Rename.lift] using
        (Exp.subst_succTVar_comm (s0:=Sig.empty) (σ:=σ2))
  case tvar =>
    intro X; cases X <;> try rfl
    case there_tvar X0 =>
      simpa [Subst.lift, Rename.lift] using
        (Ty.subst_succTVar_comm (s0:=Sig.empty) (T:=σ1.tvar X0) (σ:=σ2))

/-- Proves that lifting a substitution for term variables commutes with composition. -/
theorem Subst.liftVar_comp {σ1 : Subst s1 s2} {σ2 : Subst s2 s3} :
  (σ1.comp σ2).liftVar = σ1.liftVar.comp σ2.liftVar := by
  apply Subst.funext
  case var =>
    intro x; cases x <;> try rfl
    case there_var x0 =>
      simpa [Subst.lift, Rename.lift] using
        (Exp.subst_succVar_comm (s0:=Sig.empty) (σ:=σ2))
  case tvar =>
    intro X; cases X
    case there_var X0 =>
      simpa [Subst.lift, Rename.lift] using
        (Ty.subst_succVar_comm (s0:=Sig.empty) (T:=σ1.tvar X0) (σ:=σ2))

/-- **Fundamental associativity law for substitution composition on types**:
    Sequential application of substitutions equals composition.

    This states that (T[σ₁])[σ₂] = T[σ₁ ∘ σ₂], establishing that substitution
    forms a category-like structure. This is essential for reasoning about
    complex substitution chains in proofs. -/
theorem Ty.subst_comp {T : Ty s1} (σ1 : Subst s1 s2) (σ2 : Subst s2 s3) :
  (T.subst σ1).subst σ2 = T.subst (σ1.comp σ2) := by
  induction T generalizing s2 s3 <;> try (solve | rfl)
  all_goals simp only [Ty.subst, Subst.liftTVar_comp]; grind

/-- **Fundamental associativity law for substitution composition on expressions**:
    Sequential application of substitutions equals composition.

    This extends the associativity property to expressions, ensuring that
    the substitution algebra is consistent across all syntactic categories. -/
theorem Exp.subst_comp {e : Exp s1} (σ1 : Subst s1 s2) (σ2 : Subst s2 s3) :
  (e.subst σ1).subst σ2 = e.subst (σ1.comp σ2) := by
  induction e generalizing s2 s3
  case var x => rfl
  all_goals grind [Exp.subst, Ty.subst_comp, Subst.liftVar_comp, Subst.liftTVar_comp]

/-- Shows that converting a rename to a substitution commutes with lifting for type variables. -/
theorem Rename.asSubst_liftTVar_comm {f : Rename s1 s2} :
  (f.asSubst).liftTVar = f.liftTVar.asSubst := by
  apply Subst.funext <;> intro a <;> cases a <;> rfl

/-- Shows that converting a rename to a substitution commutes with lifting for term variables. -/
theorem Rename.asSubst_liftVar_comm {f : Rename s1 s2} :
  (f.asSubst).liftVar = f.liftVar.asSubst := by
  apply Subst.funext <;> intro a <;> cases a <;> rfl

/-- Proves that substituting with a rename-as-substitution equals renaming for types. -/
theorem Ty.subst_asSubst {T : Ty s1} {f : Rename s1 s2} :
  T.subst f.asSubst = T.rename f := by
  induction T generalizing s2
    <;> try (solve | rfl | grind [Ty.subst, Ty.rename, Rename.asSubst_liftTVar_comm])

/-- Proves that substituting with a rename-as-substitution equals renaming for expressions. -/
theorem Exp.subst_asSubst {e : Exp s1} {f : Rename s1 s2} :
  e.subst f.asSubst = e.rename f := by
  induction e generalizing s2
  case var x => rfl
  all_goals (simp [Exp.subst, Exp.rename,
    Ty.subst_asSubst, Rename.asSubst_liftVar_comm, Rename.asSubst_liftTVar_comm]; grind)

/-- Shows that lifting the identity substitution for term variables gives the identity. -/
theorem Subst.id_liftVar :
  (Subst.id (s:=s)).liftVar = Subst.id := by
  apply Subst.funext <;> intro a <;> cases a <;> rfl

/-- Shows that lifting the identity substitution for type variables gives the identity. -/
theorem Subst.id_liftTVar :
  (Subst.id (s:=s)).liftTVar = Subst.id := by
  apply Subst.funext <;> intro a <;> cases a <;> rfl

/-- **Identity law for types**: The identity substitution acts as neutral element.
    This establishes that T[id] = T, showing that substitution has the proper
    categorical structure with identity morphisms. -/
theorem Ty.subst_id {T : Ty s} : T.subst Subst.id = T := by
  induction T <;> try (solve | rfl)
  all_goals (simp only [Ty.subst, Subst.id_liftTVar]; grind)

/-- **Identity law for expressions**: The identity substitution acts as neutral element.
    This extends the identity property to expressions, completing the algebraic
    structure of the substitution category. -/
theorem Exp.subst_id {e : Exp s} : e.subst Subst.id = e := by
  induction e <;> try (solve | rfl)
  all_goals (simp only [Exp.subst, Ty.subst_id, Subst.id_liftVar, Subst.id_liftTVar]; grind)

/-- Proves that opening a type variable commutes with renaming for substitutions. -/
theorem Subst.open_tvar_rename_comm {T : Ty s} {f : Rename s s'} :
  (Subst.open_tvar T).comp (f.asSubst)
    = f.liftTVar.asSubst.comp (Subst.open_tvar (T.rename f)) := by
  apply Subst.funext
  case var => intro x; cases x; rfl
  case tvar =>
    intro X; cases X <;> try (solve | rfl | simp only [Subst.comp, Ty.subst_asSubst]; rfl)

/-- Proves that opening a type variable commutes with renaming for types. -/
theorem Ty.open_tvar_rename_comm {T : Ty (s,X)} {U : Ty s} {f : Rename s s'} :
  (T.open_tvar U).rename f = (T.rename f.liftTVar).open_tvar (U.rename f) := by
  simp [Ty.open_tvar, ←Ty.subst_asSubst]
  grind [Ty.subst_comp, Subst.open_tvar_rename_comm, Ty.subst_asSubst]

/-- Shows that successively weakening then opening a type variable gives the identity. -/
theorem Subst.succTVar_open_tvar {T : Ty s} :
  Rename.succTVar.asSubst.comp (Subst.open_tvar T) = Subst.id := by apply Subst.funext <;> aesop

/-- Proves that renaming with succTVar then opening cancels out for expressions. -/
theorem Exp.rename_succTVar_open_tvar {e : Exp s} :
  (e.rename Rename.succTVar).subst (Subst.open_tvar X) =
    e := by
  simp [←Exp.subst_asSubst]
  grind [Exp.subst_comp, Subst.succTVar_open_tvar, Exp.subst_id]

/-- Proves that renaming with succTVar then opening cancels out for types. -/
theorem Ty.rename_succTVar_open_tvar {T : Ty s} :
  (T.rename Rename.succTVar).subst (Subst.open_tvar X) =
    T := by
  simp [←Ty.subst_asSubst]
  grind [Ty.subst_comp, Subst.succTVar_open_tvar, Ty.subst_id]

/-- Shows that successively weakening then opening a term variable gives the identity. -/
theorem Subst.succVar_open_var {e : Exp s} :
  Rename.succVar.asSubst.comp (Subst.open_var e) = Subst.id := by apply Subst.funext <;> aesop

/-- Proves that renaming with succVar then opening cancels out for expressions. -/
theorem Exp.rename_succVar_open_var {e : Exp s} :
  (e.rename Rename.succVar).subst (Subst.open_var X) =
    e := by
  simp [←Exp.subst_asSubst]
  grind [Exp.subst_comp, Subst.succVar_open_var, Exp.subst_id]

/-- Proves that renaming with succVar then opening cancels out for types. -/
theorem Ty.rename_succVar_open_var {T : Ty s} :
  (T.rename Rename.succVar).subst (Subst.open_var X) =
    T := by
  simp [←Ty.subst_asSubst]
  grind [Ty.subst_comp, Subst.succVar_open_var, Ty.subst_id]

/-- Proves that opening a type variable commutes with substitution for substitutions. -/
theorem Subst.open_tvar_subst_comm {T : Ty s} {σ : Subst s s'} :
  (Subst.open_tvar T).comp σ = σ.liftTVar.comp (Subst.open_tvar (T.subst σ)) := by
  apply Subst.funext
  case var =>
    intro x; cases x
    conv => lhs; simp only [Subst.comp, Subst.open_tvar]
    conv => rhs; simp only [Subst.comp, Subst.liftTVar]
    simp only [Exp.rename_succTVar_open_tvar]; rfl
  case tvar =>
    intro X; cases X <;> try rfl
    case there_tvar X0 =>
      conv => lhs; simp only [Subst.comp, Subst.open_tvar]
      conv => rhs; simp only [Subst.comp, Subst.liftTVar]
      simp only [Ty.rename_succTVar_open_tvar]; rfl

/-- Proves that opening a type variable commutes with substitution for types. -/
theorem Ty.open_tvar_subst_comm {T : Ty (s,X)} {U : Ty s} {σ : Subst s s'} :
  (T.open_tvar U).subst σ = (T.subst σ.liftTVar).open_tvar (U.subst σ) := by
  simp [Ty.open_tvar, Ty.subst_comp, Subst.open_tvar_subst_comm]
