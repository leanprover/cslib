import Cslib.Computability.LambdaCalculus.WellScoped.FSub.Substitution.Core
import Cslib.Computability.LambdaCalculus.WellScoped.FSub.Syntax.Subst

def Subst.comp (σ1 : Subst s1 s2) (σ2 : Subst s2 s3) : Subst s1 s3 := by
  constructor
  case var =>
    intro x; exact (σ1.var x).subst σ2
  case tvar =>
    intro X; exact (σ1.tvar X).subst σ2

theorem Subst.tvar_there_var_liftVar {σ : Subst s1 s2} :
  (σ.liftVar.tvar (.there_var X)) = (σ.tvar X).rename Rename.succVar := rfl

theorem Subst.tvar_there_tvar_liftTVar {σ : Subst s1 s2} :
  (σ.liftTVar.tvar (.there_tvar X)) = (σ.tvar X).rename Rename.succTVar := rfl

theorem Subst.var_there_tvar_liftTVar {σ : Subst s1 s2} :
  (σ.liftTVar.var (.there_tvar x)) = (σ.var x).rename Rename.succTVar := rfl

theorem Ty.tvar_subst_succVar_comm {X : TVar (s1 ++ s0)} (σ : Subst s1 s2) :
  ((tvar X).subst (σ.lift s0)).rename (Rename.succVar.lift s0) =
    ((tvar X).rename (Rename.succVar.lift s0)).subst (σ.liftVar.lift s0) := by
  induction s0
  case empty => rfl
  case cons_var s0 ih =>
    cases X
    case there_var X0 =>
      simp [Subst.lift, Ty.subst]
      conv => lhs; simp [Subst.liftVar]
      conv =>
        rhs; simp [Ty.rename, Rename.lift, Rename.liftVar]
        simp [Ty.subst]
        simp [Subst.tvar_there_var_liftVar]
      simp [Rename.lift]
      simp [<-Ty.rename_succVar_comm]
      congr
      exact (ih (X:=X0))
  case cons_tvar s0 ih =>
    cases X
    case here => rfl
    case there_tvar X0 =>
      conv => lhs; simp [Subst.lift, Ty.subst]
      conv => lhs; simp [Subst.liftTVar, Rename.lift]
      simp [<-Ty.rename_succTVar_comm]
      congr
      exact (ih (X:=X0))

theorem Ty.tvar_subst_succTVar_comm {X : TVar (s1 ++ s0)} (σ : Subst s1 s2) :
  ((tvar X).subst (σ.lift s0)).rename (Rename.succTVar.lift s0) =
    ((tvar X).rename (Rename.succTVar.lift s0)).subst (σ.liftTVar.lift s0) := by
  induction s0
  case empty => rfl
  case cons_var s0 ih =>
    cases X
    case there_var X0 =>
      conv => lhs; simp [Subst.lift, Ty.subst]
      conv => lhs; simp [Subst.liftVar, Rename.lift]
      simp [<-Ty.rename_succVar_comm]
      congr
      exact (ih (X:=X0))
  case cons_tvar s0 ih =>
    cases X
    case here => rfl
    case there_tvar X0 =>
      conv => lhs; simp [Subst.lift, Ty.subst]
      conv => lhs; simp [Subst.liftTVar, Rename.lift]
      simp [<-Ty.rename_succTVar_comm]
      congr
      exact (ih (X:=X0))

theorem Ty.subst_succVar_comm {T : Ty (s1 ++ s0)} (σ : Subst s1 s2) :
  (T.subst (σ.lift s0)).rename (Rename.succVar.lift s0) =
    (T.rename (Rename.succVar.lift s0)).subst (σ.liftVar.lift s0) := by
  match T with
  | .top => rfl
  | .tvar X => simp [Ty.tvar_subst_succVar_comm]
  | .arrow T1 T2 =>
    have ih1 := Ty.subst_succVar_comm (T:=T1) (σ:=σ)
    have ih2 := Ty.subst_succVar_comm (T:=T2) (σ:=σ)
    simp [Ty.subst, Ty.rename]
    simp [ih1, ih2]
  | .poly T1 T2 =>
    have ih1 := Ty.subst_succVar_comm (T:=T1) (σ:=σ)
    have ih2 := Ty.subst_succVar_comm (s0:=s0,X) (T:=T2) (σ:=σ)
    simp [Ty.subst, Ty.rename]
    simp [ih1]
    exact ih2

theorem Ty.subst_succTVar_comm {T : Ty (s1 ++ s0)} (σ : Subst s1 s2) :
  (T.subst (σ.lift s0)).rename (Rename.succTVar.lift s0) =
    (T.rename (Rename.succTVar.lift s0)).subst (σ.liftTVar.lift s0) := by
  match T with
  | .top => rfl
  | .tvar X => simp [Ty.tvar_subst_succTVar_comm]
  | .arrow T1 T2 =>
    have ih1 := Ty.subst_succTVar_comm (T:=T1) (σ:=σ)
    have ih2 := Ty.subst_succTVar_comm (T:=T2) (σ:=σ)
    simp [Ty.subst, Ty.rename]
    simp [ih1, ih2]
  | .poly T1 T2 =>
    have ih1 := Ty.subst_succTVar_comm (T:=T1) (σ:=σ)
    have ih2 := Ty.subst_succTVar_comm (s0:=s0,X) (T:=T2) (σ:=σ)
    simp [Ty.subst, Ty.rename]
    simp [ih1]
    exact ih2

theorem Ty.subst_succVar_comm_base {T : Ty s1} (σ : Subst s1 s2) :
  (T.subst σ).rename Rename.succVar = (T.rename Rename.succVar).subst (σ.liftVar) := by
  exact Ty.subst_succVar_comm (T:=T) (σ:=σ) (s0:=Sig.empty)

theorem Ty.subst_succTVar_comm_base {T : Ty s1} (σ : Subst s1 s2) :
  (T.subst σ).rename Rename.succTVar = (T.rename Rename.succTVar).subst (σ.liftTVar) := by
  exact Ty.subst_succTVar_comm (T:=T) (σ:=σ) (s0:=Sig.empty)

theorem Exp.rename_succTVar_comm {e : Exp s1} {f : Rename s1 s2} :
  (e.rename f).rename Rename.succTVar =
    (e.rename Rename.succTVar).rename f.liftTVar := by
  simp [Exp.rename_comp, Rename.rename_succTVar_comm]

theorem Exp.rename_succVar_comm {e : Exp s1} {f : Rename s1 s2} :
  (e.rename f).rename Rename.succVar =
    (e.rename Rename.succVar).rename f.liftVar := by
  simp [Exp.rename_comp, Rename.rename_succVar_comm]

theorem Exp.var_subst_succTVar_comm {x : Var (s1 ++ s0)} (σ : Subst s1 s2) :
  ((var x).subst (σ.lift s0)).rename (Rename.succTVar.lift s0) =
    ((var x).rename (Rename.succTVar.lift s0)).subst (σ.liftTVar.lift s0) := by
  induction s0
  case empty => rfl
  case cons_var s0 ih =>
    cases x
    case here => rfl
    case there_var x0 =>
      conv => lhs; simp [Subst.lift, Exp.subst]
      conv => lhs; simp [Subst.liftVar, Rename.lift]
      simp [<-Exp.rename_succVar_comm]
      congr
      exact (ih (x:=x0))
  case cons_tvar s0 ih =>
    cases x
    case there_tvar x0 =>
      conv => lhs; simp [Subst.liftTVar]
      conv => lhs; simp [Subst.liftVar, Subst.lift, Rename.lift]
      conv => lhs; simp [Exp.subst, Subst.liftTVar]
      simp [<-Exp.rename_succTVar_comm]
      congr
      exact (ih (x:=x0))

theorem Exp.var_subst_succVar_comm {x : Var (s1 ++ s0)} (σ : Subst s1 s2) :
  ((var x).subst (σ.lift s0)).rename (Rename.succVar.lift s0) =
    ((var x).rename (Rename.succVar.lift s0)).subst (σ.liftVar.lift s0) := by
  induction s0
  case empty => rfl
  case cons_var s0 ih =>
    cases x
    case here => rfl
    case there_var x0 =>
      conv => lhs; simp [Subst.lift, Exp.subst]
      conv => lhs; simp [Subst.liftVar, Rename.lift]
      simp [<-Exp.rename_succVar_comm]
      congr
      exact (ih (x:=x0))
  case cons_tvar s0 ih =>
    cases x
    case there_tvar x0 =>
      conv => lhs; simp [Subst.lift, Exp.subst]
      conv => lhs; simp [Subst.liftTVar, Rename.lift]
      simp [<-Exp.rename_succTVar_comm]
      congr
      exact (ih (x:=x0))

theorem Exp.subst_succTVar_comm {e : Exp (s1 ++ s0)} (σ : Subst s1 s2) :
  (e.subst (σ.lift s0)).rename (Rename.succTVar.lift s0) =
    (e.rename (Rename.succTVar.lift s0)).subst (σ.liftTVar.lift s0) := by
  match e with
  | .var x => simp [Exp.var_subst_succTVar_comm]
  | .abs A t =>
    have ih1 := Ty.subst_succTVar_comm (T:=A) (σ:=σ)
    have ih2 := Exp.subst_succTVar_comm (s0:=s0,x) (e:=t) (σ:=σ)
    simp [Exp.subst, Exp.rename]
    simp [ih1]
    congr
  | .tabs A t =>
    have ih1 := Ty.subst_succTVar_comm (T:=A) (σ:=σ)
    have ih2 := Exp.subst_succTVar_comm (s0:=s0,X) (e:=t) (σ:=σ)
    simp [Exp.subst, Exp.rename, ih1]
    congr
  | .app t1 t2 =>
    have ih1 := Exp.subst_succTVar_comm (e:=t1) (σ:=σ)
    have ih2 := Exp.subst_succTVar_comm (e:=t2) (σ:=σ)
    simp [Exp.subst, Exp.rename]
    simp [ih1, ih2]
  | .tapp t A =>
    have ih1 := Ty.subst_succTVar_comm (T:=A) (σ:=σ)
    have ih2 := Exp.subst_succTVar_comm (s0:=s0) (e:=t) (σ:=σ)
    simp [Exp.subst, Exp.rename, ih1, ih2]

theorem Exp.subst_succVar_comm {e : Exp (s1 ++ s0)} (σ : Subst s1 s2) :
  (e.subst (σ.lift s0)).rename (Rename.succVar.lift s0) =
    (e.rename (Rename.succVar.lift s0)).subst (σ.liftVar.lift s0) := by
  match e with
  | .var x => simp [Exp.var_subst_succVar_comm]
  | .abs A t =>
    have ih1 := Ty.subst_succVar_comm (T:=A) (σ:=σ)
    have ih2 := Exp.subst_succVar_comm (s0:=s0,x) (e:=t) (σ:=σ)
    simp [Exp.subst, Exp.rename]
    simp [ih1]
    congr
  | .tabs A t =>
    have ih1 := Ty.subst_succVar_comm (T:=A) (σ:=σ)
    have ih2 := Exp.subst_succVar_comm (s0:=s0,X) (e:=t) (σ:=σ)
    simp [Exp.subst, Exp.rename, ih1]
    congr
  | .app t1 t2 =>
    have ih1 := Exp.subst_succVar_comm (e:=t1) (σ:=σ)
    have ih2 := Exp.subst_succVar_comm (e:=t2) (σ:=σ)
    simp [Exp.subst, Exp.rename, ih1, ih2]
  | .tapp t A =>
    have ih1 := Ty.subst_succVar_comm (T:=A) (σ:=σ)
    have ih2 := Exp.subst_succVar_comm (s0:=s0) (e:=t) (σ:=σ)
    simp [Exp.subst, Exp.rename, ih1, ih2]

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
    intro X; cases X
    case here => rfl
    case there_tvar X0 =>
      simp [Subst.comp, Subst.liftTVar]
      simpa [Subst.lift, Rename.lift] using
        (Ty.subst_succTVar_comm (s0:=Sig.empty) (T:=σ1.tvar X0) (σ:=σ2))

theorem Subst.liftVar_comp {σ1 : Subst s1 s2} {σ2 : Subst s2 s3} :
  (σ1.comp σ2).liftVar = σ1.liftVar.comp σ2.liftVar := by
  apply Subst.funext
  case var =>
    intro x; cases x
    case there_var x0 =>
      simp [Subst.comp, Subst.liftVar]
      simpa [Subst.lift, Rename.lift] using
        (Exp.subst_succVar_comm (s0:=Sig.empty) (σ:=σ2))
    case here => rfl
  case tvar =>
    intro X; cases X
    case there_var X0 =>
      simp [Subst.comp]
      simpa [Subst.lift, Rename.lift] using
        (Ty.subst_succVar_comm (s0:=Sig.empty) (T:=σ1.tvar X0) (σ:=σ2))

theorem Ty.subst_comp {T : Ty s1} (σ1 : Subst s1 s2) (σ2 : Subst s2 s3) :
  (T.subst σ1).subst σ2 = T.subst (σ1.comp σ2) := by
  induction T generalizing s2 s3
  case top => rfl
  case tvar X => rfl
  case arrow T1 T2 ih1 ih2 =>
    simp [Ty.subst]
    simp [ih1, ih2]
  case poly T1 T2 ih1 ih2 =>
    simp [Ty.subst]
    simp [ih1]
    simp [Subst.liftTVar_comp]
    simp [ih2]

theorem Exp.subst_comp {e : Exp s1} (σ1 : Subst s1 s2) (σ2 : Subst s2 s3) :
  (e.subst σ1).subst σ2 = e.subst (σ1.comp σ2) := by
  induction e generalizing s2 s3
  case var x => rfl
  case abs A t ih =>
    simp [Exp.subst]
    simp [Ty.subst_comp]
    simp [Subst.liftVar_comp]
    simp [ih]
  case tabs A t ih =>
    simp [Exp.subst]
    simp [Ty.subst_comp]
    simp [Subst.liftTVar_comp]
    simp [ih]
  case app t1 t2 ih1 ih2 =>
    simp [Exp.subst]
    simp [ih1]
    simp [ih2]
  case tapp t A ih =>
    simp [Exp.subst]
    simp [Ty.subst_comp]
    simp [ih]

theorem Rename.asSubst_liftTVar_comm {f : Rename s1 s2} :
  (f.asSubst).liftTVar = f.liftTVar.asSubst := by
  apply Subst.funext
  case var =>
    intro x; cases x
    case there_tvar x0 => rfl
  case tvar =>
    intro X; cases X
    case here => rfl
    case there_tvar X0 => rfl

theorem Rename.asSubst_liftVar_comm {f : Rename s1 s2} :
  (f.asSubst).liftVar = f.liftVar.asSubst := by
  apply Subst.funext
  case var =>
    intro x; cases x
    case here => rfl
    case there_var x0 => rfl
  case tvar => intro X; cases X; rfl

theorem Ty.subst_asSubst {T : Ty s1} {f : Rename s1 s2} :
  T.subst f.asSubst = T.rename f := by
  induction T generalizing s2
  case top => rfl
  case tvar => rfl
  case arrow T1 T2 ih1 ih2 => simp [Ty.subst, Ty.rename, ih1, ih2]
  case poly T1 T2 ih1 ih2 =>
    simp [Ty.subst, Ty.rename]
    simp [ih1]
    simp [Rename.asSubst_liftTVar_comm]
    simp [ih2]

theorem Exp.subst_asSubst {e : Exp s1} {f : Rename s1 s2} :
  e.subst f.asSubst = e.rename f := by
  induction e generalizing s2
  case var x => rfl
  case abs A t ih =>
    simp [Exp.subst, Exp.rename, Ty.subst_asSubst]
    simp [Rename.asSubst_liftVar_comm]
    simp [ih]
  case tabs A t ih =>
    simp [Exp.subst, Exp.rename, Ty.subst_asSubst]
    simp [Rename.asSubst_liftTVar_comm]
    simp [ih]
  case app t1 t2 ih1 ih2 =>
    simp [Exp.subst, Exp.rename, ih1, ih2]
  case tapp t A ih =>
    simp [Exp.subst, Exp.rename, Ty.subst_asSubst]
    simp [ih]

theorem Subst.id_liftVar :
  (Subst.id (s:=s)).liftVar = Subst.id := by
  apply Subst.funext
  case var => intro x; cases x <;> rfl
  case tvar => intro X; cases X; rfl

theorem Subst.id_liftTVar :
  (Subst.id (s:=s)).liftTVar = Subst.id := by
  apply Subst.funext
  case var => intro x; cases x; rfl
  case tvar => intro X; cases X <;> rfl

theorem Ty.subst_id {T : Ty s} : T.subst Subst.id = T := by
  induction T
  case top => rfl
  case tvar => rfl
  case arrow T1 T2 ih1 ih2 =>
    simp [Ty.subst, ih1, ih2]
  case poly T1 T2 ih1 ih2 =>
    simp [Ty.subst, ih1]
    simp [Subst.id_liftTVar]
    simp [ih2]

theorem Exp.subst_id {e : Exp s} : e.subst Subst.id = e := by
  induction e
  case var x => rfl
  case abs A t ih =>
    simp [Exp.subst, Ty.subst_id]
    simp [Subst.id_liftVar]
    simp [ih]
  case tabs A t ih =>
    simp [Exp.subst, Ty.subst_id]
    simp [Subst.id_liftTVar]
    simp [ih]
  case app t1 t2 ih1 ih2 =>
    simp [Exp.subst, ih1, ih2]
  case tapp t A ih =>
    simp [Exp.subst, Ty.subst_id]
    simp [ih]

theorem Subst.open_tvar_rename_comm {T : Ty s} {f : Rename s s'} :
  (Subst.open_tvar T).comp (f.asSubst)
    = f.liftTVar.asSubst.comp (Subst.open_tvar (T.rename f)) := by
  apply Subst.funext
  case var =>
    intro x
    cases x
    case there_tvar x0 => rfl
  case tvar =>
    intro X
    cases X
    case here =>
      simp [Subst.comp]
      conv => lhs; simp [Subst.open_tvar]
      conv =>
        rhs; simp [Rename.asSubst, Rename.liftTVar, Ty.subst]
        simp [Subst.open_tvar]
      simp [Ty.subst_asSubst]
    case there_tvar X0 => rfl

theorem Ty.open_tvar_rename_comm {T : Ty (s,X)} {U : Ty s} {f : Rename s s'} :
  (T.open_tvar U).rename f = (T.rename f.liftTVar).open_tvar (U.rename f) := by
  simp [Ty.open_tvar, <-Ty.subst_asSubst]
  simp [Ty.subst_comp]
  simp [Subst.open_tvar_rename_comm]
  simp [Ty.subst_asSubst]

theorem Subst.succTVar_open_tvar {T : Ty s} :
  Rename.succTVar.asSubst.comp (Subst.open_tvar T) = Subst.id := by
  apply Subst.funext
  case var => intro x; rfl
  case tvar => intro X; rfl

theorem Exp.rename_succTVar_open_tvar {e : Exp s} :
  (e.rename Rename.succTVar).subst (Subst.open_tvar X) =
    e := by
  simp [<-Exp.subst_asSubst]
  simp [Exp.subst_comp]
  simp [Subst.succTVar_open_tvar]
  simp [Exp.subst_id]

theorem Ty.rename_succTVar_open_tvar {T : Ty s} :
  (T.rename Rename.succTVar).subst (Subst.open_tvar X) =
    T := by
  simp [<-Ty.subst_asSubst]
  simp [Ty.subst_comp]
  simp [Subst.succTVar_open_tvar]
  simp [Ty.subst_id]

theorem Subst.succVar_open_var {e : Exp s} :
  Rename.succVar.asSubst.comp (Subst.open_var e) = Subst.id := by
  apply Subst.funext
  case var => intro x; rfl
  case tvar => intro X; rfl

theorem Exp.rename_succVar_open_var {e : Exp s} :
  (e.rename Rename.succVar).subst (Subst.open_var X) =
    e := by
  simp [<-Exp.subst_asSubst]
  simp [Exp.subst_comp]
  simp [Subst.succVar_open_var]
  simp [Exp.subst_id]

theorem Ty.rename_succVar_open_var {T : Ty s} :
  (T.rename Rename.succVar).subst (Subst.open_var X) =
    T := by
  simp [<-Ty.subst_asSubst]
  simp [Ty.subst_comp]
  simp [Subst.succVar_open_var]
  simp [Ty.subst_id]

theorem Subst.open_tvar_subst_comm {T : Ty s} {σ : Subst s s'} :
  (Subst.open_tvar T).comp σ = σ.liftTVar.comp (Subst.open_tvar (T.subst σ)) := by
  apply Subst.funext
  case var =>
    intro x
    cases x
    conv => lhs; simp [Subst.comp, Subst.open_tvar]
    conv =>
      rhs
      simp [Subst.comp, Subst.liftTVar]
    simp [Exp.rename_succTVar_open_tvar]
    rfl
  case tvar =>
    intro X
    cases X
    case here => rfl
    case there_tvar X0 =>
      conv => lhs; simp [Subst.comp, Subst.open_tvar]
      conv =>
        rhs
        simp [Subst.comp, Subst.liftTVar]
      simp [Ty.rename_succTVar_open_tvar]
      rfl

theorem Ty.open_tvar_subst_comm {T : Ty (s,X)} {U : Ty s} {σ : Subst s s'} :
  (T.open_tvar U).subst σ = (T.subst σ.liftTVar).open_tvar (U.subst σ) := by
  simp [Ty.open_tvar]
  simp [Ty.subst_comp]
  simp [Subst.open_tvar_subst_comm]
