import Cslib.Computability.LambdaCalculus.WellScoped.FSub.Debruijn

inductive Ty : Sig -> Type where
| top : Ty s
| tvar : TVar s -> Ty s
| arrow : Ty s -> Ty s -> Ty s
| poly : Ty s -> Ty (s,X) -> Ty s

def Ty.rename : Ty s1 -> Rename s1 s2 -> Ty s2
| .top, _ => .top
| .tvar X, ρ => .tvar (ρ.tvar X)
| .arrow A B, ρ => .arrow (A.rename ρ) (B.rename ρ)
| .poly A B, ρ => .poly (A.rename ρ) (B.rename ρ.liftTVar)

inductive Exp : Sig -> Type where
| var : Var s -> Exp s
| abs : Ty s -> Exp (s,x) -> Exp s
| tabs : Ty s -> Exp (s,X) -> Exp s
| app : Exp s -> Exp s -> Exp s
| tapp : Exp s -> Ty s -> Exp s

def Exp.rename : Exp s1 -> Rename s1 s2 -> Exp s2
| .var x, ρ => .var (ρ.var x)
| .abs A e, ρ => .abs (A.rename ρ) (e.rename ρ.liftVar)
| .tabs A e, ρ => .tabs (A.rename ρ) (e.rename ρ.liftTVar)
| .app e1 e2, ρ => .app (e1.rename ρ) (e2.rename ρ)
| .tapp e A, ρ => .tapp (e.rename ρ) (A.rename ρ)

theorem Ty.rename_id {T : Ty s} : T.rename Rename.id = T := by
  induction T
  case top => rfl
  case tvar => rfl
  case arrow A B ihA ihB => simp [Ty.rename, ihA, ihB]
  case poly A B ihA ihB => simp [Ty.rename, ihA, ihB]

theorem Exp.rename_id {e : Exp s} : e.rename Rename.id = e := by
  induction e
  case var => rfl
  case abs A e ih => simp [Exp.rename, ih, Ty.rename_id]
  case tabs A e ih => simp [Exp.rename, ih, Ty.rename_id]
  case app e1 e2 ih1 ih2 => simp [Exp.rename, ih1, ih2]
  case tapp e A ih => simp [Exp.rename, ih, Ty.rename_id]

theorem Ty.rename_comp {T : Ty s1} {f1 : Rename s1 s2} {f2 : Rename s2 s3} :
  (T.rename f1).rename f2 = T.rename (f1.comp f2) := by
  induction T generalizing s2 s3
  case top => rfl
  case tvar => rfl
  case arrow A B ihA ihB => simp [Ty.rename, ihA, ihB]
  case poly A B ihA ihB =>
    simp [Ty.rename, ihA]
    simp [Rename.comp_liftTVar]
    simp [ihB]

theorem Exp.rename_comp {e : Exp s1} {f1 : Rename s1 s2} {f2 : Rename s2 s3} :
  (e.rename f1).rename f2 = e.rename (f1.comp f2) := by
  induction e generalizing s2 s3
  case var => rfl
  case abs A e ih => simp [Exp.rename, ih, Ty.rename_comp, Rename.comp_liftVar]
  case tabs A e ih => simp [Exp.rename, ih, Ty.rename_comp, Rename.comp_liftTVar]
  case app e1 e2 ih1 ih2 => simp [Exp.rename, ih1, ih2]
  case tapp e A ih => simp [Exp.rename, ih, Ty.rename_comp]

theorem Ty.rename_succVar_comm {T : Ty s} :
  (T.rename f).rename Rename.succVar = (T.rename Rename.succVar).rename f.liftVar := by
  simp [Ty.rename_comp, Rename.rename_succVar_comm]

theorem Ty.rename_succTVar_comm {T : Ty s} :
  (T.rename f).rename Rename.succTVar = (T.rename Rename.succTVar).rename f.liftTVar := by
  simp [Ty.rename_comp, Rename.rename_succTVar_comm]

inductive Exp.IsVal : Exp s -> Prop where
| abs : IsVal (.abs T e)
| tabs : IsVal (.tabs T e)
