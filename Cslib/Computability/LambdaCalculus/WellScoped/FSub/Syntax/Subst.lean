import Cslib.Computability.LambdaCalculus.WellScoped.FSub.Substitution.Core

def Ty.subst : Ty s1 -> Subst s1 s2 -> Ty s2
| .top, _ => .top
| .tvar X, s => s.tvar X
| .arrow A B, s => .arrow (A.subst s) (B.subst s)
| .poly A B, s => .poly (A.subst s) (B.subst s.liftTVar)

def Exp.subst : Exp s1 -> Subst s1 s2 -> Exp s2
| .var x, s => s.var x
| .abs A e, s => .abs (A.subst s) (e.subst s.liftVar)
| .tabs A e, s => .tabs (A.subst s) (e.subst s.liftTVar)
| .app e1 e2, s => .app (e1.subst s) (e2.subst s)
| .tapp e A, s => .tapp (e.subst s) (A.subst s)

def Ty.open_tvar (T : Ty (s,X)) (U : Ty s) : Ty s :=
  T.subst (Subst.open_tvar U)

def Exp.open_var (e : Exp (s,x)) (U : Exp s) : Exp s :=
  e.subst (Subst.open_var U)

def Exp.open_tvar (e : Exp (s,X)) (U : Ty s) : Exp s :=
  e.subst (Subst.open_tvar U)
