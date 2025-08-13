import Cslib.Computability.LambdaCalculus.WellScoped.FSub.Syntax.Core

structure Subst (s1 s2 : Sig) where
  var : Var s1 -> Exp s2
  tvar : TVar s1 -> Ty s2

def Subst.liftVar (s : Subst s1 s2) : Subst (s1,x) (s2,x) := by
  constructor
  case var =>
    intro x; cases x
    case here => exact .var .here
    case there_var x0 => exact (s.var x0).rename Rename.succVar
  case tvar =>
    intro X; cases X
    case there_var X0 => exact (s.tvar X0).rename Rename.succVar

def Subst.liftTVar (s : Subst s1 s2) : Subst (s1,X) (s2,X) := by
  constructor
  case tvar =>
    intro X; cases X
    case here => exact .tvar .here
    case there_tvar X0 => exact (s.tvar X0).rename Rename.succTVar
  case var =>
    intro x; cases x
    case there_tvar x0 => exact (s.var x0).rename Rename.succTVar

def Subst.open_var (e : Exp s) : Subst (s,x) s := by
  constructor
  case var =>
    intro x; cases x
    case here => exact e
    case there_var x0 => exact .var x0
  case tvar =>
    intro X; cases X
    case there_var X0 => exact .tvar X0

def Subst.open_tvar (T : Ty s) : Subst (s,X) s := by
  constructor
  case var =>
    intro x; cases x
    case there_tvar x0 => exact .var x0
  case tvar =>
    intro X; cases X
    case here => exact T
    case there_tvar X0 => exact .tvar X0

def Rename.asSubst (f : Rename s1 s2) : Subst s1 s2 := by
  constructor
  case var => intro x; exact .var (f.var x)
  case tvar => intro X; exact .tvar (f.tvar X)

theorem Subst.funext {σ1 σ2 : Subst s1 s2}
  (var : ∀ x, σ1.var x = σ2.var x)
  (tvar : ∀ X, σ1.tvar X = σ2.tvar X) : σ1 = σ2 := by
  cases σ1; cases σ2
  simp
  constructor
  { funext x; aesop }
  { funext X; aesop }

def Subst.lift : Subst s1 s2 -> (s : Sig) -> Subst (s1 ++ s) (s2 ++ s)
| σ, .empty => σ
| σ, .cons_var s => (σ.lift s).liftVar
| σ, .cons_tvar s => (σ.lift s).liftTVar

def Subst.id : Subst s s := by
  constructor
  case var => intro x; exact .var x
  case tvar => intro X; exact .tvar X
