import Mathlib.Tactic

inductive Sig : Type where
| empty : Sig
| cons_var : Sig -> Sig
| cons_tvar : Sig -> Sig

@[simp]
instance : EmptyCollection Sig := ⟨Sig.empty⟩

theorem Sig.empty_eq : {} = Sig.empty := rfl

postfix:50 ",x" => Sig.cons_var
postfix:50 ",X" => Sig.cons_tvar

inductive Var : Sig -> Type where
| here : Var (s,x)
| there_var : Var s -> Var (s,x)
| there_tvar : Var s -> Var (s,X)

inductive TVar : Sig -> Type where
| here : TVar (s,X)
| there_var : TVar s -> TVar (s,x)
| there_tvar : TVar s -> TVar (s,X)

structure Rename (s1 s2 : Sig) where
  var : Var s1 -> Var s2
  tvar : TVar s1 -> TVar s2

def Rename.liftVar (f : Rename s1 s2) : Rename (s1,x) (s2,x) := by
  constructor
  case var =>
    intro x; cases x
    case here => exact .here
    case there_var x0 => exact .there_var (f.var x0)
  case tvar =>
    intro X; cases X
    case there_var X0 => exact .there_var (f.tvar X0)

def Rename.liftTVar (f : Rename s1 s2) : Rename (s1,X) (s2,X) := by
  constructor
  case tvar =>
    intro X; cases X
    case here => exact .here
    case there_tvar X0 => exact .there_tvar (f.tvar X0)
  case var =>
    intro x; cases x
    case there_tvar x0 => exact .there_tvar (f.var x0)

def Rename.succVar : Rename s1 (s1,x) :=
  { var := fun x => x.there_var, tvar := fun X => X.there_var }

def Rename.succTVar : Rename s1 (s1,X) :=
  { var := fun x => x.there_tvar, tvar := fun X => X.there_tvar }

def Rename.id : Rename s s :=
  { var := fun x => x, tvar := fun X => X }

def Rename.comp (f1 : Rename s1 s2) (f2 : Rename s2 s3) : Rename s1 s3 :=
  { var := fun x => f2.var (f1.var x), tvar := fun X => f2.tvar (f1.tvar X) }

theorem Rename.funext {f g : Rename s1 s2}
  (var : ∀ x, f.var x = g.var x)
  (tvar : ∀ X, f.tvar X = g.tvar X) : f = g := by
  cases f; cases g
  simp
  constructor
  { funext x; aesop }
  { funext X; aesop }

@[simp]
theorem Rename.id_liftVar_eq_id : Rename.id.liftVar = (Rename.id (s:=(s,x))) := by
  apply Rename.funext
  case var => intro x; cases x <;> rfl
  case tvar => intro X; cases X; rfl

@[simp]
theorem Rename.id_liftTVar_eq_id : Rename.id.liftTVar = (Rename.id (s:=(s,X))) := by
  apply Rename.funext
  case var => intro x; cases x; rfl
  case tvar => intro X; cases X <;> rfl

theorem Rename.comp_liftTVar {f1 : Rename s1 s2} {f2 : Rename s2 s3} :
  (f1.comp f2).liftTVar = f1.liftTVar.comp f2.liftTVar := by
  apply Rename.funext
  case var => intro x; cases x; rfl
  case tvar => intro X; cases X <;> rfl

theorem Rename.comp_liftVar {f1 : Rename s1 s2} {f2 : Rename s2 s3} :
  (f1.comp f2).liftVar = f1.liftVar.comp f2.liftVar := by
  apply Rename.funext
  case var => intro x; cases x <;> rfl
  case tvar => intro X; cases X; rfl

theorem Rename.rename_succVar_comm {f : Rename s1 s2} :
  (f.comp Rename.succVar) = Rename.succVar.comp f.liftVar := by
  apply Rename.funext
  case var => intro x; rfl
  case tvar => intro X; rfl

theorem Rename.rename_succTVar_comm {f : Rename s1 s2} :
  (f.comp Rename.succTVar) = Rename.succTVar.comp f.liftTVar := by
  apply Rename.funext
  case var => intro x; rfl
  case tvar => intro X; rfl

def Sig.append : Sig -> Sig -> Sig
| s1, .empty => s1
| s1, .cons_var s2 => .cons_var (s1.append s2)
| s1, .cons_tvar s2 => .cons_tvar (s1.append s2)

@[simp]
instance : Append Sig := ⟨Sig.append⟩

def Rename.lift : Rename s1 s2 -> (s : Sig) -> Rename (s1 ++ s) (s2 ++ s)
| f, .empty => f
| f, .cons_var s => (f.lift s).liftVar
| f, .cons_tvar s => (f.lift s).liftTVar
