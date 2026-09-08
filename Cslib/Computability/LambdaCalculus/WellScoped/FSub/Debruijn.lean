/-
Copyright (c) 2025 Yichen Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yichen Xu.
-/

/-
# Intrinsically scoped de Bruijn indices

This module defines the foundation for intrinsically scoped de Bruijn indices used throughout
the System F<: mechanization.
Instead of using raw natural numbers for de Bruijn indices,
variables and type variables are indexed by a signature (`Sig`) that describes
the available binders in the context.

This approach ensures that syntactic constructs are well-scoped by construction,
eliminating the possibility of free variables and making theorems easier to state and prove.

The module defines:
- `Sig`: Signatures that describe the structure of typing contexts
- `Var` and `TVar`: Intrinsically scoped variables and type variables
- `Rename`: Renamings between different signatures
- Context lifting operations for working under binders
-/

import Mathlib.Tactic

/-- A signature describes the structure of a typing context, tracking both
    term variables and type variables in the order they were introduced. -/
inductive Sig : Type where
| empty : Sig
/-- Extend signature with a term variable -/
| push_var : Sig → Sig
/-- Extend signature with a type variable -/
| push_tvar : Sig → Sig

@[simp]
instance : EmptyCollection Sig := ⟨Sig.empty⟩

theorem Sig.empty_eq : {} = Sig.empty := rfl

/-- Convenient syntax for extending a signature with a term variable -/
postfix:50 ",x" => Sig.push_var
/-- Convenient syntax for extending a signature with a type variable -/
postfix:50 ",X" => Sig.push_tvar

/-- Term variables indexed by signatures. A `Var s` represents a term variable
    that is valid in signature `s`. The constructors correspond to different ways
    a variable can be accessed from the current context. -/
inductive Var : Sig → Type where
/-- The most recently bound term variable -/
| here : Var (s,x)
/-- Skip over the most recent term variable -/
| there_var : Var s → Var (s,x)
/-- Skip over the most recent type variable -/
| there_tvar : Var s → Var (s,X)

/-- Type variables indexed by signatures. A `TVar s` represents a type variable
    that is valid in signature `s`. -/
inductive TVar : Sig → Type where
/-- The most recently bound type variable -/
| here : TVar (s,X)
/-- Skip over the most recent term variable -/
| there_var : TVar s → TVar (s,x)
/-- Skip over the most recent type variable -/
| there_tvar : TVar s → TVar (s,X)

/-- A renaming between signatures `s1` and `s2` specifies how to map variables
    from `s1` to variables in `s2`. This is the foundation for all variable
    renamings in the mechanization. -/
structure Rename (s1 s2 : Sig) where
  /-- How to rename term variables -/
  var : Var s1 → Var s2
  /-- How to rename type variables -/
  tvar : TVar s1 → TVar s2

/-- Lift a renaming to work under a new term variable binder. The new term variable
    is mapped to itself, while existing variables are renamed and shifted. -/
def Rename.liftVar (f : Rename s1 s2) : Rename (s1,x) (s2,x) where
  var := fun x => match x with
    | .here => .here
    | .there_var x0 => .there_var (f.var x0)
  tvar := fun X => match X with
    | .there_var X0 => .there_var (f.tvar X0)

/-- Lift a renaming to work under a new type variable binder. The new type variable
    is mapped to itself, while existing variables are renamed and shifted. -/
def Rename.liftTVar (f : Rename s1 s2) : Rename (s1,X) (s2,X) where
  tvar := fun X => match X with
    | .here => .here
    | .there_tvar X0 => .there_tvar (f.tvar X0)
  var := fun x => match x with
    | .there_tvar x0 => .there_tvar (f.var x0)

/-- Weakening renaming that adds a new term variable to the context.
    All existing variables are shifted to account for the new binding. -/
def Rename.succVar : Rename s1 (s1,x) where
  var := fun x => x.there_var
  tvar := fun X => X.there_var

/-- Weakening renaming that adds a new type variable to the context.
    All existing variables are shifted to account for the new binding. -/
def Rename.succTVar : Rename s1 (s1,X) where
  var := fun x => x.there_tvar
  tvar := fun X => X.there_tvar

/-- The identity renaming that maps each variable to itself. -/
def Rename.id : Rename s s where
  var := fun x => x
  tvar := fun X => X

/-- Composition of renamings. If `f1` renames from `s1` to `s2` and `f2` renames
    from `s2` to `s3`, then their composition renames from `s1` to `s3`. -/
def Rename.comp (f1 : Rename s1 s2) (f2 : Rename s2 s3) : Rename s1 s3 where
  var := fun x => f2.var (f1.var x)
  tvar := fun X => f2.tvar (f1.tvar X)

/-- Two renamings are equal if they map variables in the same way. -/
theorem Rename.funext {f g : Rename s1 s2}
  (var : ∀ x, f.var x = g.var x)
  (tvar : ∀ X, f.tvar X = g.tvar X) : f = g := by
  cases f; cases g
  aesop

/-- Lifting the identity renaming gives the identity renaming. -/
@[simp]
theorem Rename.id_liftVar_eq_id : Rename.id.liftVar = (Rename.id (s:=(s,x))) := by
  apply Rename.funext <;> intro x <;> cases x <;> rfl

/-- Lifting the identity renaming gives the identity renaming. -/
@[simp]
theorem Rename.id_liftTVar_eq_id : Rename.id.liftTVar = (Rename.id (s:=(s,X))) := by
  apply Rename.funext <;> intro X <;> cases X <;> rfl

/-- Composition commutes with lifting over type variables. -/
theorem Rename.comp_liftTVar {f1 : Rename s1 s2} {f2 : Rename s2 s3} :
  (f1.comp f2).liftTVar = f1.liftTVar.comp f2.liftTVar := by
  apply Rename.funext <;> intro X <;> cases X <;> rfl

/-- Composition commutes with lifting over term variables. -/
theorem Rename.comp_liftVar {f1 : Rename s1 s2} {f2 : Rename s2 s3} :
  (f1.comp f2).liftVar = f1.liftVar.comp f2.liftVar := by
  apply Rename.funext <;> intro x <;> cases x <;> rfl

/-- Composing with variable weakening commutes with lifting. -/
theorem Rename.rename_succVar_comm {f : Rename s1 s2} :
  (f.comp Rename.succVar) = Rename.succVar.comp f.liftVar := by
  apply Rename.funext <;> aesop

/-- Composing with type variable weakening commutes with lifting. -/
theorem Rename.rename_succTVar_comm {f : Rename s1 s2} :
  (f.comp Rename.succTVar) = Rename.succTVar.comp f.liftTVar := by
  apply Rename.funext <;> aesop

/-- Append two signatures, concatenating their binder sequences. -/
def Sig.append : Sig → Sig → Sig
| s1, .empty => s1
| s1, .push_var s2 => .push_var (s1.append s2)
| s1, .push_tvar s2 => .push_tvar (s1.append s2)

@[simp]
instance : Append Sig := ⟨Sig.append⟩

/-- Lift a renaming to work under multiple binders specified by a signature.
    This is the generalization of `liftVar` and `liftTVar` to arbitrary sequences of binders. -/
def Rename.lift : Rename s1 s2 → (s : Sig) → Rename (s1 ++ s) (s2 ++ s)
| f, .empty => f
| f, .push_var s => (f.lift s).liftVar
| f, .push_tvar s => (f.lift s).liftTVar
