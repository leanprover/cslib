/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Foundations.Syntax.HasSubstitution

/-!
# Local expressions, stores, and evaluation

Choreographic programming and associated languages (like process calculi for modelling distributed
protocol implementations) are typically defined abstracting from how processes locally compute and
store values [Montesi2023]. This module defines this interface, as well as the derived concept of
global store.

## Implementation notes

The module is currently developed with minimality in mind. In the future, we plan on adding
facilities for typing expressions and easy integration with Lean and other IRs/FFIs.

## References

* [F. Montesi, *Introduction to Choreographies*][Montesi2023]
-/

@[expose] public section

namespace Cslib.Mech

/-- Expressions for local computation. -/
inductive Expr (Var Val FunId : Type*) where
  /-- Read variable `x`. -/
  | var (x : Var)
  /-- Value `v`. -/
  | val (v : Val)
  /-- Call function `f` with arguments `args`. -/
  | call (f : FunId) (args : List (Expr Var Val FunId))

/-- Utility instance to write variables directly as expressions. -/
instance : Coe Var (Expr Var Val FunId) where
  coe x := .var x

/-- Utility instance to write values directly as expressions. -/
instance : Coe Val (Expr Var Val FunId) where
  coe v := .val v

/-- A local store represents the memory state of a process, mapping variables to values. -/
abbrev LocalStore Var Val := (x : Var) → Val

/-- Type of (potentially nondeterministic) evaluation relations for local function calls at
processes. -/
abbrev FunCallEval FunId Val := (f : FunId) → (args : List Val) → Val → Prop

/-- Evaluation relation for expressions. -/
inductive FunCallEval.EvalExpr (eval : FunCallEval FunId Val) :
    (σ : LocalStore Var Val) → (e : Expr Var Val FunId) → (v : Val) → Prop where
  /-- A value evaluates to itself. -/
  | val : eval.EvalExpr σ (.val v) v
  /-- A variable evaluates to its mapped value in the store. -/
  | var : eval.EvalExpr σ (.var x) (σ x)
  /-- A function call first recursively evaluates its expression arguments, and then
  invokes the parameter for function evaluation. -/
  | call
    (hArgs : List.Forall₂ (eval.EvalExpr σ) args vals)
    (hFun : eval f vals v) :
    eval.EvalExpr σ (.call f args) v

/-- A global store represents the memory state of an entire system, mapping each process to its
local store. -/
abbrev GlobalStore Pid Var Val := (p : Pid) → LocalStore Var Val

/-- Type of an element of type `α` located at a process. -/
abbrev AtPid Pid α := Pid × α

/-- The process name of a located element. -/
abbrev AtPid.pid (a : AtPid Pid α) := a.fst

/-- The element of a located element. -/
abbrev AtPid.elem (a : AtPid Pid α) := a.snd

instance [DecidableEq Pid] [DecidableEq Var] :
    HasSubstitution (GlobalStore Pid Var Val) (AtPid Pid Var) Val where
  subst gs px v := gs[px.fst := ((gs px.pid)[px.elem := v])]

end Cslib.Mech
