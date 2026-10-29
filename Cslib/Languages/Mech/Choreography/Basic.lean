/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Init
public import Mathlib.Data.Finset.Basic

/-!
# Choreography

A choreography defines the collective behaviour of a system of communicating participants
(processes) [Montesi2023].

## Limitations

Some notable features not yet included:
- Recursion (only the syntax is implemented, but no semantics).
- General recursion (the current syntax supports only tail recursion).
- Choreographic choice (for barriers, first-come/first-served patterns, etc.).
- Asynchronous communication.

## References

* [F. Montesi, *Introduction to Choreographies*][Montesi2023]
-/

@[expose] public section

namespace Cslib.Languages.Mech

section Syntax

/-! ## Syntax of choreographies -/

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

/-- Choreographic prefix. -/
inductive Prefix (Pid Var Val FunId SelLabel : Type*) where
  /-- `p` assigns `x` the value computed from `e`. -/
  | assign (p : Pid) (x : Var) (e : Expr Var Val FunId)
  /-- `p` communicates the evaluation of `e` to `q`, which stores it in its variable `x`. -/
  | com (p : Pid) (e : Expr Var Val FunId) (q : Pid) (x : Var)
  /-- `p` communicates the selection label (a static tag used to denote a choice) to `q`. -/
  | sel (p : Pid) (q : Pid) (l : SelLabel)

/-- Choreographies. -/
inductive Choreography (Pid Var Val FunId SelLabel ProcName : Type*) where
  /-- The terminated choreography. -/
  | nil
  /-- Do `prf` and continue as `c`. -/
  | pre (prf : Prefix Pid Var Val FunId SelLabel)
    (c : Choreography Pid Var Val FunId SelLabel ProcName)
  /-- Conditional: `p` evaluates `e` to choose between `c₁` and `c₂`. -/
  | cond (p : Pid) (e : Expr Var Val FunId)
    (c₁ c₂ : Choreography Pid Var Val FunId SelLabel ProcName)
  /-- Call the procedure `proc`. -/
  | call (proc : ProcName) (ps : List Pid)

instance : Zero (Choreography Pid Var Val FunId SelLabel ProcName) := ⟨.nil⟩

/-- Syntactic category for prefixes. -/
declare_syntax_cat mechPre

@[inherit_doc Prefix.assign]
scoped syntax term:max "." term "≔" term : mechPre

@[inherit_doc Prefix.com]
scoped syntax term:max "." term "⮕" term:max "." term : mechPre

@[inherit_doc Prefix.sel]
scoped syntax term:max "⮕" term:max "[" term "]" : mechPre

@[inherit_doc Prefix]
scoped syntax "`(MechPre|" mechPre ")" : term

scoped macro_rules
  | `(`(MechPre| $p:term . $x:term ≔ $e:term)) => `(Prefix.assign $p $x $e)
  | `(`(MechPre| $p:term . $e:term ⮕ $q:term . $x:term)) => `(Prefix.com $p $e $q $x)
  | `(`(MechPre| $p:term ⮕ $q:term [ $l:term ])) => `(Prefix.sel $p $q $l)

/-- Syntactic category for choreographies. -/
declare_syntax_cat mechChor

@[inherit_doc Choreography.nil]
scoped syntax num : mechChor

@[inherit_doc Choreography.pre]
scoped syntax mechPre "; " mechChor : mechChor

@[inherit_doc Choreography.cond]
scoped syntax "if" term:max "." term "then" mechChor "else" mechChor : mechChor

@[inherit_doc Choreography]
scoped syntax "`(Mech| " mechChor ")" : term

scoped macro_rules
  | `(`(Mech| 0)) => `(0)
  | `(`(Mech| $prf:mechPre; $pr:mechChor)) => `(Choreography.pre `(MechPre| $prf) `(Mech| $pr))
  | `(`(Mech| if $p:term . $e:term then $c₁:mechChor else $c₂:mechChor)) =>
    `(Choreography.cond $p $e `(Mech| $c₁) `(Mech| $c₂))

variable [DecidableEq Pid]

/-- Process names in a prefix. -/
def Prefix.pn : Prefix Pid Var Val FunId SelLabel → Finset Pid
  | assign p _ _ => {p}
  | com p _ q _ | sel p q _ => {p, q}

/-- Process names in a choreography. -/
def Choreography.pn : Choreography Pid Var Val FunId SelLabel ProcName → Finset Pid
  | 0 => ∅
  | pre prf c => prf.pn ∪ c.pn
  | cond p _ c₁ c₂ => {p} ∪ c₁.pn ∪ c₂.pn
  | call _ args => args.toFinset

end Syntax

end Cslib.Languages.Mech
