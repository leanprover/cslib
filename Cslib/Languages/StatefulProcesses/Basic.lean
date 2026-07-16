/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Foundations.Semantics.LTS.Basic

/-!
# Stateful Processes

The language of Stateful Processes (SP for short), a process calculus
where processes communicate via message passing [Montesi2023]. Stateful processes or similar
languages are typically used to model implementations of choreographic programs, but they can also
be used as abstract representations that can be later compiled to executable mainstream languages.

## Limitations

The current formalisation does not cover process polymorphism (procedures do not take process
parameters) nor general recursion (this is the tail-recursive fragment of Stateful Processes)

## Implementation notes

This development faithfully follows the presentation in [Montesi2023] but for a minor difference:
we adopt a more structural approach to the operational semantics of the calculus, by defining
a semantics of observable actions for processes.

## References

* [F. Montesi, *Introduction to Choreographies*][Montesi2023]
-/

@[expose] public section

namespace Cslib.StatefulProcesses

section Syntax

/-! ## Syntax of process terms -/

/-- Prefixes. -/
inductive Process.Prefix (Pid Var Expr SelLabel : Type*) where
  /-- Assign to `x` the result of evaluating `e`. -/
  | assign (x : Var) (e : Expr)
  /-- Send to `p` the result of evaluating `e`. -/
  | sendValue (p : Pid) (e : Expr)
  /-- Receive a value from `p` and store it in `x`. -/
  | recvValue (p : Pid) (x : Var)
  /-- Send to `p` the label `l`. -/
  | sendLabel (p : Pid) (l : SelLabel)
deriving DecidableEq

/-- Processes. -/
inductive Process (Pid Var Expr SelLabel ProcName : Type*) where
  /-- The terminated process. -/
  | nil
  /-- Execute the prefix `prf` and proceed as the continuation `pr`. -/
  | pre (prf : Process.Prefix Pid Var Expr SelLabel) (pr : Process Pid Var Expr SelLabel ProcName)
  /-- Branching process: receives a selection label and continues accordingly. -/
  | recvLabel (p : Pid) (branches : List (SelLabel × Process Pid Var Expr SelLabel ProcName))
  /-- Conditional: evaluate `e` to choose between `pr₁` and `pr₂`. -/
  | cond (e : Expr) (pr₁ pr₂ : Process Pid Var Expr SelLabel ProcName)
  /-- Call the procedure `proc`. -/
  | call (proc : ProcName) (ps : List Pid)

instance : Zero (Process Pid Var Expr SelLabel ProcName) := ⟨.nil⟩

declare_syntax_cat pre
scoped syntax term "≔" term : pre
scoped syntax term "!" term : pre
scoped syntax term "?" term : pre
scoped syntax term "⊕" term : pre
scoped syntax "[SPpre|" pre "]" : term
scoped macro "[SPpre|" x:term "≔" e:term "]" : term => `(Process.Prefix.assign $x $e)
scoped macro "[SPpre|" p:term "!" e:term "]" : term => `(Process.Prefix.sendValue $p $e)
scoped macro "[SPpre|" p:term "?" x:term "]" : term => `(Process.Prefix.recvValue $p $x)
scoped macro "[SPpre|" p:term "⊕" l:term "]" : term => `(Process.Prefix.sendLabel $p $l)

declare_syntax_cat proc
scoped syntax num : proc
scoped syntax pre : proc
scoped syntax pre "; " proc : proc
scoped syntax "if" term "then" proc "else" proc : proc
scoped syntax "[SP|" proc "]" : term
scoped macro_rules
  | `([SP|0]) => `(0)
  | `([SP|$prf:pre; $pr:proc]) => `(Process.pre `([SPpre|$prf]) `([SP|$pr]))
  | `([SP|$prf:pre]) => `(Process.pre `([SPpre|$prf]) 0)
  | `([SP|if $e then $p₁:proc else $p₂:proc]) => `(Process.cond $e `([SP|$p₁]) `([SP|$p₂]))

end Syntax

section Semantics

/-! ## Semantics -/

/-- Actions. -/
inductive Act (Pid Var Expr SelLabel : Type*) where
  /-- Assign to `x` the result of evaluating `e`. -/
  | assign (x : Var) (e : Expr)
  /-- Send to `p` the result of evaluating `e`. -/
  | sendValue (p : Pid) (e : Expr)
  /-- Receive a value from `p` and store it in variable `x`. -/
  | recvValue (p : Pid) (x : Var)
  /-- Send to `p` the selection label `l`. -/
  | sendLabel (p : Pid) (l : SelLabel)
  /-- Receive from `p` the selection label `l`. -/
  | recvLabel (p : Pid) (l : SelLabel)
  /-- Choose the then-branch of a conditional guarded by `e`. -/
  | condThen (e : Expr)
  /-- Choose the else-branch of a conditional guarded by `e`. -/
  | condElse (e : Expr)
deriving DecidableEq

abbrev Process.Prefix.toAct : Process.Prefix Pid Var Expr SelLabel → Act Pid Var Expr SelLabel
  | assign x e => .assign x e
  | sendValue p e => .sendValue p e
  | recvValue p x => .recvValue p x
  | sendLabel p l => .sendLabel p l

/-- Transition relation for processes.
Do not use this directly, use `Process.lts` instead. -/
inductive Process.Tr :
    Process Pid Var Expr SelLabel ProcName → Act Pid Var Expr SelLabel →
    Process Pid Var Expr SelLabel ProcName → Prop
  | pre : Tr (pre prf pr) prf.toAct (pr)
  | condThen : Tr (cond e pr₁ pr₂) (.condThen e) pr₁
  | condElse : Tr (cond e pr₁ pr₂) (.condElse e) pr₂
  | recvLabel (h : (l, pr) ∈ branches): Tr (recvLabel p branches) (.recvLabel p l) pr

def Process.lts :
    LTS (Process Pid Var Expr SelLabel ProcName) (Act Pid Var Expr SelLabel) := ⟨Process.Tr⟩

end Semantics

end Cslib.StatefulProcesses
