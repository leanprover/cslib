/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Languages.Mech.LocalComputation
public import Cslib.Foundations.Semantics.LTS.Basic

set_option linter.style.header false in
set_option linter.style.longLine false in
/-!
# Stateful Processes

The language of Stateful Processes (SP for short), a process calculus
where processes communicate via message passing [Montesi2023]. Stateful processes or similar
languages are typically used to model implementations of choreographic programs (concurrent and/or
distributed protocols), but they are also designed to be used as abstract representations that can
be later compiled to executable mainstream languages.

## Limitations

The current formalisation does not cover process polymorphism (procedures do not take process
parameters) nor general recursion (this is the tail-recursive fragment of Stateful Processes).
For recursion, only the syntax is currently implemented. Its semantics will follow a similar
approach to that for `CCS`.

## Implementation notes

This development follows the presentation in [Montesi2023], with one difference: we adopt a modular
approach to the definition of operational semantics, by first defining a symbolic semantics from
which a concrete semantics is then derived by adding stores (process memory). This approach is
described in [Acclavio2026].

## References

* [M. Acclavio, G. Manara, F. Montesi, X. Qin, *Choreographic Programming: a Semantic Approach*][Acclavio2026]
* [F. Montesi, *Introduction to Choreographies*][Montesi2023]
-/

@[expose] public section

namespace Cslib.StatefulProcesses

open Cslib.Mech

section Syntax

/-! ## Syntax of process terms -/

/-- Prefixes. -/
inductive Prefix (Pid Var Val FunId SelLabel : Type*) where
  /-- Assign to `x` the result of evaluating `e`. -/
  | assign (x : Var) (e : Expr Var Val FunId)
  /-- Send to `p` the result of evaluating `e`. -/
  | sendValue (p : Pid) (e : Expr Var Val FunId)
  /-- Receive a value from `p` and store it in `x`. -/
  | recvValue (p : Pid) (x : Var)
  /-- Send to `p` the label `l`. -/
  | sendLabel (p : Pid) (l : SelLabel)

/-- Processes. -/
inductive Process (Pid Var Val FunId SelLabel ProcName : Type*) where
  /-- The terminated process. -/
  | nil
  /-- Execute the prefix `prf` and proceed as the continuation `pr`. -/
  | pre (prf : Prefix Pid Var Val FunId SelLabel) (pr : Process Pid Var Val FunId SelLabel ProcName)
  /-- Branching process: receives a selection label and continues accordingly. -/
  | recvLabel (p : Pid) (branches : List (SelLabel × Process Pid Var Val FunId SelLabel ProcName))
  /-- Conditional: evaluate `e` to choose between `pr₁` and `pr₂`. -/
  | cond (e : Expr Var Val FunId) (pr₁ pr₂ : Process Pid Var Val FunId SelLabel ProcName)
  /-- Call the procedure `proc`. -/
  | call (proc : ProcName) (ps : List Pid)

instance : Zero (Process Pid Var Val FunId SelLabel ProcName) := ⟨.nil⟩

/-- Syntactic category for prefixes. -/
declare_syntax_cat spPre

@[inherit_doc Prefix.assign]
scoped syntax term:max "≔" term : spPre

@[inherit_doc Prefix.sendValue]
scoped syntax term:max "!" term : spPre

@[inherit_doc Prefix.recvValue]
scoped syntax term:max "?" term : spPre

@[inherit_doc Prefix.sendLabel]
scoped syntax term:max "⊕" term : spPre

@[inherit_doc Prefix]
scoped syntax "`(SPpre|" spPre ")" : term

scoped macro_rules
  | `(`(SPpre| $x:term ≔ $e:term )) => `(Prefix.assign $x $e)
  | `(`(SPpre| $p:term ! $e:term )) => `(Prefix.sendValue $p $e)
  | `(`(SPpre| $p:term ? $x:term )) => `(Prefix.recvValue $p $x)
  | `(`(SPpre| $p:term ⊕ $l:term )) => `(Prefix.sendLabel $p $l)

/-- Syntactic category for processes. -/
declare_syntax_cat spProc

@[inherit_doc Process.nil]
scoped syntax num : spProc

@[inherit_doc Process.pre]
scoped syntax spPre "; " spProc : spProc

@[inherit_doc Process.recvLabel]
scoped syntax term:max "&" term : spProc

@[inherit_doc Process.cond]
scoped syntax "if" term "then" spProc "else" spProc : spProc

-- The next syntax would be nice to have to avoid having trailing 0s in examples.
-- scoped syntax:min "`(SP| " spPre ")" : term

@[inherit_doc Process]
scoped syntax "`(SP| " spProc ")" : term

scoped macro_rules
  | `(`(SP| 0)) => `(0)
  | `(`(SP| $prf:spPre; $pr:spProc)) => `(Process.pre `(SPpre| $prf) `(SP| $pr))
  | `(`(SP| $p:term & $l:term)) => `(Process.recvLabel $p $l)
  | `(`(SP| if $e:term then $p₁:spProc else $p₂:spProc)) =>
    `(Process.cond $e `(SP| $p₁) `(SP| $p₂))

end Syntax

section Semantics

/-! ## Semantics -/

/-- Actions. -/
inductive Act (Pid Var Val FunId SelLabel : Type*) where
  /-- Assign to `x` the result of evaluating `e`. -/
  | assign (x : Var) (e : Expr Var Val FunId)
  /-- Send to `p` the result of evaluating `e`. -/
  | sendValue (p : Pid) (e : Expr Var Val FunId)
  /-- Receive a value from `p` and store it in variable `x`. -/
  | recvValue (p : Pid) (x : Var)
  /-- Send to `p` the selection label `l`. -/
  | sendLabel (p : Pid) (l : SelLabel)
  /-- Receive from `p` the selection label `l`. -/
  | recvLabel (p : Pid) (l : SelLabel)
  /-- Choose the then-branch of a conditional guarded by `e`. -/
  | condThen (e : Expr Var Val FunId)
  /-- Choose the else-branch of a conditional guarded by `e`. -/
  | condElse (e : Expr Var Val FunId)

/-- An action is internal if it is not meant to interact with another process. -/
def Act.isInternal : Act Pid Var Val FunId SelLabel → Bool
  | assign _ _ | condThen _ | condElse _ => true
  | _ => false

/-- Transforms a `Prefix` into an `Act`. -/
abbrev Prefix.toAct : Prefix Pid Var Val FunId SelLabel → Act Pid Var Val FunId SelLabel
  | assign x e => .assign x e
  | sendValue p e => .sendValue p e
  | recvValue p x => .recvValue p x
  | sendLabel p l => .sendLabel p l

/-- Symbolic transition relation for processes.
Do not use this directly, use `Process.lts` instead. -/
inductive Process.Tr :
    Process Pid Var Val FunId SelLabel ProcName → Act Pid Var Val FunId SelLabel →
    Process Pid Var Val FunId SelLabel ProcName → Prop
  | pre : Tr (pre prf pr) prf.toAct (pr)
  | condThen : Tr (cond e pr₁ pr₂) (.condThen e) pr₁
  | condElse : Tr (cond e pr₁ pr₂) (.condElse e) pr₂
  | recvLabel (h : (l, pr) ∈ branches): Tr (recvLabel p branches) (.recvLabel p l) pr

/-- Symbolic LTS of processes. -/
def Process.lts :
    LTS (Process Pid Var Val FunId SelLabel ProcName) (Act Pid Var Val FunId SelLabel) :=
  ⟨Process.Tr⟩

end Semantics

end Cslib.StatefulProcesses
