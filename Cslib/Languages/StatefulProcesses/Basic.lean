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

In process syntax, expressions can use the notation for the syntactic
category `mechExpr`, see `Cslib.Languages.Mech.LocalComputation`): `{f $x $y}` applies a Lean
function to participant-local variables `x` and `y`, `{term}` embeds a Lean term, and any term of
type `L.Expr α` can be used directly.

This development otherwise follows the presentation in [Montesi2023], with one difference: we adopt a modular
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

universe u v w

section Syntax

/-! ## Syntax of process terms -/

/-- A prefix of a stateful process. -/
inductive Prefix (Pid : Type u) (L : LocalSig.{v, w}) (SelLabel : Type*)
  /-- Assign a local variable. -/
  | assign {α : Type w} (x : L.Var α) (e : L.Expr α)
  /-- Send a value to a participant. -/
  | sendValue {α : Type w} (p : Pid) (e : L.Expr α)
  /-- Receive a value in a local variable. -/
  | recvValue {α : Type w} (p : Pid) (x : L.Var α)
  /-- Send a selection label. -/
  | sendLabel (p : Pid) (l : SelLabel)

/-- Processes with typed local computations. -/
inductive Process (Pid : Type u) (L : LocalSig.{v, w}) (SelLabel ProcName : Type*)
  /-- Terminate. -/
  | nil
  /-- Execute a prefix and continue. -/
  | pre (prf : Prefix Pid L SelLabel) (pr : Process Pid L SelLabel ProcName)
  /-- Branch on a received label. -/
  | recvLabel (p : Pid) (branches : List (SelLabel × Process Pid L SelLabel ProcName))
  /-- Branch on a local computation `e`: continue as `pr₁` if `e` evaluates to the true value of its
  guard type (see `HasTrue`) and as `pr₂` otherwise. -/
  | cond {α : Type w} [inst : HasTrue α] (e : L.Expr α)
    (pr₁ pr₂ : Process Pid L SelLabel ProcName)
  /-- Call the procedure `proc`. -/
  | call (proc : ProcName) (ps : List Pid)

variable {Pid : Type u} {L : LocalSig.{v, w}} {SelLabel ProcName : Type*}

instance : Zero (Process Pid L SelLabel ProcName) := ⟨.nil⟩

/-- Syntactic category for prefixes. Local expressions use the shared category `mechExpr`. -/
declare_syntax_cat spPre

@[inherit_doc Prefix.assign]
scoped syntax term:max "≔" mechExpr : spPre

@[inherit_doc Prefix.sendValue]
scoped syntax term:max "!" mechExpr : spPre

@[inherit_doc Prefix.recvValue]
scoped syntax term:max "?" term : spPre

@[inherit_doc Prefix.sendLabel]
scoped syntax term:max "⊕" term : spPre

@[inherit_doc Prefix]
scoped syntax "`(SPpre|" spPre ")" : term

scoped macro_rules
  | `(`(SPpre| $x:term ≔ $e:mechExpr )) => `(Prefix.assign $x `(MechExpr| $e))
  | `(`(SPpre| $p:term ! $e:mechExpr )) => `(Prefix.sendValue $p `(MechExpr| $e))
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

/-- Branch on a local expression whose type has a designated true value (see `HasTrue`), such as
`Bool` or `Prop`. A braced guard `{…}` may read local variables with `$`. -/
scoped syntax "if" mechExpr "then" spProc "else" spProc : spProc

-- The next syntax would be nice to have to avoid having trailing 0s in examples.
-- scoped syntax:min "`(SP| " spPre ")" : term

@[inherit_doc Process]
scoped syntax "`(SP| " spProc ")" : term

scoped macro_rules
  | `(`(SP| 0)) => `(0)
  | `(`(SP| $prf:spPre; $pr:spProc)) => `(Process.pre `(SPpre| $prf) `(SP| $pr))
  | `(`(SP| $p:term & $l:term)) => `(Process.recvLabel $p $l)
  | `(`(SP| if $e:mechExpr then $p₁:spProc else $p₂:spProc)) =>
    `(Process.cond `(MechExpr| $e) `(SP| $p₁) `(SP| $p₂))

end Syntax

section Semantics

variable {Pid : Type*} {L : LocalSig.{u, v}} {SelLabel ProcName : Type*}

/-! ## Semantics -/

/-- Symbolic actions. -/
inductive Act (Pid : Type u) (L : LocalSig.{v, w}) (SelLabel : Type*)
  | assign {α : Type w} (x : L.Var α) (e : L.Expr α)
  | sendValue {α : Type w} (p : Pid) (e : L.Expr α)
  | recvValue {α : Type w} (p : Pid) (x : L.Var α)
  | sendLabel (p : Pid) (l : SelLabel)
  | recvLabel (p : Pid) (l : SelLabel)
  | condThen {α : Type w} [inst : HasTrue α] (e : L.Expr α)
  | condElse {α : Type w} [inst : HasTrue α] (e : L.Expr α)

/-- An action is internal if it is not meant to interact with another process. -/
def Act.isInternal : Act Pid L SelLabel → Bool
  | assign _ _ | condThen _ | condElse _ => true
  | _ => false

/-- Transforms a `Prefix` into an `Act`. -/
abbrev Prefix.toAct : Prefix Pid L SelLabel → Act Pid L SelLabel
  | assign x e => .assign x e
  | sendValue p e => .sendValue p e
  | recvValue p x => .recvValue p x
  | sendLabel p l => .sendLabel p l

/-- Symbolic transition relation for processes.
Do not use this directly, use `Process.lts` instead. -/
inductive Process.Tr :
    Process Pid L SelLabel ProcName → Act Pid L SelLabel →
    Process Pid L SelLabel ProcName → Prop
  | pre : Tr (pre prf pr) prf.toAct (pr)
  | condThen {α} {_ : HasTrue α} {e : L.Expr α} : Tr (cond e pr₁ pr₂) (.condThen e) pr₁
  | condElse {α} {_ : HasTrue α} {e : L.Expr α} : Tr (cond e pr₁ pr₂) (.condElse e) pr₂
  | recvLabel (h : (l, pr) ∈ branches): Tr (recvLabel p branches) (.recvLabel p l) pr

/-- Symbolic LTS of processes. -/
def Process.lts :
    LTS (Process Pid L SelLabel ProcName) (Act Pid L SelLabel) :=
  ⟨Process.Tr⟩

end Semantics

end Cslib.StatefulProcesses
