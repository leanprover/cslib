/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Languages.Mech.LocalComputation
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

## Implementation notes

Choreographies are polymorphic in the types of participant, selection label, and procedure name
types, and in the universes of the signature. As in Stateful
Processes, the guard of a conditional may have any value type with a designated true value
(`Cslib.HasTrue`), such as `Bool` or `Prop`.

Local expressions in choreographies can use the notation for the syntactic category `mechExpr`; for
example, a braced Lean computation, as in `p.{$x + 1} ⮕ q.y`.

## References

* [F. Montesi, *Introduction to Choreographies*][Montesi2023]
-/

@[expose] public section

namespace Cslib.Languages.Mech

open Cslib.Mech

universe u v w

section Syntax

/-! ## Syntax of choreographies -/

/-- Choreographic prefix. -/
inductive Prefix (Pid : Type u) (S : Sig.{u, v, w} Pid) (SelLabel : Type*) where
  /-- `p` assigns `x` the value computed from `e`. -/
  | assign {α : Type w} (p : Pid) (x : S.Var p α) (e : S.Expr p α)
  /-- `p` communicates the evaluation of `e` to `q`, which stores it in its variable `x`. -/
  | com {α : Type w} (p : Pid) (e : S.Expr p α) (q : Pid) (x : S.Var q α)
  /-- `p` communicates the selection label (a static tag used to denote a choice) to `q`. -/
  | sel (p : Pid) (q : Pid) (l : SelLabel)

/-- Choreographies. -/
inductive Choreography (Pid : Type u) (S : Sig.{u, v, w} Pid) (SelLabel ProcName : Type*) where
  /-- The terminated choreography. -/
  | nil
  /-- Do `prf` and continue as `c`. -/
  | pre (prf : Prefix Pid S SelLabel)
    (c : Choreography Pid S SelLabel ProcName)
  /-- Conditional: `p` evaluates the guard `e`, continuing as `c₁` if it evaluates to the true value
  of its guard type (see `HasTrue`) and as `c₂` otherwise. -/
  | cond {α : Type w} [inst : HasTrue α] (p : Pid) (e : S.Expr p α)
    (c₁ c₂ : Choreography Pid S SelLabel ProcName)
  /-- Call the procedure `proc`. -/
  | call (proc : ProcName) (ps : List Pid)

variable {Pid : Type u} {S : Sig.{u, v, w} Pid} {SelLabel ProcName : Type*}

instance : Zero (Choreography Pid S SelLabel ProcName) := ⟨.nil⟩

/-- Syntactic category for prefixes. -/
declare_syntax_cat mechPre

@[inherit_doc Prefix.assign]
scoped syntax term:max "." term "≔" mechExpr : mechPre

@[inherit_doc Prefix.com]
scoped syntax term:max "." mechExpr "⮕" term:max "." term : mechPre

@[inherit_doc Prefix.sel]
scoped syntax term:max "⮕" term:max "[" term "]" : mechPre

@[inherit_doc Prefix]
scoped syntax "`(MechPre|" mechPre ")" : term

scoped macro_rules
  | `(`(MechPre| $p:term . $x:term ≔ $e:mechExpr)) => `(Prefix.assign $p $x `(MechExpr| $e))
  | `(`(MechPre| $p:term . $e:mechExpr ⮕ $q:term . $x:term)) =>
    `(Prefix.com $p `(MechExpr| $e) $q $x)
  | `(`(MechPre| $p:term ⮕ $q:term [ $l:term ])) => `(Prefix.sel $p $q $l)

/-- Syntactic category for choreographies. -/
declare_syntax_cat mechChor

@[inherit_doc Choreography.nil]
scoped syntax num : mechChor

@[inherit_doc Choreography.pre]
scoped syntax mechPre "; " mechChor : mechChor

@[inherit_doc Choreography.cond]
scoped syntax "if" term:max "." mechExpr "then" mechChor "else" mechChor : mechChor

@[inherit_doc Choreography]
scoped syntax "`(Mech| " mechChor ")" : term

scoped macro_rules
  | `(`(Mech| 0)) => `(0)
  | `(`(Mech| $prf:mechPre; $pr:mechChor)) => `(Choreography.pre `(MechPre| $prf) `(Mech| $pr))
  | `(`(Mech| if $p:term . $e:mechExpr then $c₁:mechChor else $c₂:mechChor)) =>
    `(Choreography.cond $p `(MechExpr| $e) `(Mech| $c₁) `(Mech| $c₂))

variable [DecidableEq Pid]

/-- Process names in a prefix. -/
def Prefix.pn : Prefix Pid S SelLabel → Finset Pid
  | assign p _ _ => {p}
  | com p _ q _ | sel p q _ => {p, q}

/-- Process names in a choreography. -/
def Choreography.pn : Choreography Pid S SelLabel ProcName → Finset Pid
  | 0 => ∅
  | pre prf c => prf.pn ∪ c.pn
  | cond p _ c₁ c₂ => {p} ∪ c₁.pn ∪ c₂.pn
  | call _ args => args.toFinset

end Syntax

end Cslib.Languages.Mech
