/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Init

/-!
# Signatures and variables for local computation

Choreographic programming and associated languages (like process calculi for modelling distributed
protocol implementations) are typically defined abstracting from how processes locally compute and
store values [Montesi2023].

This module defines this interface. Local signatures (`LocalSig`) define the variables available to
a process. Signatures of networks (`Sig`) assign a local signature to each process. Similarly, we
define local stores (`LocalSig.Store`) mapping local variables to values, and global stores
(`Sig.Store`) mapping processes to their local stores.

## Implementation notes

Stores may assign different value types to different variables. Local computation uses plain Lean
functions and relations (for modelling nondeterminism). Expressions are typed and keep a small
syntax: values, variable reads, pairs, and calls of relations, so that the variables read by an
expression can be computed (`LocalSig.Expr.vars`). A call `.call r e` may evaluate to any `b` such
that `r a b`, where `a` is a value of `e`, which allows for nondeterministic local computations. A
deterministic call of a Lean function `f` is the call of its graph, written `f <$> e` or with the
braced notation `{f e}`.

Processes have independent local signatures, so the same variable name may denote variables of
different types in different processes. A variable of process `p` in a signature `S` has
type `S.Var p α`.

Local signatures include decidable equality of variable names, which is required by the write
operation for stores.

## Limitations and future work

The API currently requires going through Lean for any internal computation, and all computations
are lifted as opaque nondeterministic computations. Future work will consider better support for:
- Monadic computations in Lean (e.g., to capture probabilistic computations).
- Second-stage compilation to other languages (e.g., C, Python, Rust).
- Direct integration of other embedded languages (e.g., λ-calculus, which currently needs to go
through encodings).

## References

* [F. Montesi, *Introduction to Choreographies*][Montesi2023]
-/

@[expose] public section

namespace Cslib.Mech

/-! ## Local signatures -/

/-- A local signature, specifying variable names with their types. -/
structure LocalSig.{u, v} where
  /-- The type of variable names. -/
  VarName : Type u
  /-- Variable names have decidable equality. -/
  [decEq : DecidableEq VarName]
  /-- The type of the values stored in each variable. -/
  VarType : VarName → Type v

attribute [instance] LocalSig.decEq

namespace LocalSig

/-- A variable of type `α` under the local signature `L`. -/
structure Var (L : LocalSig.{u, v}) (α : Type v) : Type u where
  /-- The variable's name. -/
  name : L.VarName
  /-- Proof that the variable has type `α` in `L`. -/
  has_type : L.VarType name = α

/-- The type `α` of a variable `x : L.Var α`. -/
abbrev Var.Type {L : LocalSig} {α} (_ : L.Var α) := α

/-- Variables of different types necessarily have different names. -/
theorem Var.name_ne_of_type_ne {L : LocalSig} {α β} (h : α ≠ β) (x : L.Var α) (y : L.Var β) :
    x.name ≠ y.name :=
  fun e => h (x.has_type.symm.trans (e ▸ y.has_type))

end LocalSig

/-! ## Signatures of networks -/

set_option linter.checkUnivs false in
/-- The signature of a network, which assigns a local signature to each process. -/
abbrev Sig.{u,v,w} (Pid : Type u) := Pid → LocalSig.{v, w}

namespace Sig

/-- A variable of type `α` of process `p`. -/
abbrev Var {Pid} (S : Sig Pid) (p : Pid) (α : Type*) := (S p).Var α

end Sig

end Cslib.Mech
