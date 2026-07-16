/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Languages.StatefulProcesses.Basic
public import Cslib.Foundations.Data.FinFun.Basic

/-! # Semantics of stateful process networks

## Implementation notes

We leverage the fact that networks are functions to formulate the semantics without requiring a
definition of parallel composition.

## References

* [F. Montesi, *Introduction to Choreographies*][Montesi2023]
-/

@[expose] public section

namespace Cslib.StatefulProcesses

open scoped FinFun

/-- A network maps process names to process terms. -/
abbrev Network (Pid Var Expr SelLabel ProcName : Type*) :=
  Pid → Process Pid Var Expr SelLabel ProcName

namespace Network

inductive TrLabel Pid Var Expr SelLabel ProcName : Network

def lts :
    LTS (Network Pid Var Expr SelLabel ProcName) (Pid × Act Pid Var Expr SelLabel) :=


end Network

end Cslib.StatefulProcesses
