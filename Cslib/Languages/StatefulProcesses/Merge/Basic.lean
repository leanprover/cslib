/-
Copyright (c) 2026 Xueying Qin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xueying Qin
-/

module

public import Cslib.Languages.StatefulProcesses.Basic

/-! # Merging Stateful Process Prefixes -/

@[expose] public section

namespace Cslib.StatefulProcesses.Merge

open Cslib.Mech Cslib.StatefulProcesses

section Merge

/-- The merge operation for two prefixes. Two prefix are mergeable if they are equal. -/
def Prefix.merge
    [DecidableEq Pid]
    [DecidableEq Var]
    [DecidableEq Val]
    [DecidableEq FunId]
    [DecidableEq SelLabel]
    [DecidableEq (Expr Var Val FunId)]
    (opre1 opre2 : Option (Prefix Pid Var Val FunId SelLabel)) :
  Option (Prefix Pid Var Val FunId SelLabel) :=
  match opre1, opre2 with
  | some (.assign x1 e1), some (.assign x2 e2) =>
    if x1 = x2 ∧ e1 = e2 then some (.assign x1 e1) else none
  | some (.sendValue p1 e1), some (.sendValue p2 e2) =>
    if p1 = p2 ∧ e1 = e2 then some (.sendValue p1 e1) else none
  | some (.recvValue p1 x1), some (.recvValue p2 x2) =>
    if p1 = p2 ∧ x1 = x2 then some (.recvValue p1 x1) else none
  | some (.sendLabel p1 l1), some (.sendLabel p2 l2) =>
    if p1 = p2 ∧ l1 = l2 then some (.sendLabel p1 l1) else none
  | _, _ => none


def Process.merge
    [DecidableEq Pid]
    [DecidableEq Var]
    [DecidableEq Val]
    [DecidableEq FunId]
    [DecidableEq SelLabel]
    [LinearOrder SelLabel]
    [DecidableEq (Expr Var Val FunId)]
    (opr1 opr2 : Option (Process Pid Var Val FunId SelLabel ProcName)) :
    Option (Process Pid Var Val FunId SelLabel ProcName) :=
  match opr1, opr2 with
  | some .nil, some .nil => some .nil
  | some (.pre pre1 pr1), some (.pre pre2 pr2) =>
    match Prefix.merge (some pre1) (some pre2), Process.merge (some pr1) (some pr2) with
    | some pre, some pr => some (.pre pre pr)
    | _, _ => none
  | _, _ => none

end Merge
end Cslib.StatefulProcesses.Merge
