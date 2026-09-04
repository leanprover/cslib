/-
Copyright (c) 2026 Xueying Qin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xueying Qin
-/

module

public import Cslib.Languages.StatefulProcesses.Basic

set_option linter.style.header false in
set_option linter.style.longLine false in

@[expose] public section

namespace Cslib.StatefulProcesses

open Cslib.Mech

def Prefix.merge (prf1 prf2 : Prefix Pid Var Val FunId SelLabel) :
  Option (Prefix Pid Var Val FunId SelLabel) :=
  match prf1, prf2 with
  | .assign x1 e1, .assign x2 e2 =>

    -- if x1 = x2 ∧ e1 = e2 then .assign x1 e1 else none
    sorry
  | _, _ => none


def Process.merge (opr1 opr2 : Option (Process Pid Var Val FunId SelLabel ProcName)) :
  Option (Process Pid Var Val FunId SelLabel ProcName) :=
  match opr1, opr2 with
  | some .nil, some .nil => some .nil
  | some (.pre pre1 pr1), some (.pre pre2 pr2) =>
    sorry
  | _, _ => none
