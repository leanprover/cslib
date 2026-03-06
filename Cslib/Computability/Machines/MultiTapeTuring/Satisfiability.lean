/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.MultiTapeTuring.Basic
public import Cslib.Computability.Machines.MultiTapeTuring.Encoding

namespace Turing

namespace Satisfiability

abbrev Var := ℕ

inductive Literal where
  | pos (v : Var)
  | neg (v : Var)

instance : StrEnc Literal where
  encInner
    | Literal.pos v => (StrEnc.enc 0) ++ (StrEnc.enc v)
    | Literal.neg v => (StrEnc.enc 1) ++ (StrEnc.enc v)
  maxDepth := 1
  fieldDepths := #[#[StrEnc.maxDepth ℕ], #[StrEnc.maxDepth ℕ]]
  hDepth := sorry
  hInj := sorry

def Clause := List Literal

def Formula := List Clause

--- The list of all positive variables.
def Assignments := List Var


end Satisfiability

end Turing
