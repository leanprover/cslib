/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Cslib.Computability.Circuit.Basic
public import Cslib.Foundations.Data.BitString
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Tactic.DeriveFintype

/-!
# Boolean circuits

The De Morgan basis consists of binary AND and OR, unary NOT, and Boolean constants.
Every gate has fan-in at most two, so these are the usual bounded fan-in Boolean circuits
(`Program.fanInAtMost_two`). Circuit size counts every gate, including constants;
designated output wires are free.
-/

@[expose] public section

namespace Cslib.Circuits
namespace Boolean

/-- Operations of the De Morgan basis, including constants. -/
inductive Op where
  /-- A Boolean constant. -/
  | const (value : Bool)
  /-- Negation. -/
  | not
  /-- Binary conjunction. -/
  | and
  /-- Binary disjunction. -/
  | or
  deriving DecidableEq, Fintype

/-- The De Morgan basis has five operation symbols, counting its two constants. -/
@[simp] theorem Op.card : Fintype.card Op = 5 := rfl

/-- The De Morgan signature. -/
abbrev signature : Signature where
  Op := Op
  Arity
    | .const _ => 0
    | .not => 1
    | .and | .or => 2

/-- The usual Boolean interpretation. -/
def interpretation : Interpretation signature Bool
  | .const b, _ => b
  | .not, x => !x 0
  | .and, x => x 0 && x 1
  | .or, x => x 0 || x 1

end Boolean

/-- Every De Morgan program has fan-in at most two. -/
theorem Program.fanInAtMost_two {n g : ℕ} (p : Program Boolean.signature n g) :
    p.FanInAtMost 2 := by
  induction p with
  | empty => trivial
  | gate p line ih => exact And.intro ih (by cases line.op <;> simp)

/-- Every De Morgan circuit has fan-in at most two. -/
theorem Circuit.fanInAtMost_two {n g o : ℕ} (c : Circuit Boolean.signature n g o) :
    c.FanInAtMost 2 :=
  c.program.fanInAtMost_two

end Cslib.Circuits
