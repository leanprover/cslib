/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Cslib.Computability.Circuit.Basic

/-!
# Boolean circuits

The De Morgan basis consists of binary AND and OR, unary NOT, and Boolean constants.
Circuit size counts every gate, including constants; designated output wires are free.
-/

@[expose] public section

namespace Cslib.Circuits
namespace Boolean

/-- Boolean functions on `n` inputs. -/
abbrev BooleanFunction (n : ℕ) := (Fin n → Bool) → Bool

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
  deriving DecidableEq

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

/-- A single-output De Morgan circuit computes `f` if its output agrees with `f` on every input. -/
def Circuit.Computes {n g : ℕ} (c : Circuit Boolean.signature n g 1)
    (f : Boolean.BooleanFunction n) : Prop :=
  ∀ x, c.eval Boolean.interpretation x 0 = f x

end Cslib.Circuits
