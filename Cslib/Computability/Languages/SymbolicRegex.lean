/-
Copyright (c) 2026 Mohamad Al-Zawahreh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mohamad Al-Zawahreh
-/

import Mathlib.Order.BooleanAlgebra.Defs
import Mathlib.Order.BooleanAlgebra.Basic

import Mathlib.Data.Set.Basic

namespace Cslib.Computability.Languages

variable {α : Type*} [BooleanAlgebra α] -- The "Symbolic Alphabet" (Predicates)

/-- Symbolic Regular Expressions -/
inductive SymbolicRegex (α : Type*)
| empty : SymbolicRegex α
| epsilon : SymbolicRegex α
| atom (p : α) : SymbolicRegex α -- 'p' is a predicate, not a char
| union : SymbolicRegex α → SymbolicRegex α → SymbolicRegex α
| concat : SymbolicRegex α → SymbolicRegex α → SymbolicRegex α
| star : SymbolicRegex α → SymbolicRegex α
| complement : SymbolicRegex α → SymbolicRegex α -- The missing piece!
| intersect : SymbolicRegex α → SymbolicRegex α → SymbolicRegex α

end Cslib.Computability.Languages

namespace Cslib.Computability.Languages.SymbolicRegex

variable {α : Type*} [BooleanAlgebra α]

/-- Nullability Check (Does it accept empty string?) -/
def nullable : SymbolicRegex α → Bool
| .empty => false
| .epsilon => true
| .atom _ => false
| .union r1 r2 => nullable r1 || nullable r2
| .concat r1 r2 => nullable r1 && nullable r2
| .star _ => true
| .complement r => !nullable r
| .intersect r1 r2 => nullable r1 && nullable r2

/-- The Symbolic Derivative (Brzozowski)
    Given a concrete character 'c' and a satisfaction relation, what is the residual Regex? -/
def derivative {Char : Type} (satisfies : Char → α → Bool) (c : Char) :
    SymbolicRegex α → SymbolicRegex α
| .empty => .empty
| .epsilon => .empty
| .atom p => if satisfies c p then .epsilon else .empty
| .union r1 r2 => .union (derivative satisfies c r1) (derivative satisfies c r2)
| .concat r1 r2 =>
    if nullable r1 then
      .union (.concat (derivative satisfies c r1) r2) (derivative satisfies c r2)
    else
      .concat (derivative satisfies c r1) r2
| .star r => .concat (derivative satisfies c r) (.star r)
| .complement r => .complement (derivative satisfies c r)
| .intersect r1 r2 => .intersect (derivative satisfies c r1) (derivative satisfies c r2)

end Cslib.Computability.Languages.SymbolicRegex
