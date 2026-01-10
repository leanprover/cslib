import Cslib.Computability.Languages.SymbolicRegex
import Mathlib.Data.Set.Basic
import Mathlib.Order.BooleanAlgebra.Defs
import Mathlib.Order.BooleanAlgebra.Basic


namespace CslibTests.SymbolicRegex

open Cslib.Computability.Languages
open Cslib.Computability.Languages.SymbolicRegex

-- We use `Set Nat` as our Boolean Algebra of predicates.
-- Characters are `Nat`.
abbrev Pred := Set Nat

-- Satisfaction relation: c satisfies P iff c ∈ P
def satisfies (c : Nat) (P : Pred) : Bool := c ∈ P

-- Helpers for predicates
def isEven : Pred := { n | n % 2 = 0 }
def isOdd  : Pred := { n | n % 2 = 1 }
def isZero : Pred := { 0 }

-- 1. Test Nullable
def r_eps : SymbolicRegex Pred := .epsilon
def r_empty : SymbolicRegex Pred := .empty
def r_even : SymbolicRegex Pred := .atom isEven
def r_star_even : SymbolicRegex Pred := .star r_even

example : nullable r_eps = true := rfl
example : nullable r_empty = false := rfl
example : nullable r_even = false := rfl -- Atomic predicates consume a character
example : nullable r_star_even = true := rfl

-- 2. Test Derivative
-- derivative of 'even' by 2 (even) -> epsilon
example : derivative satisfies 2 r_even = .epsilon := by
  -- 2 is even, so distinct from empty
  simp [derivative, satisfies, isEven]
  rfl

-- derivative of 'even' by 1 (odd) -> empty
example : derivative satisfies 1 r_even = .empty := by
  simp [derivative, satisfies, isEven]
  rfl

-- derivative of (even*) by 2 -> even . even*
-- (derivative of star r is (deriv r) . star r)
example : derivative satisfies 2 r_star_even = .concat .epsilon r_star_even := by
  simp [derivative, satisfies, isEven]
  rfl

-- 3. Complex Example
-- r = (even . odd)
def r_seq : SymbolicRegex Pred := .concat r_even (.atom isOdd)

-- deriv 2 r_seq -> (nullable even ? ... ) no. -> (deriv 2 even) . odd -> epsilon . odd
example : derivative satisfies 2 r_seq = .concat .epsilon (.atom isOdd) := by
  -- Just verify correct structure
  dsimp [r_seq, derivative, nullable, satisfies, isEven]
  simp [derivative]
  rfl

end CslibTests.SymbolicRegex
