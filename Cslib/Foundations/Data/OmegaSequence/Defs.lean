/-
Copyright (c) 2025 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou, Fabrizio Montesi
-/
import Mathlib.Data.Nat.Notation
import Mathlib.Data.FunLike.Basic
import Mathlib.Logic.Function.Iterate


/-!
# Definition of `ωSequence` and functions on infinite sequences

An `ωSequence α` is an infinite sequence of elements of `α`.  It is basically
a wrapper around the type `ℕ → α` which supports the dot-notation and
the analogues of many familiar API functions of `List α`.  In particular,
the element at postion `n : ℕ` of `s : ωSequence α` is obtained using the
function application notation `s n`.

In this file we define `ωSequence` and its API functions.
Most code below is adapted from Mathlib.Data.Stream.Defs.
-/

universe u v w
variable {α : Type u} {β : Type v} {δ : Type w}

/-- An `ωSequence α` is an infinite sequence of elements of `α`. -/
structure ωSequence (α : Type u) where
  get : ℕ → α

instance : FunLike (ωSequence α) ℕ α where
  coe := ωSequence.get
  coe_injective' := by grind [ωSequence, Function.Injective]

instance : Coe (ℕ → α) (ωSequence α) where
  coe f := ⟨f⟩

namespace ωSequence

/-- Head of an ω-sequence: `ωSequence.head s = ωSequence s 0`. -/
abbrev head (s : ωSequence α) : α := s 0

/-- Tail of an ω-sequence: `ωSequence.tail (h :: t) = t`. -/
def tail (s : ωSequence α) : ωSequence α := fun i => s (i + 1)

/-- Drop first `n` elements of an ω-sequence. -/
def drop (n : ℕ) (s : ωSequence α) : ωSequence α := fun i => s (i + n)

/-- `take n s` returns a list of the `n` first elements of ω-sequence `s` -/
def take : ℕ → ωSequence α → List α
  | 0, _ => []
  | n + 1, s => List.cons (head s) (take n (tail s))

/-- Get the list containing the elements of `xs` from position `m` to `n - 1`. -/
def extract (xs : ωSequence α) (m n : ℕ) : List α :=
  take (n - m) (xs.drop m)

/-- Prepend an element to an ω-sequence. -/
def cons (a : α) (s : ωSequence α) : ωSequence α
  | 0 => a
  | n + 1 => s n

@[inherit_doc] scoped infixr:67 " ::ω " => cons

/-- Append an ω-sequence to a list. -/
def appendωSequence : List α → ωSequence α → ωSequence α
  | [], s => s
  | List.cons a l, s => a ::ω appendωSequence l s

@[inherit_doc] infixl:65 " ++ω " => appendωSequence

/-- The constant ω-sequence: `ωSequence n (ωSequence.const a) = a`. -/
def const (a : α) : ωSequence α := fun (_ : ℕ) => a

/-- Apply a function `f` to all elements of an ω-sequence `s`. -/
def map (f : α → β) (s : ωSequence α) : ωSequence β := fun n => f (s n)

/-- Zip two ω-sequences using a binary operation:
`ωSequence n (ωSequence.zip f s₁ s₂) = f (ωSequence s₁) (ωSequence s₂)`. -/
def zip (f : α → β → δ) (s₁ : ωSequence α) (s₂ : ωSequence β) : ωSequence δ :=
  fun n => f (s₁ n) (s₂ n)

/-- Iterates of a function as an ω-sequence. -/
def iterate (f : α → α) (a : α) : ωSequence α := fun n => f^[n] a

end ωSequence
