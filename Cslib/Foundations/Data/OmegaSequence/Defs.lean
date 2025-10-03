/-
Copyright (c) 2025-present Ching-Tsun Chou All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/
import Mathlib.Data.Nat.Notation

/-!
# Definition of `ωSequence` and functions on infinite sequences

An `ωSequence α` is an infinite sequence of elements of `α`.  It isbasically
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
def ωSequence (α : Type u) := ℕ → α

namespace ωSequence

/-- Prepend an element to an ω-sequence. -/
def cons (a : α) (s : ωSequence α) : ωSequence α
  | 0 => a
  | n + 1 => s n

@[inherit_doc] scoped infixr:67 " :: " => cons

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

/-- Append an ω-sequence to a list. -/
def appendωSequence : List α → ωSequence α → ωSequence α
  | [], s => s
  | List.cons a l, s => a::appendωSequence l s

@[inherit_doc] infixl:65 " ++ω " => appendωSequence

/-- Proposition saying that all elements of an ω-sequence satisfy a predicate. -/
def All (p : α → Prop) (s : ωSequence α) := ∀ n, p (s n)

/-- Proposition saying that at least one element of an ω-sequence satisfies a predicate. -/
def Any (p : α → Prop) (s : ωSequence α) := ∃ n, p (s n)

/-- `a ∈ s` means that `a = ωSequence n s` for some `n`. -/
instance : Membership α (ωSequence α) :=
  ⟨fun s a => Any (fun b => a = b) s⟩

/-- Apply a function `f` to all elements of an ω-sequence `s`. -/
def map (f : α → β) (s : ωSequence α) : ωSequence β := fun n => f (s n)

/-- Zip two ω-sequences using a binary operation:
`ωSequence n (ωSequence.zip f s₁ s₂) = f (ωSequence s₁) (ωSequence s₂)`. -/
def zip (f : α → β → δ) (s₁ : ωSequence α) (s₂ : ωSequence β) : ωSequence δ :=
  fun n => f (s₁ n) (s₂ n)

/-- The ω-sequence of natural numbers: `ωSequence n ωSequence.nats = n`. -/
def nats : ωSequence ℕ := fun n => n

/-- Enumerate an ω-sequence by tagging each element with its index. -/
def enum (s : ωSequence α) : ωSequence (ℕ × α) := fun n => (n, s n)

/-- The constant ω-sequence: `ωSequence n (ωSequence.const a) = a`. -/
def const (a : α) : ωSequence α := fun _ => a

/-- Iterates of a function as an ω-sequence. -/
def iterate (f : α → α) (a : α) : ωSequence α
  | 0 => a
  | n + 1 => f (iterate f a n)

/-- Given functions `f : α → β` and `g : α → α`, `corec f g` creates an ω-sequence by:
1. Starting with an initial value `a : α`
2. Applying `g` repeatedly to get an ω-sequence of α values
3. Applying `f` to each value to convert them to β
-/
def corec (f : α → β) (g : α → α) : α → ωSequence β := fun a => map f (iterate g a)

/-- Given an initial value `a : α` and functions `f : α → β` and `g : α → α`,
`corecOn a f g` creates an ω-sequence by repeatedly:
1. Applying `f` to the current value to get the next ω-sequence element
2. Applying `g` to get the next value to process
This is equivalent to `corec f g a`. -/
def corecOn (a : α) (f : α → β) (g : α → α) : ωSequence β :=
  corec f g a

/-- Given a function `f : α → β × α`, `corec' f` creates an ω-sequence by repeatedly:
1. Starting with an initial value `a : α`
2. Applying `f` to get both the next ω-sequence element (β) and next state value (α)
This is a more convenient form when the next element and state are computed together. -/
def corec' (f : α → β × α) : α → ωSequence β :=
  corec (Prod.fst ∘ f) (Prod.snd ∘ f)

/-- Use a state monad to generate an ω-sequence through corecursion -/
def corecState {σ α} (cmd : StateM σ α) (s : σ) : ωSequence α :=
  corec Prod.fst (cmd.run ∘ Prod.snd) (cmd.run s)

-- corec is also known as unfolds
abbrev unfolds (g : α → β) (f : α → α) (a : α) : ωSequence β :=
  corec g f a

/-- Interleave two ω-sequences. -/
def interleave (s₁ s₂ : ωSequence α) : ωSequence α :=
  corecOn (s₁, s₂) (fun ⟨s₁, _⟩ => head s₁) fun ⟨s₁, s₂⟩ => (s₂, tail s₁)

@[inherit_doc] infixl:65 " ⋈ " => interleave

/-- Elements of an ω-sequence with even indices. -/
def even (s : ωSequence α) : ωSequence α :=
  corec head (fun s => tail (tail s)) s

/-- Elements of an ω-sequence with odd indices. -/
def odd (s : ωSequence α) : ωSequence α :=
  even (tail s)

/-- An auxiliary definition for `ωSequence.cycle` corecursive def -/
protected def cycleF : α × List α × α × List α → α
  | (v, _, _, _) => v

/-- An auxiliary definition for `ωSequence.cycle` corecursive def -/
protected def cycleG : α × List α × α × List α → α × List α × α × List α
  | (_, [], v₀, l₀) => (v₀, l₀, v₀, l₀)
  | (_, List.cons v₂ l₂, v₀, l₀) => (v₂, l₂, v₀, l₀)

/-- Interpret a nonempty list as a cyclic ω-sequence. -/
def cycle : ∀ l : List α, l ≠ [] → ωSequence α
  | [], h => absurd rfl h
  | List.cons a l, _ => corec ωSequence.cycleF ωSequence.cycleG (a, l, a, l)

/-- Tails of an ω-sequence, starting with `ωSequence.tail s`. -/
def tails (s : ωSequence α) : ωSequence (ωSequence α) :=
  corec id tail (tail s)

/-- An auxiliary definition for `ωSequence.inits`. -/
def initsCore (l : List α) (s : ωSequence α) : ωSequence (List α) :=
  corecOn (l, s) (fun ⟨a, _⟩ => a) fun p =>
    match p with
    | (l', s') => (l' ++ [head s'], tail s')

/-- Nonempty initial segments of an ω-sequence. -/
def inits (s : ωSequence α) : ωSequence (List α) :=
  initsCore [head s] (tail s)

/-- A constant ω-sequence, same as `ωSequence.const`. -/
def pure (a : α) : ωSequence α :=
  const a

/-- Given an ω-sequence of functions and an ω-sequence of values,
apply `n`-th function to `n`-th value. -/
def apply (f : ωSequence (α → β)) (s : ωSequence α) : ωSequence β := fun n => (f n) (s n)

@[inherit_doc] infixl:75 " ⊛ " => apply -- input as `\circledast`

end ωSequence
