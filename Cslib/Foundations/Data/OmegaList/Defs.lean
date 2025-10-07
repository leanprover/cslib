/-
Copyright (c) 2025-present Ching-Tsun Chou All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/
import Mathlib.Data.Nat.Notation

/-!
# Definition of `ωList` and functions on infinite lists

An `ωList α` is an infinite sequence of elements of `α`.  It isbasically
a wrapper around the type `ℕ → α` which supports the dot-notation and
the analogues of many familiar API functions of `List α`.  In particular,
the element at postion `n : ℕ` of `s : ωList α` is obtained using the
function application notation `s n`.

In this file we define `ωList` and its API functions.
Most code below is adapted from Mathlib.Data.Stream.Defs.
-/

universe u v w
variable {α : Type u} {β : Type v} {δ : Type w}

/-- An `ωList α` is an infinite sequence of elements of `α`. -/
def ωList (α : Type u) := ℕ → α

namespace ωList

/-- Prepend an element to an ω-list. -/
def cons (a : α) (s : ωList α) : ωList α
  | 0 => a
  | n + 1 => s n

@[inherit_doc] scoped infixr:67 " :: " => cons

/-- Head of an ω-list: `ωList.head s = ωList.get s 0`. -/
abbrev head (s : ωList α) : α := s 0

/-- Tail of an ω-list: `ωList.tail (h :: t) = t`. -/
def tail (s : ωList α) : ωList α := fun i => s (i + 1)

/-- Drop first `n` elements of an ω-list. -/
def drop (n : ℕ) (s : ωList α) : ωList α := fun i => s (i + n)

/-- Proposition saying that all elements of an ω-list satisfy a predicate. -/
def All (p : α → Prop) (s : ωList α) := ∀ n, p (s n)

/-- Proposition saying that at least one element of an ω-list satisfies a predicate. -/
def Any (p : α → Prop) (s : ωList α) := ∃ n, p (s n)

/-- `a ∈ s` means that `a = ωList.get n s` for some `n`. -/
instance : Membership α (ωList α) :=
  ⟨fun s a => Any (fun b => a = b) s⟩

/-- Apply a function `f` to all elements of an ω-list `s`. -/
def map (f : α → β) (s : ωList α) : ωList β := fun n => f (s n)

/-- Zip two ω-lists using a binary operation:
`ωList.get n (ωList.zip f s₁ s₂) = f (ωList.get s₁) (ωList.get s₂)`. -/
def zip (f : α → β → δ) (s₁ : ωList α) (s₂ : ωList β) : ωList δ :=
  fun n => f (s₁ n) (s₂ n)

/-- Enumerate an ω-list by tagging each element with its index. -/
def enum (s : ωList α) : ωList (ℕ × α) := fun n => (n, s n)

/-- The constant ω-list: `ωList.get n (ωList.const a) = a`. -/
def const (a : α) : ωList α := fun _ => a

/-- Iterates of a function as an ω-list. -/
def iterate (f : α → α) (a : α) : ωList α
  | 0 => a
  | n + 1 => f (iterate f a n)

/-- Given functions `f : α → β` and `g : α → α`, `corec f g` creates an ω-list by:
1. Starting with an initial value `a : α`
2. Applying `g` repeatedly to get an ω-list of α values
3. Applying `f` to each value to convert them to β
-/
def corec (f : α → β) (g : α → α) : α → ωList β := fun a => map f (iterate g a)

/-- Given an initial value `a : α` and functions `f : α → β` and `g : α → α`,
`corecOn a f g` creates an ω-list by repeatedly:
1. Applying `f` to the current value to get the next ω-list element
2. Applying `g` to get the next value to process
This is equivalent to `corec f g a`. -/
def corecOn (a : α) (f : α → β) (g : α → α) : ωList β :=
  corec f g a

/-- Given a function `f : α → β × α`, `corec' f` creates an ω-list by repeatedly:
1. Starting with an initial value `a : α`
2. Applying `f` to get both the next ω-list element (β) and next state value (α)
This is a more convenient form when the next element and state are computed together. -/
def corec' (f : α → β × α) : α → ωList β :=
  corec (Prod.fst ∘ f) (Prod.snd ∘ f)

/-- Use a state monad to generate an ω-list through corecursion -/
def corecState {σ α} (cmd : StateM σ α) (s : σ) : ωList α :=
  corec Prod.fst (cmd.run ∘ Prod.snd) (cmd.run s)

-- corec is also known as unfolds
abbrev unfolds (g : α → β) (f : α → α) (a : α) : ωList β :=
  corec g f a

/-- Interleave two ω-lists. -/
def interleave (s₁ s₂ : ωList α) : ωList α :=
  corecOn (s₁, s₂) (fun ⟨s₁, _⟩ => head s₁) fun ⟨s₁, s₂⟩ => (s₂, tail s₁)

@[inherit_doc] infixl:65 " ⋈ " => interleave

/-- Elements of an ω-list with even indices. -/
def even (s : ωList α) : ωList α :=
  corec head (fun s => tail (tail s)) s

/-- Elements of an ω-list with odd indices. -/
def odd (s : ωList α) : ωList α :=
  even (tail s)

/-- Append an ω-list to a list. -/
def appendωList : List α → ωList α → ωList α
  | [], s => s
  | List.cons a l, s => a::appendωList l s

@[inherit_doc] infixl:65 " ++ₗ " => appendωList

/-- `take n s` returns a list of the `n` first elements of ω-list `s` -/
def take : ℕ → ωList α → List α
  | 0, _ => []
  | n + 1, s => List.cons (head s) (take n (tail s))

/-- Get the list containing the elements of `xs` from position `m` to `n - 1`. -/
def extract (xs : ωList α) (m n : ℕ) : List α :=
  take (n - m) (xs.drop m)

/-- An auxiliary definition for `ωList.cycle` corecursive def -/
protected def cycleF : α × List α × α × List α → α
  | (v, _, _, _) => v

/-- An auxiliary definition for `ωList.cycle` corecursive def -/
protected def cycleG : α × List α × α × List α → α × List α × α × List α
  | (_, [], v₀, l₀) => (v₀, l₀, v₀, l₀)
  | (_, List.cons v₂ l₂, v₀, l₀) => (v₂, l₂, v₀, l₀)

/-- Interpret a nonempty list as a cyclic ω-list. -/
def cycle : ∀ l : List α, l ≠ [] → ωList α
  | [], h => absurd rfl h
  | List.cons a l, _ => corec ωList.cycleF ωList.cycleG (a, l, a, l)

/-- Tails of an ω-list, starting with `ωList.tail s`. -/
def tails (s : ωList α) : ωList (ωList α) :=
  corec id tail (tail s)

/-- An auxiliary definition for `ωList.inits`. -/
def initsCore (l : List α) (s : ωList α) : ωList (List α) :=
  corecOn (l, s) (fun ⟨a, _⟩ => a) fun p =>
    match p with
    | (l', s') => (l' ++ [head s'], tail s')

/-- Nonempty initial segments of an ω-list. -/
def inits (s : ωList α) : ωList (List α) :=
  initsCore [head s] (tail s)

/-- A constant ω-list, same as `ωList.const`. -/
def pure (a : α) : ωList α :=
  const a

/-- Given an ω-list of functions and an ω-list of values, apply `n`-th function to `n`-th value. -/
def apply (f : ωList (α → β)) (s : ωList α) : ωList β := fun n => (f n) (s n)

@[inherit_doc] infixl:75 " ⊛ " => apply -- input as `\circledast`

/-- The ω-list of natural numbers: `ωList.get n ωList.nats = n`. -/
def nats : ωList ℕ := fun n => n

end ωList
