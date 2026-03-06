/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Cryptography.Foundations.Indistinguishability
public import Cslib.Computability.Machines.SingleTapeTuring.Basic

@[expose] public section

/-!
# Poly-Time Distinguishers

This file bridges the abstract crypto definitions in `Indistinguishability.lean`
with the Turing-machine–based computability definitions.

## Main Definitions

* `PolyTimeEncodable` — a type class providing polynomial-length encodings to `List Bool`
* `IsPolyTimeDistinguisher` — a distinguisher computed by a poly-time Turing machine
* `PPTIndistinguishable` — computational indistinguishability restricted to PPT distinguishers

## Design Notes

`PolyTimeEncodable` bridges abstract crypto types (`α : ℕ → Type*`) to `List Bool`,
where `PolyTimeComputable` lives. The encoding length is polynomially bounded in `n`,
ensuring that poly-time on the encoding is poly-time in the security parameter.

`IsPolyTimeDistinguisher` requires that a single poly-time TM computes the
accept/reject decision on all encoded inputs. The output is deterministic (0 or 1),
modeling the standard accept/reject paradigm.
-/

open Turing Turing.SingleTapeTM Polynomial

/-- A type family `α : ℕ → Type*` is **poly-time encodable** if there exists
an encoding into `List Bool` with a polynomial length bound, together with
a decoding function that is a left inverse. -/
class PolyTimeEncodable (α : ℕ → Type*) where
  /-- Encode an element at security parameter `n` to a bitstring. -/
  encode : (n : ℕ) → α n → List Bool
  /-- Decode a bitstring back to an element. -/
  decode : (n : ℕ) → List Bool → Option (α n)
  /-- Decoding is a left inverse of encoding. -/
  encodeDecode : ∀ n a, decode n (encode n a) = some a
  /-- A polynomial bounding the length of encoded elements. -/
  lengthPoly : Polynomial ℕ
  /-- The encoding length is bounded by `lengthPoly.eval n`. -/
  encodeLengthBound : ∀ n (a : α n), (encode n a).length ≤ lengthPoly.eval n

/-- A family of functions `f : (n : ℕ) → α n → β n` is **poly-time computable**
if there exists a poly-time TM function on bitstrings that correctly computes
`f` when composed with the polynomial-time encodings.

Concretely, there exists `g : List Bool → List Bool` with a
`PolyTimeComputable g` proof such that decoding `g(encode(n, a))` at
security parameter `n` yields `f n a`. -/
def IsPolyTimeFamily {α β : ℕ → Type*}
    [PolyTimeEncodable α] [PolyTimeEncodable β]
    (f : (n : ℕ) → α n → β n) : Prop :=
  ∃ (g : List Bool → List Bool),
    Nonempty (PolyTimeComputable (Symbol := Bool) g) ∧
    ∀ n (a : α n),
      PolyTimeEncodable.decode n (g (PolyTimeEncodable.encode n a)) = some (f n a)

/-- A distinguisher is a **poly-time distinguisher** if there exists a poly-time
computable function `f : List Bool → List Bool` on bitstrings such that the
distinguisher's output (0 or 1) is determined by whether `f` returns a nonempty
list on the encoded input. -/
def IsPolyTimeDistinguisher {α : ℕ → Type*} [PolyTimeEncodable α]
    (D : Distinguisher α) : Prop :=
  ∃ (f : List Bool → List Bool),
    Nonempty (PolyTimeComputable (Symbol := Bool) f) ∧
    ∀ n (a : α n),
      D n a = if f (PolyTimeEncodable.encode n a) ≠ [] then 1 else 0

/-- A poly-time distinguisher is automatically bounded: its output is always
0 or 1, so it satisfies `IsBounded`. -/
theorem IsPolyTimeDistinguisher.isBounded
    {α : ℕ → Type*} [PolyTimeEncodable α]
    {D : Distinguisher α} (h : IsPolyTimeDistinguisher D) :
    D.IsBounded := by
  obtain ⟨f, _, hD⟩ := h
  intro n a
  rw [hD n a]
  split <;> norm_num

/-- Restricting the admissibility predicate preserves computational
indistinguishability: if all `Q`-admissible distinguishers are also
`P`-admissible, then `P`-indistinguishability implies `Q`-indistinguishability. -/
theorem CompIndistinguishable.mono
    {α : ℕ → Type*} [∀ n, Fintype (α n)]
    {P Q : Distinguisher α → Prop}
    {X Y : Ensemble α}
    (hPQ : ∀ D, Q D → P D)
    (h : CompIndistinguishable P X Y) :
    CompIndistinguishable Q X Y := by
  intro D hB hQ
  exact h D hB (hPQ D hQ)

/-- **PPT-indistinguishability**: two ensembles are computationally
indistinguishable against probabilistic polynomial-time distinguishers. -/
abbrev PPTIndistinguishable
    {α : ℕ → Type*} [∀ n, Fintype (α n)] [PolyTimeEncodable α]
    (X Y : Ensemble α) : Prop :=
  CompIndistinguishable IsPolyTimeDistinguisher X Y

end
