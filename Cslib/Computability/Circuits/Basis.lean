/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Init

@[expose] public section

/-! # Circuit Basis

A `Basis` defines the set of operations (gates) available in a circuit or formula.
Each operation declares an `Arity` — how many inputs it accepts — and provides
evaluation semantics via `Basis.eval`.

## Design

The key design choice is that `Basis.eval` requires a proof that the input list length
satisfies the operation's arity (`(arity op).admits bs.length`). This makes it impossible
to evaluate a gate with the wrong number of inputs at the type level. Because `Arity.admits`
has a `Decidable` instance, callers can obtain the proof via a run-time check when the
arity is not statically known.

The circuit complexity hierarchy motivates two standard bases:

- `BoundedFanInOp k` — AND/OR with fan-in at most `k`, NOT with arity 1.
  The abbreviation `NCOp := BoundedFanInOp 2` gives the canonical bounded fan-in
  basis used in **NC** circuits.
- `ACOp` — AND/OR with unbounded fan-in, NOT with arity 1.
  This is the basis used in **AC** circuits.

## Main definitions

- `Arity` — `.exactly k`, `.atMost k`, or `.any`
- `Arity.admits` — predicate: does an arity accept a given input count?
- `Basis` — typeclass pairing an `arity` function with a type-safe `eval`
- `BoundedFanInOp k` — Boolean operations with fan-in bounded by `k`
- `NCOp` — `BoundedFanInOp 2`, the standard bounded fan-in basis
- `ACOp` — Boolean operations with unbounded fan-in

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraB2009]
-/

namespace Cslib.Circuits

/-- An `Arity` specifies how many inputs a gate operation accepts:
exactly `k` inputs, at most `k` inputs, or any number of inputs. -/
inductive Arity where
  /-- The gate accepts exactly `k` inputs. -/
  | exactly : Nat → Arity
  /-- The gate accepts at most `k` inputs. -/
  | atMost : Nat → Arity
  /-- The gate accepts any number of inputs. -/
  | any : Arity
  deriving DecidableEq, Repr

/-- Predicate stating that arity `a` accepts `n` inputs.
For `.exactly k`, requires `n = k`; for `.atMost k`, requires `n ≤ k`;
for `.any`, always `True`. -/
@[simp]
def Arity.admits : Arity → Nat → Prop
  | .exactly k, n => n = k
  | .atMost k, n => n ≤ k
  | .any, _ => True

instance (a : Arity) (n : Nat) : Decidable (a.admits n) :=
  match a with
  | .exactly k => if h : n = k then isTrue h else isFalse h
  | .atMost k => if h : n ≤ k then isTrue h else isFalse h
  | .any => isTrue trivial

/-- A `Basis` defines the arity and evaluation semantics for a set of gate operations.
Each operation declares its arity, and `eval` requires a proof that the input list
has the correct length. -/
class Basis (Op : Type*) where
  /-- The arity of a gate operation. -/
  arity : Op → Arity
  /-- Evaluate a gate operation on a list of Boolean inputs of the correct length. -/
  eval : (op : Op) → (bs : List Bool) → (arity op).admits bs.length → Bool

/-- Boolean operations with fan-in bounded by `k`: AND and OR accept at most `k` inputs,
NOT accepts exactly 1. This models the bounded fan-in gates used in NC-style circuits. -/
inductive BoundedFanInOp (k : Nat) where
  /-- Boolean conjunction (bounded fan-in). -/
  | and
  /-- Boolean disjunction (bounded fan-in). -/
  | or
  /-- Boolean negation. -/
  | not
  deriving DecidableEq, Repr

/-- The bounded fan-in basis assigns arity `.atMost k` to AND and OR, arity `.exactly 1`
to NOT. AND folds `&&` with identity `true`, OR folds `||` with identity `false`. -/
instance : Basis (BoundedFanInOp k) where
  arity
    | .and => .atMost k
    | .or => .atMost k
    | .not => .exactly 1
  eval
    | .and, bs, _ => bs.foldl (· && ·) true
    | .or, bs, _ => bs.foldl (· || ·) false
    | .not, [b], _ => !b

/-- `NCOp` is the standard bounded fan-in basis with fan-in at most 2, corresponding
to the **NC** (Nick's Class) hierarchy in circuit complexity. -/
abbrev NCOp := BoundedFanInOp 2

/-- Boolean operations with unbounded fan-in: AND and OR accept any number of inputs,
NOT accepts exactly 1. This models the unbounded fan-in gates used in AC-style circuits. -/
inductive ACOp where
  /-- Boolean conjunction (unbounded fan-in). -/
  | and
  /-- Boolean disjunction (unbounded fan-in). -/
  | or
  /-- Boolean negation. -/
  | not
  deriving DecidableEq, Repr

/-- The unbounded fan-in basis assigns arity `.any` to AND and OR, arity `.exactly 1`
to NOT. AND folds `&&` with identity `true`, OR folds `||` with identity `false`. -/
instance : Basis ACOp where
  arity
    | .and => .any
    | .or => .any
    | .not => .exactly 1
  eval
    | .and, bs, _ => bs.foldl (· && ·) true
    | .or, bs, _ => bs.foldl (· || ·) false
    | .not, [b], _ => !b

end Cslib.Circuits
