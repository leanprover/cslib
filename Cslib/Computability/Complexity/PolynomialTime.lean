/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic
public import Cslib.Foundations.Data.BitString
public import Cslib.Foundations.Data.Nat.PolynomialBoundIn

/-!
# Polynomial-time word functions and predicates

`FP f` means that a deterministic binary multi-tape Turing machine computes the ordinary word
function `f` in polynomial time. The auxiliary space bound is unrestricted; the class is defined
by time. `P f` specializes this to predicates represented by a single output bit.

The underlying machine predicate supplies finite control, read-only input, work tapes and an
append-only output. The running time is polynomially bounded in the input length, in the sense
of `PolynomiallyBoundedIn`, so any polynomial expression in the length is accepted.
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

/-- Word functions computed in polynomial time by a deterministic binary Turing machine. -/
@[fun_prop] def FP (f : BitString → BitString) : Prop :=
  ∃ t : BitString → ℕ, PolynomiallyBoundedIn t List.length ∧ ∃ s : BitString → ℕ,
    ComputableInTimeAndSpace f (Function.Embedding.refl _) (Function.Embedding.refl _) t s

/-- Predicates decided in polynomial time, with their answer emitted as a single bit. -/
@[fun_prop] def P (f : BitString → Bool) : Prop := FP (fun x => [f x])

/-- An existing polynomial-time machine computation is an FP witness. -/
@[fun_prop] theorem FP.of_computableInTimeAndSpace {f : BitString → BitString}
    {t s : BitString → ℕ}
    (h : ComputableInTimeAndSpace f (Function.Embedding.refl _) (Function.Embedding.refl _) t s)
    (ht : PolynomiallyBoundedIn t List.length) : FP f := ⟨t, ht, s, h⟩

/-- A language decided in polynomial time has its indicator in P. -/
theorem P.of_decidableInTimeAndSpace {L : Set BitString} {t s : BitString → ℕ}
    (h : DecidableInTimeAndSpace L (Function.Embedding.refl _) t s)
    (ht : PolynomiallyBoundedIn t List.length) : P (indicator L) :=
  let ⟨k, State, hfinite, tm, htm⟩ := h
  ⟨t, ht, s, k, State, hfinite, tm, fun a => htm a⟩

end Cslib.Complexity
