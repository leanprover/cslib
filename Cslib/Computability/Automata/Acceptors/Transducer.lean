/-
Copyright (c) 2026 William (Liam) Schilling. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William (Liam) Schilling
-/

module

public import Cslib.Init
public import Mathlib.Algebra.Group.Basic

@[expose] public section

namespace Cslib.Automata

/-- A `Transducer` is a machine that assigns weights to input strings.
Typically, weights are from a `Monoid` or a `Semiring`,
though `Mul` suffices to state the definition.

The definition specializes to:
- weighted acceptors,
  by attaching an annihilator `none` to the weights
- functional string transducers,
  by having output strings as the weights
- partial functional string transducers,
  by having output strings with an annihilator `none` as the weights

In the definition, `T` is the type of the transducers.
The function recognized by a transducer `t : T` can
be accessed via `transduceFromLeft t` and `transduceFromRight t`.
In this sense, `T` and `t : T` are analogous to `a` and `a : A` in
the definition of the `Acceptor` type class. -/
class Transducer
    (T : Type u) (Symbol : outParam (Type v)) (Weight : outParam (Type w)) [Mul Weight] where

  /-- The function that assigns weights to input strings by
  accumulating weight onto `acc` via right-multiplication.
  That is, if `t` is meant to assign the weight `w` to the input string `xs`,
  then `transduceFromLeft t acc xs` should output `acc * w`.

  Passing an accumulator `acc` allows for a consistent direction of associativity,
  which is important because some types have a preferred direction for performance.
  The implemeter of `transduceFromLeft` should left-associate all multiplications,
  and the caller should always pass an accumulator
  in place of right-multiplying by the output of `transduceFromLeft`. -/
  transduceFromLeft (t : T) (acc : Weight) (xs : List Symbol) : Weight

  /-- The function that assigns weights to input strings by
  accumulating weight onto `acc` via left-multiplication.
  That is, if `t` is meant to assign the weight `w` to the input string `xs`,
  then `transduceFromRight t xs acc` should output `w * acc`.

  Passing an accumulator `acc` allows for a consistent direction of associativity,
  which is important because some types have a preferred direction for performance.
  The implemeter of `transduceFromRight` should right-associate all multiplications,
  and the caller should always pass an accumulator
  in place of left-multiplying by the output of `transduceFromRight`. -/
  transduceFromRight (t : T) (xs : List Symbol) (acc : Weight) : Weight

  /-- Proof that `transduceFromLeft` and `transduceFromRight` represent the same function. -/
  mul_transduceFromRight_eq_transduceFromLeft_mul
      (t : T) (acc₁ : Weight) (xs : List Symbol) (acc₂ : Weight) :
    acc₁ * transduceFromRight t xs acc₂ = transduceFromLeft t acc₁ xs * acc₂

  /-- Proof that `transduceFromLeft` works by accumulating weight onto `acc`. -/
  mul_transduceFromLeft_eq_transduceFromLeft
      (t : T) (acc₁ acc₂ : Weight) (xs : List Symbol) :
    acc₁ * transduceFromLeft t acc₂ xs = transduceFromLeft t (acc₁ * acc₂) xs

  /-- Proof that `transduceFromRight` works by accumulating weight onto `acc`. -/
  transduceFromRight_mul_eq_transduceFromRight
      (t : T) (xs : List Symbol) (acc₁ acc₂ : Weight) :
    transduceFromRight t xs acc₁ * acc₂ = transduceFromRight t xs (acc₁ * acc₂)

namespace Transducer

/- We choose the direction of simplification that
rewrites `transduceFromRight` as `transduceFromLeft` and pulls multiplication into the accumulator.
This is consistent with the left-associativity of the `Mul` operator. -/
attribute [simp, scoped grind =]
  mul_transduceFromRight_eq_transduceFromLeft_mul
  mul_transduceFromLeft_eq_transduceFromLeft
  transduceFromRight_mul_eq_transduceFromRight

variable {Symbol : Type v} {Weight : Type w}

section MulOneClass

variable [MulOneClass Weight]

/-- `transduceLeft` is the canonical version of `transduceFromLeft`.
It accumulates onto the empty weight `1`.

Recall that the caller should not right-multiply by the output of `transduceLeft` for performance.
Instead, the caller should pass the left-hand operand as an accumulator to `transduceFromLeft`. -/
abbrev transduceLeft [Transducer T Symbol Weight] (t : T) (xs : List Symbol) : Weight :=
  transduceFromLeft t 1 xs

/-- `transduceRight` is the canonical version of `transduceFromRight`.
It accumulates onto the empty weight `1`.

Recall that the caller should not left-multiply by the output of `transduceRight` for performance.
Instead, the caller should pass the right-hand operand as an accumulator to `transduceFromRight`. -/
abbrev transduceRight [Transducer T Symbol Weight] (t : T) (xs : List Symbol) : Weight :=
  transduceFromRight t xs 1

/-- `transduceLeft` and `transduceFromRight` represent the same function. -/
@[simp, scoped grind =]
theorem transduceFromRight_eq_transduceLeft_mul
    [Transducer T Symbol Weight] (t : T) (xs : List Symbol) (acc : Weight) :
    transduceFromRight t xs acc = transduceLeft t xs * acc := by
  rw [←one_mul (transduceFromRight t xs acc)]
  simp

/-- `transduceFromLeft` and `transduceRight` represent the same function. -/
theorem mul_transduceRight_eq_transduceFromLeft
    [Transducer T Symbol Weight] (t : T) (acc : Weight) (xs : List Symbol) :
    acc * transduceRight t xs = transduceFromLeft t acc xs := by
  simp

/-- `transduceLeft` and `transduceRight` represent the same function. -/
theorem transduceRight_eq_transduceLeft
    [Transducer T Symbol Weight] (t : T) (xs : List Symbol) :
    transduceRight t xs = transduceLeft t xs := by
  simp

/-- `transduceFromLeft` works by accumulating weight onto `acc`. -/
theorem mul_transduceLeft_eq_transduceFromLeft
    [Transducer T Symbol Weight] (t : T) (acc : Weight) (xs : List Symbol) :
    acc * transduceLeft t xs = transduceFromLeft t acc xs := by
  simp

/-- `transduceFromRight` works by accumulating weight onto `acc`. -/
theorem transduceRight_mul_eq_transduceFromRight
    [Transducer T Symbol Weight] (t : T) (xs : List Symbol) (acc : Weight) :
    transduceRight t xs * acc = transduceFromRight t xs acc := by
  simp

end MulOneClass

end Transducer

end Cslib.Automata
