/-
Copyright (c) 2026 William (Liam) Schilling. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William (Liam) Schilling
-/

module

public import Cslib.Init
public import Mathlib.Algebra.Group.Basic

@[expose] public section

namespace CSlib.Automata

/-- A `Transducer` is a machine that assigns weights from a `Semigroup` to input strings.

The definition specializes to:
- weighted acceptors,
  by attaching an annihilator `none` to the weights
- functional string transducers,
  by having output strings as the weights
- partial functional string transducers,
  by having output strings with an annihilator `none` as the weights -/
class Transducer
    (T : Type u) (Symbol : outParam (Type v)) (Weight : outParam (Type w)) [Semigroup Weight] where
  /-- The function that assigns weights to input strings
  by accumulating weight between `accL` and `accR`.
  That is, if `t` is meant to assign the weight `w` to the input string `xs`,
  then `transduceFrom t xs accL accR` should output `accL * w * accR`.

  Accumulating weight between an initial `accL` and `accR` is beneficial for two reasons:
  - Othwerise, some transducer instances would need to enforce that
    weights be from a `Monoid` to guarentee inhabitation by `1`.
    In the case of this definition, it is `accL` and `accR` that guarentee inhabitation.
  - It gives the implementer control over the associativity of multiplications.
    e.g. In the case of strings (`List`), it is computationally redundant
    to left-multiply (`List.append`) by the result of a transduction.
    The implementer can avoid this if the right-hand operand is instead passed as `accR`. -/
  transduceFrom (t : T) (xs : List Symbol) (accL accR : Weight) : Weight

  /-- Proof that `transduceFrom` does, indeed, work by accumulating weight onto `accL`. -/
  mul_transduceFrom (t : T) (xs : List Symbol) (accL accR acc' : Weight) :
    acc' * transduceFrom t xs accL accR = transduceFrom t xs (acc' * accL) accR

  /-- Proof that `transduceFrom` does, indeed, work by accumulating weight onto `accR`. -/
  transduceFrom_mul (t : T) (xs : List Symbol) (accL accR acc' : Weight) :
    transduceFrom t xs accL accR * acc' = transduceFrom t xs accL (accR * acc')

namespace Transducer

/- We choose the direction of simplification that pulls multiplication into the accumulator.
The motivation is cases like `transduceFrom t xs 1 1 * acc = transduceFrom t xs 1 acc`,
which are not handled by the other choice of direction. -/
attribute [simp, scoped grind =] Transducer.mul_transduceFrom Transducer.transduceFrom_mul

variable {Symbol : Type v} {Weight : Type w}

section Monoid

variable [Monoid Weight]

/-- When weights are from a `Monoid`, `transduce` is the canonical version
of the weight assignment function. It accumulates onto the empty weight `1`. -/
abbrev transduce [Transducer T Symbol Weight] (t : T) (xs : List Symbol) : Weight :=
  transduceFrom t xs 1 1

/-- Left-multiplication after transduction is equivalent to
passing the left-hand operand as an accumulator. -/
theorem mul_transduce
    [Transducer T Symbol Weight] (t : T) (xs : List Symbol) (accL : Weight) :
    accL * transduce t xs = transduceFrom t xs accL 1 := by
  simp

/-- Right-multiplication after transduction is equivalent to
passing the right-hand operand as an accumulator. -/
theorem transduce_mul
    [Transducer T Symbol Weight] (t : T) (xs : List Symbol) (accR : Weight) :
    transduce t xs * accR = transduceFrom t xs 1 accR := by
  simp

/-- Multiplication after transduction is equivalent to
passing the operands as accumulators. -/
theorem mul_transduce_mul
    [Transducer T Symbol Weight] (t : T) (xs : List Symbol) (accL accR : Weight) :
    accL * transduce t xs * accR = transduceFrom t xs accL accR := by
  simp

end Monoid

end Transducer

end CSlib.Automata
