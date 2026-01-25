/-
Copyright (c) 2026 William (Liam) Schilling. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William (Liam) Schilling
-/

module

public import Cslib.Computability.Automata.DA.Basic
public import Cslib.Computability.Automata.Transducers.Transducer

@[expose] public section

/-! # Deterministic Transducers

Deterministic transducer models
(not to be confused with the special case of typical deterministic FSTs `DetTransducer`)
accumulate output by traversing one or more underlying deterministic automata (`DA`)
according to an input string.

Transducers with different underlying automata are defined:
- `DetTransducer`: typical deterministics FSTs over one automaton for look-left

## References

* [Stoyan Mihov, Klaus U. Schulz,
  *Finite-State Techniques: Automata, Transducers and Bimachines*][Mihov2019]
-/

namespace Cslib.Automata

namespace DA

variable {State Symbol Weight : Type*}

/-- A `DetTransducer` is a `DA` with a weight attached to:
- the transition into the start state (`startWeight`)
- every transition step between states (`stepWeight`)
- every final transition out of a state (`finalWeight`)

Every transition traversed by an input string accumulates the attached weight by multiplication.

Equivalently, a `DetTransducer` may be thought of as mapping each position of the input string
to a weight with look-left via the state reached by an underlying `DA`, but with no look-right.
This interpretation is more analogous to the interpretation of a `Bimachine`. -/
structure DetTransducer (State Symbol Weight : Type*) extends DA State Symbol where
  startWeight : Weight
  stepWeight : State → Symbol → Weight
  finalWeight : State → Weight

namespace DetTransducer

section Mul

variable [Mul Weight]

/-- Accumulate weight onto the right of `acc` by
traversing according to the input string `xs` and starting from the state `s`.

This function handles step weights and final weights, but not the start weight.
The full transduction function is given by
passing the start weight into `acc` and the start state as `s`,
as in `DetTransducer.instTransducer.transduceFromLeft` later.

The implementation is designed to left-associate multiplication.
The right-associative version is `runRight`. -/
def runLeft
    (dt : DetTransducer State Symbol Weight) (acc : Weight) (xs : List Symbol) (s : State) :
    Weight :=
  match xs with
  | [] => acc * dt.finalWeight s
  | x :: xs => runLeft dt (acc * dt.stepWeight s x) xs (dt.tr s x)

/-- Accumulate weight onto the left of `acc` by
traversing according to the input string `xs` and starting from the state `s`.

This function handles step weights and final weights, but not the start weight.
The full transduction function is given by
adjoining the start weight and passing the start state as `s`,
as in `DetTransducer.instTransducer.transduceFromRight` later.

The implementation is designed to right-associate multiplication.
The left-associative version is `runLeft`. -/
def runRight
    (dt : DetTransducer State Symbol Weight) (xs : List Symbol) (acc : Weight) (s : State) :
    Weight :=
  match xs with
  | [] => dt.finalWeight s * acc
  | x :: xs => dt.stepWeight s x * runRight dt xs acc (dt.tr s x)

end Mul

section Semigroup

variable [Semigroup Weight]

/-- `runLeft` works by accumulating weight onto `acc`. -/
@[simp, scoped grind =]
theorem mul_runLeft_eq_runLeft
    dt (acc₁ acc₂ : Weight) (xs : List Symbol) (s : State) :
    acc₁ * runLeft dt acc₂ xs s = runLeft dt (acc₁ * acc₂) xs s := by
  induction xs generalizing acc₂ s with
  | nil => simp [mul_assoc, runLeft]
  | cons x xs ih => simp [mul_assoc, runLeft, ih]

/-- `runRight` works by accumulating weight onto `acc`. -/
@[simp, scoped grind =]
theorem runRight_mul_eq_runRight
    dt (xs : List Symbol) (acc₁ acc₂ : Weight) (s : State) :
    runRight dt xs acc₁ s * acc₂ = runRight dt xs (acc₁ * acc₂) s := by
  induction xs generalizing s with
  | nil => simp [mul_assoc, runRight]
  | cons x xs ih => simp [mul_assoc, runRight, ih]

/-- `runLeft` and `runRight` represent the same function. -/
@[simp, scoped grind =]
theorem mul_runRight_eq_runLeft_mul
    dt (acc₁ : Weight) (xs : List Symbol) (acc₂ : Weight) (s : State) :
    acc₁ * runRight dt xs acc₂ s = runLeft dt acc₁ xs s * acc₂ := by
  induction xs generalizing acc₁ s with
  | nil => simp [mul_assoc, runLeft, runRight]
  | cons x xs ih => simp [←mul_assoc, runLeft, runRight, ih]

/-- A `Transducer` instance for `DetTransducer`
exposing the recognized transduction via `transduceFromLeft` and `transduceFromRight`. -/
@[simp, scoped grind =]
instance : Transducer (DetTransducer State Symbol Weight) Symbol Weight where
  transduceFromLeft dt (acc : Weight) (xs : List Symbol) :=
    runLeft dt (acc * dt.startWeight) xs dt.start
  transduceFromRight dt (xs : List Symbol) (acc : Weight) :=
    dt.startWeight * runRight dt xs acc dt.start
  mul_transduceFromRight_eq_transduceFromLeft_mul dt acc₁ xs acc₂ := by
    simp [←mul_assoc]
  mul_transduceFromLeft_eq_transduceFromLeft dt acc₁ acc₂ xs := by
    simp [mul_assoc]
  transduceFromRight_mul_eq_transduceFromRight dt xs acc₁ acc₂ := by
    simp [mul_assoc]

end Semigroup

end DetTransducer

end DA

end Cslib.Automata
