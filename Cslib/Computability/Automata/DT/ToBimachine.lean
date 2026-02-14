/-
Copyright (c) 2026 William (Liam) Schilling. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William (Liam) Schilling
-/

module

public import Cslib.Computability.Automata.DT.Basic

@[expose] public section

/-! # Translation of Deterministic Transducers into Bimachines

The translation is by
using the underlying automaton of the transducer as the look-left automaton and
using a useless automaton as the look-right automaton.

## Golfing notice

There are four instances in this file of a nasty rewrite statement like this:

```
  rw [show (fun (sr : Unit) => _ * dt.toBimachine.stepWeight _ sr _) =
            (fun (_ : Unit) => _ * dt.toBimachine.stepWeight _ () _) from rfl]
```

Surely there is a better way to do this.
-/

namespace Cslib.Automata.DT.DetTransducer

open Transducer

variable {State Symbol Weight : Type*}

/-- `DetTransducer` is a special case of `Bimachine`. -/
@[scoped grind =]
def toBimachine (dt : DetTransducer State Symbol Weight) :
    Bimachine State Unit Symbol Weight where
  daLeft := dt.toDA
  daRight := DA.unit Symbol
  startWeight _ := dt.startWeight
  stepWeight (s : State) _ := dt.stepWeight s
  finalWeight (s : State) := dt.finalWeight s

section Mul

variable [Mul Weight]

/-- The constructed `Bimachine` has an equivalent `runLeft`. -/
@[simp]
theorem toBimachine_runLeft
    (dt : DetTransducer State Symbol Weight) (acc : Weight) (xs : List Symbol) (s : State) :
    dt.toBimachine.runLeft (fun () => acc) xs s = dt.runLeft acc xs s := by
  induction xs generalizing acc s with
  | nil => rfl
  | cons x xs ih =>
    simp only [DetTransducer.runLeft, Bimachine.runLeft]
    rw [show (fun sr => _ * dt.toBimachine.stepWeight _ sr _) =
              (fun _ => _ * dt.toBimachine.stepWeight _ () _) from rfl]
    rw [ih]; rfl

end Mul

section Semigroup

variable [Semigroup Weight]

/-- The constructed `Bimachine` has an equivalent `runRight`. -/
@[simp]
theorem toBimachine_runRight
    (dt : DetTransducer State Symbol Weight)
    (acc₁ : Weight) (xs : List Symbol) (acc₂ : Weight) (s : State) :
    dt.toBimachine.runRight (fun () w => acc₁ * w) xs acc₂ s = acc₁ * dt.runRight xs acc₂ s := by
  induction xs generalizing acc₁ acc₂ s with
  | nil => rfl
  | cons x xs ih =>
    simp only [←mul_assoc, DetTransducer.runRight, Bimachine.runRight]
    rw [show (fun sr _ => _ * dt.toBimachine.stepWeight _ sr _ * _) =
              (fun _ _ => _ * dt.toBimachine.stepWeight _ () _ * _) from rfl]
    rw [ih]; rfl

/-- The constructed `Bimachine` has an equivalent `transduceLeft`. -/
@[simp]
theorem toBimachine_transduceLeft
    (dt : DetTransducer State Symbol Weight) (acc : Weight) (xs : List Symbol) :
    transduceFromLeft dt.toBimachine acc xs = transduceFromLeft dt acc xs := by
  simp only [transduceFromLeft]
  rw [show (fun sr => _ * dt.toBimachine.startWeight sr) =
            (fun _ => _ * dt.toBimachine.startWeight ()) from rfl]
  simp; rfl

/-- The constructed `Bimachine` has an equivalent `transduceRight`. -/
@[simp]
theorem toBimachine_transduceRight
    (dt : DetTransducer State Symbol Weight) (xs : List Symbol) (acc : Weight) :
    transduceFromRight dt.toBimachine xs acc = transduceFromRight dt xs acc := by
  simp only [transduceFromRight]
  rw [show (fun sr _ => dt.toBimachine.startWeight sr * _) =
            (fun _ _ => dt.toBimachine.startWeight () * _) from rfl]
  simp; rfl

end Semigroup

end Cslib.Automata.DT.DetTransducer
