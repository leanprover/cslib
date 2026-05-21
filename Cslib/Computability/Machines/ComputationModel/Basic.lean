/-
Copyright (c) 2026 Maximilian Keßler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maximilian Keßler
-/

module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Logic.Function.Iterate
public import Cslib.Foundations.Data.RelatesInSteps

/-! # Transition Based Computation Models

Defines typeclasses and definitions for computation systems based on a transition function
`step : cfg → Option cfg`, where `cfg` is the type of configurations of such a system.
Additionally, we bundle this with input/output functions from/to words over an alphabet
to obtain a model of computation between lists of symbols that has a notion of execution time
(given by the needed number of applications of the `step` function).

The main example of such a transition machine are turing machines:
Typical turing models work by inputting a word (over a fixed alphabet)
on a specific tape, then iterating a step function until an accepting state is reached,
and the output is defined as a word (potentially over a different alphabet than the input),
typically read from a specific tape.
For all such turing machines (independent of the exact design choices), we can define instances
to `TransitionMachine` and thereby use the same definitions of computation and time for all
models, and in particular state equivalences of such computation models.

## Design

- Termination of such a machine is modeled by the step function yielding `none`
- We expose the alphabet types in the definition of `TransitionMachine`.
- The output function is *partial* in the sense that it can return `none`. In this case,
  there is no output of a computation (this can occur even if the computation terminates).

## Important declarations
- `TransitionSystem τ`: Terms `(t : τ)` have an associated *configuration type* `cfg t`
- `TransitionMachine τ Γᵢ Γₒ`: In addition to this being a `TransitionSystem τ`, there is
  - an input function `init : List Γᵢ → cfg t`
  - an output function `output : cfg t → Option (List Γₒ)`
- `OutputsInTime t n l l'`: States that `t` outputs `l'` from `l` in at most `n` steps.
- `ComputesInPolyTime t f`: The machine `t` computes the function `f : List Γᵢ → List Γₒ` in
  polynomial time.

## TODO:
It might be useful to work with `ℕ∞` instead of `ℕ` for predicates such as `EvalsToInTime`.
This would allow us to recover the regular notion of `EvalsTo` (without time constraints)
as the special case of the time bound `ω`.
We could then introduce abbreviations for `EvalsTo` or `Outputs` that insert `ω`.

-/

@[expose] public section

namespace Computation

/--
For each element `(t : τ)`, there is a bundle of a type `cfg t` with a step / transition function
`cfg t → Option (cfg t)`.
-/
class TransitionSystem (τ : Type u) where
  cfg (t : τ) : Type*
  red {t : τ} : cfg t → cfg t → Prop

class SpaceSize (τ : Type u) [TransitionSystem τ] where
  space_used {t : τ} : TransitionSystem.cfg t → ℕ

/--
Bundles a `TransitionSystem` with input and output functions from/to words over an alphabet.
This way, we can think of elements of `τ` as allowing computations `List Γᵢ → List Γₒ`
by lifting inputs into the computation context, iterating the `step` function,
and taking output from this computation context.
-/
class TransitionMachine (τ : Type u) (Γᵢ Γₒ : outParam (Type v)) extends TransitionSystem τ where
  init {t : τ} : List Γᵢ → cfg t
  -- TODO: Potentially work with a partial function here instead of `Option`?
  output {t : τ} : cfg t → Option (List Γₒ)

namespace TransitionSystem



variable {τ : Type u} [TransitionSystem τ]

def EvalsTo (t : τ) (a b : cfg t) := Relation.ReflTransGen red a b

/--
The machine `t` reaches `b` from `a` in at most `n` steps.
-/
def EvalsToInTime (t : τ) (a b : cfg t) (n : ℕ) := Relation.RelatesWithinSteps red a b n

variable {t : τ} {a b c : cfg t} {n n₁ n₂ : ℕ}

-- TODO: Potentially get rid of these definitions and work with `RelatesWithinSteps` directly
-- in proof contexts?

lemma EvalsTo.refl : EvalsTo t a a := Relation.ReflTransGen.refl

lemma EvalsTo.trans (h₁ : EvalsTo t a b) (h₂ : EvalsTo t b c) : EvalsTo t a c :=
  Relation.ReflTransGen.trans h₁ h₂

lemma EvalsToInTime.refl : EvalsToInTime t a a 0 := Relation.RelatesWithinSteps.refl a

lemma EvalsToInTime.trans (h₁ : EvalsToInTime t a b n₁) (h₂ : EvalsToInTime t b c n₂) :
    EvalsToInTime t a c (n₁ + n₂) := Relation.RelatesWithinSteps.trans h₁ h₂

def EvalsToInTime.of_le (h : EvalsToInTime t a b n₁) (hn : n₁ ≤ n₂) :
    EvalsToInTime t a b n₂ :=
  Relation.RelatesWithinSteps.of_le h hn


end TransitionSystem

namespace TransitionMachine
open TransitionSystem

variable {τ : Type*} {Γᵢ Γₒ : Type} [TransitionMachine τ Γᵢ Γₒ]

/--
The transition machine `t` outputs `l'` on input `l`.
-/
structure Outputs (t : τ) (l : List Γᵢ) (l' : List Γₒ) where
  haltState : cfg t
  haltState_halts : ¬ ∃ s, red haltState s
  evalsTo : TransitionSystem.EvalsTo t (init l) haltState
  output_eq : output haltState =  some l'

/--
The transition machine `t` outputs `l'` on input `l` in at most `n` steps.
-/
structure OutputsInTime (t : τ) (n : ℕ) (l : List Γᵢ) (l' : List Γₒ) where
  haltState : (cfg t)
  haltState_halts : ¬ ∃ s, red haltState s
  evals_to : TransitionSystem.EvalsToInTime t (init l) haltState n
  output_eq : output haltState = some l'

/--
Time bounds of `OutputsInTime` can be increased.
-/
def OutputsInTime.of_le {t : τ} {n m : ℕ} {l : List Γᵢ} {l' : List Γₒ} (hnm : n ≤ m)
    (hv : OutputsInTime t n l l') : OutputsInTime t m l l' where
  haltState := hv.haltState
  haltState_halts := hv.haltState_halts
  evals_to := TransitionSystem.EvalsToInTime.of_le hv.evals_to hnm
  output_eq := hv.output_eq


-- TODO: This is only true for deterministic machines.
-- Add the corresponding typeclass and then proof this statement
/-
The output of any computation of transition machines is unique.
lemma OutputsInTime.output_unique {t : τ} {n₁ n₂ : ℕ} {l : List Γᵢ} {l'₁ l'₂ : List Γₒ}
    (ho₁ : OutputsInTime t n₁ l l'₁) (ho₂ : OutputsInTime t n₂ l l'₂) :
    l'₁ = l'₂ := by
  obtain ⟨steps₁, hle₁, hr₁⟩ := ho₁.evals_to
  obtain ⟨steps₂, hle₂, hr₂⟩ := ho₂.evals_to
  wlog hle : steps₁ ≤ steps₂
  · grind
  · have : steps₁ = steps₂ := by
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le' hle
      cases d with
      | zero => symm; simpa using hd
      | succ d' =>
          have := ho₂.evals_to.evals
          rw [hd, Function.iterate_add_apply, ho₁.evals_to.evals,
            Function.iterate_succ_apply, Option.bind_eq_bind, flip, Option.bind_some,
            ho₁.haltState_halts, Function.iterate_fixed rfl] at this
          contradiction
    have : ho₁.haltState = ho₂.haltState := by
      apply Option.some.inj
      rw [← ho₁.evals_to.evals, ← ho₂.evals_to.evals, this]
    rw [← Option.some_inj, ← ho₁.output_eq, ← ho₂.output_eq, this]
-/

variable (τ) in
/--
"Proof" that `f` is computable by the system `τ`.
A witness machine is bundled as part of this structure,
as well as a function bounding execution time.
-/
structure TimeComputable (f : List Γᵢ → List Γₒ) where
  t : τ
  time_bound : ℕ → ℕ
  outputsFun : ∀ w, OutputsInTime t (time_bound w.length) w (f w)

variable (τ) in
/--
"Proof" that `f` is computable in polynomial time by the system `τ`.
A witness machine and polynomial which bounds runtime are bundled as part of this structure.
-/
structure PolyTimeComputable (f : List Γᵢ → List Γₒ) extends TimeComputable τ f where
  poly : Polynomial ℕ
  bounds : ∀ n, time_bound n ≤ poly.eval n

end TransitionMachine


end Computation
