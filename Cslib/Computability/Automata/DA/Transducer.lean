/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Automata.DA.Basic
public import Cslib.Computability.Automata.Transducers.Transducer
import Mathlib.Basic.Finite.Prod
import Mathlib.Data.Fintype.Order

/-!
# Sequential and subsequential transducers.

A sequential transducer is a deterministic automaton that emits a word per transition.
A subsequential transducer can also output a final word at the end of the input. The output on a
complete input word is the concatenation of the output words along the run of the automaton,
followed by the final output of the last state. A transducer translates an input word into
exactly this output.

The transducers here are total. Every state has a transition for each input symbol, and every
state of a subsequential transducer has a final output. The state type may be infinite.

## Main definitions

* `Cslib.Automata.SequentialTransducer` extends a deterministic automaton with a word emitted on
  each transition. `Cslib.Automata.SubsequentialTransducer` adds a final output word per state.
* `Cslib.Automata.SequentialTransducer.toSubsequential` equips a sequential transducer with
  empty final output.
* `Cslib.Automata.SequentialTransducer.evalFrom` and
  `Cslib.Automata.SubsequentialTransducer.evalFrom` compute the output from a given state.
* `Cslib.Automata.SequentialTransducer.eval` and `Cslib.Automata.SubsequentialTransducer.eval`
  compute the output on a complete input word from the start state. They define the translation
  relation of each kind of transducer.
* `Cslib.Automata.SubsequentialTransducer.OutputBoundedBy` bounds the length of each word
  emitted on a transition or at end of input.

## Main results

* `Cslib.Automata.SubsequentialTransducer.exists_outputBoundedBy_of_finite` bounds the output
  words of a transducer with finitely many states and input symbols.
* `Cslib.Automata.SequentialTransducer.evalFrom_unique` and
  `Cslib.Automata.SubsequentialTransducer.evalFrom_unique` characterize the output by its
  defining equations.

## References

* [S. Mihov and K. U. Schulz, *Finite-State Techniques*, Chapter 5][MihovSchulz2019]
-/

@[expose] public section

namespace Cslib.Automata

/-- A deterministic automaton that emits a word on each transition. -/
structure SequentialTransducer (State InSymbol OutSymbol : Type*) extends DA State InSymbol where
  /-- The output word emitted by a transition. -/
  emit (s : State) (c : InSymbol) : List OutSymbol

/-- A sequential transducer that emits a final word at the end of the input. -/
structure SubsequentialTransducer (State InSymbol OutSymbol : Type*)
    extends SequentialTransducer State InSymbol OutSymbol where
  /-- The output word at end of input. -/
  finalOut (s : State) : List OutSymbol

namespace SequentialTransducer

variable {State InSymbol OutSymbol : Type*}

/-- Regard a sequential transducer as subsequential by emitting nothing at end of input. -/
@[simps finalOut toSequentialTransducer]
def toSubsequential (transducer : SequentialTransducer State InSymbol OutSymbol) :
    SubsequentialTransducer State InSymbol OutSymbol :=
  { toSequentialTransducer := transducer, finalOut := fun _ => [] }

end SequentialTransducer

namespace SubsequentialTransducer

variable {State InSymbol OutSymbol : Type*}
variable (transducer : SubsequentialTransducer State InSymbol OutSymbol)

/-- Every transition output and every final output has length at most `m`. The input `none`
stands for the end of the input, where the final output is emitted. -/
def OutputBoundedBy (m : ℕ) : Prop :=
  ∀ q (a : Option InSymbol), (a.elim (transducer.finalOut q) (transducer.emit q)).length ≤ m

/-- A transducer with finitely many states and input symbols has a uniform bound on the length
of its transition and final outputs. -/
theorem exists_outputBoundedBy_of_finite [Finite State] [Finite InSymbol] :
    ∃ m, transducer.OutputBoundedBy m := by
  obtain ⟨m, hm⟩ := Finite.exists_le fun p : State × Option InSymbol =>
    (p.2.elim (transducer.finalOut p.1) (transducer.emit p.1)).length
  exact ⟨m, fun q a => hm (q, a)⟩

/-- The output of `transducer` on an input word when starting from state `q`. -/
@[simp]
def evalFrom (transducer : SubsequentialTransducer State InSymbol OutSymbol) (q : State) :
    List InSymbol → List OutSymbol
  | [] => transducer.finalOut q
  | a :: w => transducer.emit q a ++ transducer.evalFrom (transducer.tr q a) w

/-- The defining equations of `evalFrom` uniquely determine it. -/
theorem evalFrom_unique {spec : State → List InSymbol → List OutSymbol}
    (hfinal : ∀ q, spec q [] = transducer.finalOut q)
    (hstep : ∀ q a w, spec q (a :: w) = transducer.emit q a ++ spec (transducer.tr q a) w) :
    transducer.evalFrom = spec := by
  funext q w
  induction w generalizing q with
  | nil => exact (hfinal q).symm
  | cons a w ih => rw [evalFrom, ih, hstep]

/-- The output on a complete input word. -/
abbrev eval (transducer : SubsequentialTransducer State InSymbol OutSymbol) :=
  transducer.evalFrom transducer.start

/-- A subsequential transducer translates each input word into its output. This instance is an
example of the general `Transducer` interface; downstream code should use `eval` directly. -/
instance {InSymbol OutSymbol : Type v} :
    Transducer (SubsequentialTransducer State InSymbol OutSymbol) InSymbol OutSymbol where
  Translates transducer w out := transducer.eval w = out

end SubsequentialTransducer

namespace SequentialTransducer

variable {State InSymbol OutSymbol : Type*}
variable (transducer : SequentialTransducer State InSymbol OutSymbol)

/-- The concatenated transition outputs of `transducer` on an input word when starting from
state `q`. -/
abbrev evalFrom (transducer : SequentialTransducer State InSymbol OutSymbol) :=
  transducer.toSubsequential.evalFrom

/-- The defining equations of `evalFrom` uniquely determine it. -/
theorem evalFrom_unique {spec : State → List InSymbol → List OutSymbol}
    (hnil : ∀ q, spec q [] = [])
    (hstep : ∀ q a w, spec q (a :: w) = transducer.emit q a ++ spec (transducer.tr q a) w) :
    transducer.evalFrom = spec :=
  transducer.toSubsequential.evalFrom_unique hnil hstep

/-- The concatenated transition outputs from the start state. -/
abbrev eval (transducer : SequentialTransducer State InSymbol OutSymbol) :=
  transducer.evalFrom transducer.start

/-- A sequential transducer translates each input word into its output. This instance is an
example of the general `Transducer` interface; downstream code should use `eval` directly. -/
instance {InSymbol OutSymbol : Type v} :
    Transducer (SequentialTransducer State InSymbol OutSymbol) InSymbol OutSymbol where
  Translates transducer w out := transducer.eval w = out

end SequentialTransducer

end Cslib.Automata
