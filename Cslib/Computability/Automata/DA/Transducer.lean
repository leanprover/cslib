/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Automata.DA.Basic
public import Cslib.Computability.Automata.Transducers.Transducer

/-!
# Sequential and subsequential transducers

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
* `Cslib.Automata.SequentialTransducer.outputFrom` and
  `Cslib.Automata.SubsequentialTransducer.outputFrom` compute the output from a given state.
* `Cslib.Automata.SequentialTransducer.output` and `Cslib.Automata.SubsequentialTransducer.output`
  compute the output on a complete input word from the start state. They define the translation
  relation of each kind of transducer.
* `Cslib.Automata.SubsequentialTransducer.OutputBoundedBy` bounds the length of each word
  emitted on a transition or at end of input.

## Main results

* `Cslib.Automata.SequentialTransducer.outputFrom_unique` and
  `Cslib.Automata.SubsequentialTransducer.outputFrom_unique` characterize the output by its
  defining equations.
* `Cslib.Automata.SubsequentialTransducer.outputFrom_eq_append` splits the output of a
  subsequential transducer into the transition outputs and the final output of the state reached.

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

/-- Every transition output and every final output has length at most `m`. -/
def OutputBoundedBy (m : ℕ) : Prop :=
  ∀ q (a : Option InSymbol), (a.elim (transducer.finalOut q) (transducer.emit q)).length ≤ m

/-- The output of `transducer` on an input word when starting from state `q`. -/
@[simp]
def outputFrom (transducer : SubsequentialTransducer State InSymbol OutSymbol) (q : State) :
    List InSymbol → List OutSymbol
  | [] => transducer.finalOut q
  | a :: w => transducer.emit q a ++ transducer.outputFrom (transducer.tr q a) w

/-- The defining equations of `outputFrom` uniquely determine it. -/
theorem outputFrom_unique {spec : State → List InSymbol → List OutSymbol}
    (hfinal : ∀ q, transducer.finalOut q = spec q [])
    (hstep : ∀ q a w, transducer.emit q a ++ spec (transducer.tr q a) w = spec q (a :: w)) :
    transducer.outputFrom = spec := by
  funext q w
  induction w generalizing q with
  | nil => exact hfinal q
  | cons a w ih => rw [outputFrom, ih, hstep]

/-- The output on a complete input word. -/
abbrev output (transducer : SubsequentialTransducer State InSymbol OutSymbol) :=
  transducer.outputFrom transducer.start

/-- A subsequential transducer translates each input word into its output. -/
instance {Input Output : Type v} :
    Transducer (SubsequentialTransducer State Input Output) Input Output where
  Translates transducer w out := transducer.output w = out

variable {Input Output : Type v} (transducer : SubsequentialTransducer State Input Output)

/-- Translation is the graph of the output function. -/
@[simp]
theorem translates_iff_output_eq (w : List Input) (out : List Output) :
    Transducer.Translates transducer w out ↔ transducer.output w = out := Iff.rfl

end SubsequentialTransducer

namespace SequentialTransducer

variable {State InSymbol OutSymbol : Type*}
variable (transducer : SequentialTransducer State InSymbol OutSymbol)

/-- The concatenated transition outputs of `transducer` on an input word when starting from
state `q`. -/
abbrev outputFrom (transducer : SequentialTransducer State InSymbol OutSymbol) :=
  transducer.toSubsequential.outputFrom

@[simp]
theorem outputFrom_nil (q : State) : transducer.outputFrom q [] = [] := rfl

@[simp]
theorem outputFrom_cons (q : State) (a : InSymbol) (w : List InSymbol) :
    transducer.outputFrom q (a :: w) =
      transducer.emit q a ++ transducer.outputFrom (transducer.tr q a) w := rfl

/-- The defining equations of `outputFrom` uniquely determine it. -/
theorem outputFrom_unique {spec : State → List InSymbol → List OutSymbol}
    (hnil : ∀ q, [] = spec q [])
    (hstep : ∀ q a w, transducer.emit q a ++ spec (transducer.tr q a) w = spec q (a :: w)) :
    transducer.outputFrom = spec :=
  transducer.toSubsequential.outputFrom_unique hnil hstep

/-- The concatenated transition outputs from the start state. -/
abbrev output (transducer : SequentialTransducer State InSymbol OutSymbol) :=
  transducer.outputFrom transducer.start

/-- A sequential transducer translates each input word into its output. -/
instance {Input Output : Type v} :
    Transducer (SequentialTransducer State Input Output) Input Output where
  Translates transducer w out := transducer.output w = out

variable {Input Output : Type v} (transducer : SequentialTransducer State Input Output)

/-- Translation is the graph of the output function. -/
@[simp]
theorem translates_iff_output_eq (w : List Input) (out : List Output) :
    Transducer.Translates transducer w out ↔ transducer.output w = out := Iff.rfl

end SequentialTransducer

namespace SubsequentialTransducer

variable {State InSymbol OutSymbol : Type*}
variable (transducer : SubsequentialTransducer State InSymbol OutSymbol)

/-- The output splits into the transition outputs and the final output of the state reached. -/
theorem outputFrom_eq_append (q : State) (w : List InSymbol) :
    transducer.outputFrom q w =
      transducer.toSequentialTransducer.outputFrom q w ++
        transducer.finalOut (transducer.mtr q w) := by
  induction w generalizing q with
  | nil => rfl
  | cons a w ih => simp [ih (transducer.tr q a), FLTS.mtr]

end SubsequentialTransducer

end Cslib.Automata
