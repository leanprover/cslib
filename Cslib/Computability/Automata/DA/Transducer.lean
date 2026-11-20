/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Automata.DA.Basic
public import Cslib.Computability.Automata.Transducers.Transducer
public import Cslib.Foundations.Semantics.FLTS.FLTSToLTS

/-!
# Sequential and subsequential transducers

A sequential transducer is a deterministic automaton that emits a word per transition.
A subsequential transducer can also output a final word at the end of the input. The output on a
complete input word is the concatenation of the output words along the path through the automaton,
followed by the final output of the last state.

## Main definitions

* `Cslib.Automata.SequentialTransducer` extends a deterministic automaton with a word emitted on
  each transition. `Cslib.Automata.SubsequentialTransducer` adds a final output word per state.
* `Cslib.Automata.SequentialTransducer.toIOLTS` labels each edge with the input symbol it reads
  and the output word it emits.
* `Cslib.Automata.SequentialTransducer.toSubsequential` equips a sequential transducer with
  empty final output.

## Main results

* `Cslib.Automata.SequentialTransducer.mtr_eq_of_mTr` identifies the endpoint of a labelled
  path with the state reached by reading its input in the underlying automaton.
* `Cslib.Automata.SequentialTransducer.translates_iff_output_eq` and
  `Cslib.Automata.SubsequentialTransducer.translates_iff_output_eq` characterize translation
  along labelled paths by equality with the recursively computed output.
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

variable (transducer : SequentialTransducer State InSymbol OutSymbol)

/-- Label each transition with the consumed symbol and the emitted word.
The underlying automaton labels transitions by input alone in `transducer.toFLTS.toLTS`. -/
def toIOLTS (transducer : SequentialTransducer State InSymbol OutSymbol) :
    LTS State (InSymbol × List OutSymbol) where
  Tr q label q' := transducer.emit q label.1 = label.2 ∧ transducer.tr q label.1 = q'

@[simp]
theorem toIOLTS_tr (q : State) (label : InSymbol × List OutSymbol) (q' : State) :
    transducer.toIOLTS.Tr q label q' ↔
      transducer.emit q label.1 = label.2 ∧ transducer.tr q label.1 = q' := Iff.rfl

instance {Input Output : Type v} :
    Transducer (SequentialTransducer State Input Output) Input Output where
  Translates transducer w out :=
    ∃ labels q, transducer.toIOLTS.MTr transducer.start labels q ∧ labels.map Prod.fst = w ∧
      labels.flatMap Prod.snd = out

/-- Reading the input labels of a transducer path in the underlying automaton reaches the
same state. -/
theorem mtr_eq_of_mTr {q q' : State} {labels : List (InSymbol × List OutSymbol)}
    (h : transducer.toIOLTS.MTr q labels q') : transducer.mtr q (labels.map Prod.fst) = q' := by
  induction h with
  | refl => rfl
  | stepL edge _ ih =>
    obtain ⟨_, hnext⟩ := edge
    change transducer.mtr (transducer.tr _ _) _ = _
    rwa [hnext]

/-- Every input word determines a path from any state. -/
theorem exists_mTr (q : State) (w : List InSymbol) :
    ∃ labels q', transducer.toIOLTS.MTr q labels q' ∧ labels.map Prod.fst = w := by
  induction w generalizing q with
  | nil => exact ⟨[], q, .refl, rfl⟩
  | cons a w ih =>
    obtain ⟨labels, q', h, rfl⟩ := ih (transducer.tr q a)
    exact ⟨(a, transducer.emit q a) :: labels, q', .stepL ⟨rfl, rfl⟩ h, rfl⟩

/-- Regard a sequential transducer as subsequential by emitting nothing at end of input. -/
def toSubsequential (transducer : SequentialTransducer State InSymbol OutSymbol) :
    SubsequentialTransducer State InSymbol OutSymbol :=
  { toSequentialTransducer := transducer, finalOut := fun _ => [] }

end SequentialTransducer

namespace SubsequentialTransducer

variable {State InSymbol OutSymbol : Type*}
variable (transducer : SubsequentialTransducer State InSymbol OutSymbol)

instance {Input Output : Type v} :
    Transducer (SubsequentialTransducer State Input Output) Input Output where
  Translates transducer w out :=
    ∃ labels q, transducer.toIOLTS.MTr transducer.start labels q ∧ labels.map Prod.fst = w ∧
      labels.flatMap Prod.snd ++ transducer.finalOut q = out

/-- A recursive specification of the output of `transducer` from a state,
equivalent to the labelled-path definition. -/
def outputFrom (transducer : SubsequentialTransducer State InSymbol OutSymbol) :
    State → List InSymbol → List OutSymbol
  | q, [] => transducer.finalOut q
  | q, a :: w => transducer.emit q a ++ transducer.outputFrom (transducer.tr q a) w

@[simp]
theorem outputFrom_nil (q : State) : transducer.outputFrom q [] = transducer.finalOut q := rfl

@[simp]
theorem outputFrom_cons (q : State) (a : InSymbol) (w : List InSymbol) :
    transducer.outputFrom q (a :: w) =
      transducer.emit q a ++ transducer.outputFrom (transducer.tr q a) w := rfl

/-- To identify the output from every state, it suffices to verify the final output
and the effect of consuming one symbol. -/
theorem outputFrom_eq_of_spec {spec : State → List InSymbol → List OutSymbol}
    (hfinal : ∀ q, transducer.finalOut q = spec q [])
    (hstep : ∀ q a w, transducer.emit q a ++ spec (transducer.tr q a) w = spec q (a :: w))
    (q : State) (w : List InSymbol) : transducer.outputFrom q w = spec q w := by
  induction w generalizing q with
  | nil => exact hfinal q
  | cons a w ih => rw [outputFrom_cons, ih, hstep]

/-- The output on a complete input word. -/
abbrev output (transducer : SubsequentialTransducer State InSymbol OutSymbol) :=
  transducer.outputFrom transducer.start

/-- The output along an LTS path, including the final output, agrees with evaluation. -/
theorem outputFrom_eq_of_mTr {q q' : State} {labels : List (InSymbol × List OutSymbol)}
    (h : transducer.toIOLTS.MTr q labels q') :
    transducer.outputFrom q (labels.map Prod.fst) =
      labels.flatMap Prod.snd ++ transducer.finalOut q' := by
  induction h with
  | refl => rfl
  | stepL hstep _ ih =>
    obtain ⟨hout, hnext⟩ := hstep
    simp [hout, hnext, ih, List.append_assoc]

variable {Input Output : Type v} (transducer : SubsequentialTransducer State Input Output)

/-- Translation by the labelled transition system is the graph of the output function. -/
@[simp]
theorem translates_iff_output_eq (w : List Input) (out : List Output) :
    Transducer.Translates transducer w out ↔ transducer.output w = out := by
  constructor
  · rintro ⟨labels, q, h, rfl, rfl⟩
    exact transducer.outputFrom_eq_of_mTr h
  · intro h
    obtain ⟨labels, q, hpath, rfl⟩ := transducer.exists_mTr transducer.start w
    exact ⟨labels, q, hpath, rfl, (transducer.outputFrom_eq_of_mTr hpath).symm.trans h⟩

end SubsequentialTransducer

namespace SequentialTransducer

variable {State InSymbol OutSymbol : Type*}
variable (transducer : SequentialTransducer State InSymbol OutSymbol)

/-- A recursive specification of the output from `q`, equivalent to the labelled-path definition. -/
abbrev outputFrom (transducer : SequentialTransducer State InSymbol OutSymbol) :=
  transducer.toSubsequential.outputFrom

/-- Identify sequential output by checking the empty word and one transition. -/
theorem outputFrom_eq_of_spec {spec : State → List InSymbol → List OutSymbol}
    (hnil : ∀ q, [] = spec q [])
    (hstep : ∀ q a w, transducer.emit q a ++ spec (transducer.tr q a) w = spec q (a :: w))
    (q : State) (w : List InSymbol) : transducer.outputFrom q w = spec q w :=
  transducer.toSubsequential.outputFrom_eq_of_spec hnil hstep q w

/-- The concatenated transition outputs from the start state. -/
abbrev output (transducer : SequentialTransducer State InSymbol OutSymbol) :=
  transducer.outputFrom transducer.start

variable {Input Output : Type v} (transducer : SequentialTransducer State Input Output)

/-- Adding empty final output preserves translation. -/
theorem toSubsequential_translates_iff (w : List Input) (out : List Output) :
    Transducer.Translates transducer.toSubsequential w out ↔
      Transducer.Translates transducer w out := by
  change (∃ labels q, transducer.toIOLTS.MTr transducer.start labels q ∧ labels.map Prod.fst = w ∧
    labels.flatMap Prod.snd ++ [] = out) ↔ _
  simp only [List.append_nil]
  rfl

/-- Sequential translation is the graph of evaluation with empty final output. -/
@[simp]
theorem translates_iff_output_eq (w : List Input) (out : List Output) :
    Transducer.Translates transducer w out ↔ transducer.output w = out :=
  (toSubsequential_translates_iff transducer w out).symm.trans
    (transducer.toSubsequential.translates_iff_output_eq ..)

end SequentialTransducer

end Cslib.Automata
