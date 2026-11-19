/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Automata.Transducers.Transducer
public import Cslib.Foundations.Semantics.LTS.Basic

/-!
# Subsequential transducers

A subsequential transducer reads one input symbol per transition and emits a word. In
`Cslib.Automata.SubsequentialTransducer.toLTS`, each edge is labelled by that input symbol and
output word. A path from the start state translates the sequence of input symbols into the
concatenated output words followed by the final output of the last state. In particular, the
empty path emits the final output of the start state.

## Main result

* `Cslib.Automata.SubsequentialTransducer.translates_iff_output_eq` identifies translation
  along labelled paths with the output computed by recursion on the input word.
-/

@[expose] public section

namespace Cslib.Automata

/-- A deterministic transducer that emits a word per input symbol and a final word at end of
input. With finite state and alphabet types it is a subsequential finite-state transducer. -/
structure SubsequentialTransducer (State InSymbol OutSymbol : Type*) where
  /-- The initial state. -/
  start : State
  /-- The output chunk and successor state for an input symbol. -/
  step : State → InSymbol → List OutSymbol × State
  /-- The output chunk at end of input. -/
  final : State → List OutSymbol

namespace SubsequentialTransducer

variable {State InSymbol OutSymbol : Type*}

variable (t : SubsequentialTransducer State InSymbol OutSymbol)

/-- The output on the remaining input, starting in state `q`. -/
def outputFrom : State → List InSymbol → List OutSymbol
  | q, [] => t.final q
  | q, a :: w => (t.step q a).1 ++ outputFrom (t.step q a).2 w

@[simp]
theorem outputFrom_nil (q : State) : t.outputFrom q [] = t.final q := rfl

@[simp]
theorem outputFrom_cons (q : State) (a : InSymbol) (w : List InSymbol) :
    t.outputFrom q (a :: w) = (t.step q a).1 ++ t.outputFrom (t.step q a).2 w := rfl

/-- To identify the output from every state, it suffices to verify the final output
and the effect of consuming one symbol. -/
theorem outputFrom_eq_of_spec {spec : State → List InSymbol → List OutSymbol}
    (hfinal : ∀ q, t.final q = spec q [])
    (hstep : ∀ q a w, (t.step q a).1 ++ spec (t.step q a).2 w = spec q (a :: w))
    (q : State) (w : List InSymbol) : t.outputFrom q w = spec q w := by
  induction w generalizing q with
  | nil => exact hfinal q
  | cons a w ih => rw [outputFrom_cons, ih, hstep]

/-- The output on a complete input word. -/
abbrev output := t.outputFrom t.start

/-- Label each transition with the consumed symbol and the emitted word. -/
def toLTS : LTS State (InSymbol × List OutSymbol) where
  Tr q label q' := t.step q label.1 = (label.2, q')

@[simp]
theorem toLTS_tr (q : State) (label : InSymbol × List OutSymbol) (q' : State) :
    t.toLTS.Tr q label q' ↔ t.step q label.1 = (label.2, q') := Iff.rfl

/-- The output along an LTS path, including the final output, agrees with evaluation. -/
theorem outputFrom_eq_of_mTr {q q' : State} {labels : List (InSymbol × List OutSymbol)}
    (h : t.toLTS.MTr q labels q') :
    t.outputFrom q (labels.map Prod.fst) = labels.flatMap Prod.snd ++ t.final q' := by
  induction h with
  | refl => rfl
  | stepL hstep _ ih =>
    simp only [toLTS_tr] at hstep
    simp [hstep, ih, List.append_assoc]

/-- Every input word determines a path from any state. -/
theorem exists_mTr (q : State) (w : List InSymbol) :
    ∃ labels q', t.toLTS.MTr q labels q' ∧ labels.map Prod.fst = w := by
  induction w generalizing q with
  | nil => exact ⟨[], q, .refl, rfl⟩
  | cons a w ih =>
    obtain ⟨labels, q', h, rfl⟩ := ih (t.step q a).2
    exact ⟨(a, (t.step q a).1) :: labels, q', .stepL rfl h, rfl⟩

instance {Input Output : Type v} :
    Transducer (SubsequentialTransducer State Input Output) Input Output where
  Translates t w out :=
    ∃ labels q, t.toLTS.MTr t.start labels q ∧ labels.map Prod.fst = w ∧
      labels.flatMap Prod.snd ++ t.final q = out

/-- Translation by the labelled transition system is the graph of the output function. -/
@[simp]
theorem translates_iff_output_eq {Input Output : Type v}
    (t : SubsequentialTransducer State Input Output) (w : List Input) (out : List Output) :
    Transducer.Translates t w out ↔ t.output w = out := by
  constructor
  · rintro ⟨labels, q, h, rfl, rfl⟩
    exact t.outputFrom_eq_of_mTr h
  · intro h
    obtain ⟨labels, q, hpath, rfl⟩ := t.exists_mTr t.start w
    exact ⟨labels, q, hpath, rfl, (t.outputFrom_eq_of_mTr hpath).symm.trans h⟩

end SubsequentialTransducer

end Cslib.Automata
