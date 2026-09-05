/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Automata.NA.Basic
public import Cslib.Computability.Automata.Acceptors.Acceptor
public import Mathlib.Data.List.Chain
public import Mathlib.Data.Sign.Basic
public import Cslib.Foundations.Data.List.IsChainFromTo

/-! # Nondeterministic Two-Way Automaton
-/

@[expose] public section

namespace Cslib.Automata

variable {State Symbol : Type*}

/-- The word to be accepted is put in the state component `input`. This is necessary
because the `Acceptor` framework refers only to the automaton and nothing else.  So
you can't make the word to be accepted a parameter of the automaton. -/
@[ext]
structure TwoWayState (State Symbol : Type*) where
  state : State
  input : List Symbol
  inpPos : ℕ

/-- Another alternative is to use `Unit` for this type.  But I thik exposing the contents of
the state transitions can potentially faciliate proofs because an execution in the sense
of `LTS.Execution` would then include all nondeterministic choices made by an execution. -/
@[ext]
structure TwoWaySymbol (Symbol : Type*) where
  symbol : Symbol
  dir : SignType

abbrev TwoWayLTS (State Symbol : Type*) :=
  LTS (TwoWayState State Symbol) (TwoWaySymbol Symbol)

structure TwoWayNA (State Symbol : Type*) where
  LTS : TwoWayLTS State Symbol
  start : Set (TwoWayState State Symbol)
  accept : Set (TwoWayState State Symbol)
  /-- We require that the state component `input` never changes. -/
  input_inv : ∀ s x t, LTS.Tr s x t → t.input = s.input

namespace TwoWayNA

/-- The word to be accepted is put in the state component `input` at the beginning.
The read pointer `inpPos` is at 0 at the beginning and just beyond `input` at the end.
You can choose to change that requirement. -/
instance : Acceptor (TwoWayNA State Symbol) Symbol where
  Accepts (a : TwoWayNA State Symbol) (xs : List Symbol) : Prop :=
    ∃ s, s ∈ a.start ∧ s.input = xs ∧ s.inpPos = 0 ∧
      ∃ ys t, a.LTS.MTr s ys t ∧ t ∈ a.accept ∧ t.inpPos = s.input.length

end TwoWayNA

def TwoWayTr (State Symbol : Type*) := State → Symbol → SignType → State → Prop

def twoWayLTS.mk (tr : TwoWayTr State Symbol) : TwoWayLTS State Symbol where
  Tr s' x' t' := ∃ _ : s'.inpPos < s'.input.length,
    s'.input[s'.inpPos] = x'.symbol ∧ t'.input = s'.input ∧
    tr s'.state x'.symbol x'.dir t'.state ∧
    match x'.dir with
    | SignType.zero => t'.inpPos = s'.inpPos
    | SignType.pos => t'.inpPos = s'.inpPos.succ
    | SignType.neg => t'.inpPos = s'.inpPos.pred

def twoWayNA.mk (tr : TwoWayTr State Symbol) (start accept : Set State)
    : TwoWayNA State Symbol where
  LTS := twoWayLTS.mk tr
  start := (fun s' ↦ s'.state) ⁻¹' start
  accept := (fun s' ↦ s'.state) ⁻¹' accept
  input_inv s' x' t' := by grind [twoWayLTS.mk]

end Cslib.Automata
