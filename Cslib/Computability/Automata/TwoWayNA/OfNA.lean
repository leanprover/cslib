/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Automata.TwoWayNA.Basic

/-! # Finite acceptors as two-way automata

A nondeterministic finite acceptor (`NA.FinAcc`) is the special case of a nondeterministic two-way
automaton (`TwoWayNA`) that moves its head one symbol to the right in every step,
`NA.FinAcc.toTwoWayNA`.

The head of `a.toTwoWayNA` is thus at position `i` exactly when `a` has read the first `i`
symbols of the input, so the runs of the two-way automaton are in lockstep with the multistep
transitions of `a` (`TwoWayNA.mTr_take_of_mTr_toCfgNA`, `TwoWayNA.mTr_toCfgNA_of_mTr`) and the two
accept the same words (`TwoWayNA.accepts_toTwoWayNA_iff`, `TwoWayNA.language_toTwoWayNA`).
-/

@[expose] public section

namespace Cslib.Automata

variable {State Symbol : Type*} {input : List Symbol}

/-- The two-way automaton that performs the transitions of the nondeterministic finite acceptor
`n`, always moving its head one symbol to the right. -/
def NA.FinAcc.toTwoWayNA (n : NA.FinAcc State Symbol) : TwoWayNA State Symbol where
  Tr q x m q' := m = SignType.pos ∧ n.Tr q x q'
  start := n.start
  accept := n.accept

namespace TwoWayNA

variable {a : NA.FinAcc State Symbol}

/-- A run of `a.toTwoWayNA` that starts in an initial configuration reads a multistep transition
of `a` over the prefix of `input` that its head has scanned. -/
theorem mTr_take_of_mTr_toCfgNA {c c' : TwoWayNACfg State Symbol}
    {μs : List (Symbol × SignType)}
    (hstart : c ∈ (a.toTwoWayNA.toCfgNA input).start)
    (hrun : (a.toTwoWayNA.toCfgNA input).MTr c μs c') :
    a.MTr c.state (input.take c'.pos) c'.state := by
  obtain ⟨-, hpos, rfl⟩ := hstart
  refine (LTS.mtrInv_of_trInv
    (p := fun d => d.input = c.input ∧ a.MTr c.state (c.input.take d.pos) d.state) ?_ c μs c' hrun
    ⟨rfl, by simp [hpos]⟩).2
  rintro d ⟨x, m⟩ d' hstep ⟨hd, hmtr⟩
  obtain ⟨hlt, rfl⟩ := getElem_of_tr (input := c.input) hstep hd
  obtain ⟨hinput, -, ⟨rfl, htr⟩, hpos⟩ := hstep
  have hpos' : (d'.pos : ℕ) = (d.pos : ℕ) + 1 := by simp at hpos; omega
  refine ⟨hinput ▸ hd, ?_⟩
  rw [hpos', List.take_succ_eq_append_getElem hlt]
  exact LTS.MTr.stepR _ hmtr htr

/-- A multistep transition of `a` over a prefix of `input` is read by the run of `a.toTwoWayNA`
that takes its head from the beginning of the input to the end of that prefix, moving one symbol
to the right in every step. -/
theorem mTr_toCfgNA_of_mTr {s s' : State} {pre : List Symbol} (hpre : pre <+: input)
    (hmtr : a.MTr s pre s') :
    (a.toTwoWayNA.toCfgNA input).MTr ⟨input, s, 0⟩ (pre.map (·, SignType.pos))
      ⟨input, s', ⟨pre.length, by grind⟩⟩ := by
  induction pre using List.reverseRecOn generalizing s' with
  | nil => simp_all
  | append_singleton pre x ih =>
    rw [LTS.MTr.append_iff] at hmtr
    obtain ⟨t, hmtr, htr⟩ := hmtr
    rw [LTS.MTr.singleton_iff] at htr
    have hlt : pre.length < input.length := by grind
    have hx : input[pre.length] = x := by
      rw [← hpre.getElem (by simp)]
      simp
    have hstep : (a.toTwoWayNA.toCfgNA input).Tr
        ⟨input, t, ⟨pre.length, by omega⟩⟩ (x, SignType.pos)
        ⟨input, s', ⟨(pre ++ [x]).length, by simpa using hlt⟩⟩ :=
      ⟨rfl, by simp [← hx], ⟨rfl, htr⟩, by simp⟩
    rw [List.map_append]
    exact LTS.MTr.stepR _ (ih ((List.prefix_append _ _).trans hpre) hmtr) hstep

open Acceptor

/-- A nondeterministic finite acceptor and its two-way rendering accept the same words. -/
theorem accepts_toTwoWayNA_iff (a : NA.FinAcc State Symbol) (input : List Symbol) :
    Accepts a.toTwoWayNA input ↔ Accepts a input := by
  constructor
  · rintro ⟨μs, c, ⟨hs, hpos, hinput⟩, c', ⟨hacc, hlast⟩, hmtr⟩
    subst hinput
    have hinput' := LTS.mtrInv_of_trInv (toCfgNA_input_eq _ _) c μs c' hmtr rfl
    have hmtr := mTr_take_of_mTr_toCfgNA ⟨hs, hpos, rfl⟩ hmtr
    rw [hlast, Fin.val_last, hinput', List.take_length] at hmtr
    exact ⟨c.state, hs, c'.state, hacc, hmtr⟩
  · rintro ⟨s, hs, s', hs', hmtr⟩
    exact ⟨_, ⟨input, s, 0⟩, ⟨hs, rfl, rfl⟩, ⟨input, s', Fin.last _⟩, ⟨hs', rfl⟩,
      mTr_toCfgNA_of_mTr (List.prefix_refl _) hmtr⟩

/-- A nondeterministic finite acceptor and its two-way rendering recognise the same language. -/
theorem language_toTwoWayNA (a : NA.FinAcc State Symbol) : language a.toTwoWayNA = language a := by
  ext xs
  simpa [Acceptor.mem_language] using accepts_toTwoWayNA_iff a xs

end TwoWayNA

end Cslib.Automata
