/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Automata.TwoWayNA.Basic

/-! # Finite acceptors as two-way automata

A nondeterministic finite acceptor (`NA.FinAcc`) is the special case of a nondeterministic two-way
automaton (`TwoWayNA`) that moves its head one symbol to the right in every step, `TwoWayNA.ofNA`.

The head of `TwoWayNA.ofNA n` is thus at position `i` exactly when `n` has read the first `i`
symbols of the input, so the runs of the two-way automaton are in lockstep with the multistep
transitions of `n` (`TwoWayNA.mTr_take_of_canReach`, `TwoWayNA.canReach_of_mTr`) and the two accept
the same words (`TwoWayNA.accepts_ofNA_iff`, `TwoWayNA.language_ofNA`).
-/

@[expose] public section

namespace Cslib.Automata

variable {State Symbol : Type*} {input : List Symbol}

namespace TwoWayNA

variable {n : NA.FinAcc State Symbol}

/-- The two-way automaton that performs the transitions of the nondeterministic finite acceptor
`n`, always moving its head one symbol to the right. -/
def ofNA (n : NA.FinAcc State Symbol) : TwoWayNA State Symbol where
  Tr q x m q' := m = SignType.pos ∧ n.Tr q x q'
  start := n.start
  accept := n.accept

/-- A run of `ofNA n` starting on `input` reads a multistep transition of `n` over the prefix of
`input` scanned so far. -/
theorem mTr_take_of_canReach {s : State} {c c' : TwoWayNACfg State Symbol}
    (hreach : ((ofNA n).toCfgNA input).CanReach c c') (hc : c.input = input)
    (hmtr : n.MTr s (input.take c.pos) c.state) :
    c'.input = input ∧ n.MTr s (input.take c'.pos) c'.state := by
  obtain ⟨μs, hreach⟩ := hreach
  refine LTS.mtrInv_of_trInv
    (p := fun d => d.input = input ∧ n.MTr s (input.take d.pos) d.state) ?_ c μs c' hreach
    ⟨hc, hmtr⟩
  rintro d ⟨x, m⟩ d' hstep ⟨hd, hmtr⟩
  obtain ⟨hlt, rfl⟩ := getElem_of_tr hstep hd
  obtain ⟨hinput, -, ⟨rfl, htr⟩, hpos⟩ := hstep
  refine ⟨hinput ▸ hd, ?_⟩
  rw [show (d'.pos : ℕ) = (d.pos : ℕ) + 1 by simp at hpos; omega]
  rw [List.take_succ_eq_append_getElem hlt]
  exact LTS.MTr.stepR _ hmtr htr

/-- A multistep transition of `n` over the part of `input` that starts at position `p` is read by a
run of `ofNA n` taking its head from `p` to the end of the input. -/
theorem canReach_of_mTr {suf : List Symbol} {s s' : State} {p : ℕ}
    (hp : p < input.length + 1) (hdrop : input.drop p = suf) (hmtr : n.MTr s suf s') :
    ((ofNA n).toCfgNA input).CanReach ⟨input, s, ⟨p, hp⟩⟩ ⟨input, s', Fin.last _⟩ := by
  induction suf generalizing s p with
  | nil =>
    rw [LTS.MTr.nil_iff] at hmtr
    subst hmtr
    obtain rfl : p = input.length := by grind [List.drop_eq_nil_iff]
    exact LTS.CanReach.refl _ _
  | cons x xs ih =>
    rw [LTS.MTr.cons_iff] at hmtr
    obtain ⟨t, htr, hmtr⟩ := hmtr
    have hlt : p < input.length := by grind [List.drop_eq_nil_iff]
    have hx : input[p]'hlt = x := by
      have h0 : (input.drop p)[0]? = some x := by simp [hdrop]
      grind
    have hdrop' : input.drop (p + 1) = xs := by simp [← List.tail_drop, hdrop]
    have hstep : ((ofNA n).toCfgNA input).Tr
        ⟨input, s, ⟨p, hp⟩⟩ (x, SignType.pos) ⟨input, t, ⟨p + 1, by omega⟩⟩ :=
      ⟨rfl, by simp [← hx], ⟨rfl, htr⟩, by simp⟩
    obtain ⟨μs, hmtr'⟩ := ih (by omega) hdrop' hmtr
    exact ⟨(x, SignType.pos) :: μs, LTS.MTr.cons_iff.mpr ⟨_, hstep, hmtr'⟩⟩

/-- A nondeterministic finite acceptor and its two-way rendering accept the same words. -/
theorem accepts_ofNA_iff (a : NA.FinAcc State Symbol) (input : List Symbol) :
    Acceptor.Accepts (ofNA a) input ↔ Acceptor.Accepts a input := by
  constructor
  · rintro ⟨μs, c, ⟨hs, hpos, hinput⟩, c', ⟨hacc, hlast⟩, hmtr⟩
    have hstart : a.MTr c.state (input.take c.pos) c.state := by simp [hpos]
    obtain ⟨hinput', hmtr⟩ := mTr_take_of_canReach ⟨μs, hmtr⟩ hinput hstart
    rw [hlast, Fin.val_last, hinput', List.take_length] at hmtr
    exact ⟨c.state, hs, c'.state, hacc, hmtr⟩
  · rintro ⟨s, hs, s', hs', hmtr⟩
    obtain ⟨μs, hmtr⟩ :=
      canReach_of_mTr (suf := input) (by omega) List.drop_zero hmtr
    exact ⟨μs, ⟨input, s, ⟨0, by omega⟩⟩, ⟨hs, Fin.ext (by simp), rfl⟩,
      ⟨input, s', Fin.last _⟩, ⟨hs', rfl⟩, hmtr⟩

/-- A nondeterministic finite acceptor and its two-way rendering recognise the same language. -/
theorem language_ofNA (a : NA.FinAcc State Symbol) :
    Acceptor.language (ofNA a) = Acceptor.language a := by
  ext xs
  simpa [Acceptor.mem_language] using accepts_ofNA_iff a xs

end TwoWayNA

end Cslib.Automata
