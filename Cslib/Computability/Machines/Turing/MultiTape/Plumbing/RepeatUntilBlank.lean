/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Mathlib.Data.Fintype.Option
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.TransformsTapes

/-!
# Repeating a machine until a tape goes blank

`repeatUntilBlank i tm` runs `tm` repeatedly. After each round it reads the cell under the head of
work tape `i` and halts if that cell is blank. Each round of a `Turing.MultiTapeTM.TransformsTapes`
specification ends with every head on the first cell of its word, so the loop halts exactly when
the word on tape `i` is empty. The body always runs at least once.

## Main results

* `Turing.MultiTapeTM.transformsTapes_repeatUntilBlank`: a loop invariant preserved by every round
  gives a specification of `repeatUntilBlank i tm`, with time bound `(rounds + 1) * (t + 1)` and
  space bound `2 * k * s + k`.
-/

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}

/-- The states of `repeatUntilBlank i tm`: those of `tm`, and a state `check` for reading tape `i`
between rounds. -/
public inductive RepeatUntilBlankState (State : Type*) where
  /-- The repeated machine is running, in its state `q`. -/
  | run (q : State)
  /-- Tape `i` is being read, between two rounds. -/
  | check

public instance [Finite State] : Finite (RepeatUntilBlankState State) :=
  Finite.of_injective (fun q => match q with | .run q => some q | .check => none)
    fun q q' h => by cases q <;> cases q' <;> simp_all

/-- `tm`, with its halting transitions sent to the state `check`. From `check`, the machine halts
if the cell under the head of tape `i` is blank and otherwise restarts `tm`, moving no head. -/
public noncomputable def repeatUntilBlank (i : Fin k) (tm : MultiTapeTM k Symbol State) :
    MultiTapeTM k Symbol (RepeatUntilBlankState State) :=
  ofTr (.run tm.q₀) fun q inp work =>
    match q with
    | .run q =>
      let a := tm.tr q inp work
      { a with state := some (a.state.elim .check .run) }
    | .check =>
      { inputTape := 0, workTapes := fun _ => (none, 0), output := none,
        state := (work i).map fun _ => .run tm.q₀ }

namespace RepeatUntilBlank

variable {i : Fin k} {tm : MultiTapeTM k Symbol State}

/-- A configuration of `tm` as a configuration of `repeatUntilBlank i tm`: a live state `q` becomes
`run q` and the halted state becomes `check`. -/
def runCfg (cfg : Cfg k Symbol State input) :
    Cfg k Symbol (RepeatUntilBlankState State) input :=
  cfg.mapState (fun st => some (st.elim .check .run))

@[simp]
lemma workTapePos_runCfg (cfg : Cfg k Symbol State input) :
    (runCfg cfg).workTapePos = cfg.workTapePos := rfl

@[simp]
lemma runCfg_wordsCfg_some (q : State) (ws : Fin k → List Symbol) (out : List Symbol) :
    runCfg (input := input) (wordsCfg input (some q) ws out) =
      wordsCfg input (some (.run q)) ws out := rfl

@[simp]
lemma runCfg_wordsCfg_none (ws : Fin k → List Symbol) (out : List Symbol) :
    runCfg (State := State) (input := input) (wordsCfg input none ws out) =
      wordsCfg input (some .check) ws out := rfl

lemma q₀_repeatUntilBlank : (repeatUntilBlank i tm).q₀ = .run tm.q₀ := rfl

/-- On `tm`'s live configurations, the looping machine mirrors `tm` step for step. -/
lemma step_runCfg (cfg : Cfg k Symbol State input) (h : ¬ cfg.Halted) :
    (repeatUntilBlank i tm).step (runCfg cfg) = runCfg (tm.step cfg) := by
  obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp h
  have hstate : (runCfg cfg).state = some (RepeatUntilBlankState.run q) := by
    simp [runCfg, Cfg.mapState, hq]
  rw [step_of_state hstate, step_of_state hq]
  simp only [repeatUntilBlank, tr_ofTr]
  rfl

/-- From `check` on a `wordsCfg` configuration, the machine halts if the word on tape `i` is empty
and otherwise restarts `tm`, leaving the words unchanged. -/
lemma step_check (ws : Fin k → List Symbol) (out : List Symbol) :
    (repeatUntilBlank i tm).step (wordsCfg input (some .check) ws out) =
      wordsCfg input (if ws i = [] then none else some (.run tm.q₀)) ws out := by
  rw [step_of_state rfl]
  refine Cfg.ext ?_ ?_ ?_ ?_ ?_ <;> cases h : ws i <;>
    simp [repeatUntilBlank, Cfg.workTapeSymbols, tapeOfList_zero, wordsCfg, Action.apply,
      SignType.cast, h]

/-- One round of the loop. If `tm` transforms words satisfying `P` within `t` steps and `s` cells,
then from `tm`'s initial state on such words `w` the loop has a run path of at most `t + 1` steps
within `[-s, s]` to the words `w'` that `tm` leaves: the running steps of `tm`, and then reading
tape `i`, which halts the loop if `w' i` is empty and otherwise starts the next round. -/
lemma exists_round {P : (input : List Symbol) → (Fin k → List Symbol) → Prop}
    {Q : (input : List Symbol) → (Fin k → List Symbol) → (Fin k → List Symbol) →
      List Symbol → Prop} {t s : ℕ}
    (h : TransformsTapes tm P Q t s) {w : Fin k → List Symbol} (out : List Symbol)
    (hP : P input w) :
    ∃ w' e, Q input w w' e ∧ ∃ p : (repeatUntilBlank i tm).RunPath input,
      p.head = wordsCfg input (some (.run tm.q₀)) w out ∧
      p.last = wordsCfg input (if w' i = [] then none else some (.run tm.q₀)) w' (out ++ e) ∧
      p.length ≤ t + 1 ∧ p.InWindow s := by
  obtain ⟨w', e, hQ, p, hhead, hlast, htime, hspace⟩ := h input w out hP
  obtain ⟨q, hqhead, hqlast, hqlen, hqmem⟩ := p.exists_running (by rw [hlast]; rfl)
  let f := runningStepHom (tm' := repeatUntilBlank i tm) (input := input) runCfg step_runCfg
  have hcheck : (repeatUntilBlank i tm).Step (q.map f).last
      (wordsCfg input (if w' i = [] then none else some (.run tm.q₀)) w' (out ++ e)) := by
    simp [f, hqlast, hlast, step_check]
  refine ⟨w', e, hQ, (q.map f).snoc _ hcheck, by simp [f, hqhead, hhead], by simp,
    by simp [MultiTapeNTM.RunPath.time] at htime ⊢; lia, ?_⟩
  -- the heads of `tm` stay within `[-s, s]`, and reading tape `i` moves none of them
  have hwin := MultiTapeNTM.RunPath.inWindow_of_space_le (p := p) (by simp [hhead]) hspace
  intro c hc
  rcases RelSeries.mem_snoc.mp hc with hc | rfl
  · obtain ⟨c₀, hc₀, rfl⟩ := RelSeries.exists_of_mem_map hc
    exact hwin c₀ (hqmem c₀ hc₀)
  · simp [mem_window]

end RepeatUntilBlank

open RepeatUntilBlank in
/-- Let `P n` be a loop invariant after `n` rounds, on the words on the tapes and the word emitted
so far. If each round `n < rounds` takes `P n` to `P (n + 1)` and leaves tape `i` non-empty, and
the round after that takes `P rounds` to `R` and empties tape `i`, then `repeatUntilBlank i tm`
takes `P 0` to `R`.

Each of the `rounds + 1` rounds takes at most `t + 1` steps. No head leaves `[-s, s]`, since every
round starts with all heads at cell `0` and uses at most `s` cells. -/
public theorem transformsTapes_repeatUntilBlank (i : Fin k) {tm : MultiTapeTM k Symbol State}
    {P : ℕ → (input : List Symbol) → (Fin k → List Symbol) → List Symbol → Prop}
    {R : (input : List Symbol) → (Fin k → List Symbol) → List Symbol → Prop} {rounds t s : ℕ}
    (hround : ∀ n < rounds, ∀ emitted, TransformsTapes tm (fun input ws => P n input ws emitted)
      (fun input _ ws' e => P (n + 1) input ws' (emitted ++ e) ∧ ws' i ≠ []) t s)
    (hstop : ∀ emitted, TransformsTapes tm (fun input ws => P rounds input ws emitted)
      (fun input _ ws' e => R input ws' (emitted ++ e) ∧ ws' i = []) t s) :
    TransformsTapes (repeatUntilBlank i tm) (fun input ws => P 0 input ws [])
      (fun input _ ws' emitted => R input ws' emitted)
      ((rounds + 1) * (t + 1)) (2 * k * s + k) := by
  intro input ws out hP0
  rw [q₀_repeatUntilBlank]
  set start := wordsCfg (State := RepeatUntilBlankState State) input (some (.run tm.q₀)) ws out
    with hstart
  -- after `n ≤ rounds` rounds, the loop has a run path of at most `n * (t + 1)` steps within
  -- `[-s, s]` back to `tm`'s initial state, with `P n` holding
  have hrec : ∀ n ≤ rounds, ∃ (p : (repeatUntilBlank i tm).RunPath input)
      (wsn : Fin k → List Symbol) (acc : List Symbol), p.head = start ∧
      p.last = wordsCfg input (some (.run tm.q₀)) wsn (out ++ acc) ∧ p.length ≤ n * (t + 1) ∧
      p.InWindow s ∧ P n input wsn acc := by
    intro n hn
    induction n with
    | zero =>
      refine ⟨.singleton _ start, ws, [], rfl, by simp [hstart], by simp, ?_, hP0⟩
      rintro _ ⟨_, rfl⟩ l
      change start.workTapePos l ∈ _
      simp [hstart, mem_window]
    | succ n ih =>
      obtain ⟨p, wsn, acc, hhead, hlast, hlen, hwin, hPn⟩ := ih (by lia)
      obtain ⟨wsn', e, hQ, q, hqhead, hqlast, hqlen, hqwin⟩ :=
        exists_round (hround n (by lia) acc) (out ++ acc) hPn
      rw [ite_eq_right hQ.2, List.append_assoc] at hqlast
      exact ⟨p.smash q (hlast.trans hqhead.symm), wsn', acc ++ e, by simp [hhead], by simp [hqlast],
        by simp; lia, hwin.smash hqwin, hQ.1⟩
  -- the last round halts the loop
  obtain ⟨p, wsLast, acc, hhead, hlast, hlen, hwin, hPlast⟩ := hrec rounds le_rfl
  obtain ⟨ws', e, hQ, q, hqhead, hqlast, hqlen, hqwin⟩ :=
    exists_round (hstop acc) (out ++ acc) hPlast
  rw [ite_eq_left hQ.2, List.append_assoc] at hqlast
  -- the joined path runs the loop from `start` to its halting configuration
  exact ⟨ws', acc ++ e, hQ.1, p.smash q (hlast.trans hqhead.symm), by simp [hhead],
    by simp [hqlast], by simp [MultiTapeNTM.RunPath.time]; lia,
    (hwin.smash hqwin).space_le.trans (by lia)⟩

end Turing.MultiTapeTM
