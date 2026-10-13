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

/-- Up to its halting step, the looping machine mirrors `tm`. -/
lemma runFrom_runCfg {cfg : Cfg k Symbol State input} {u n : ℕ} (hhalt : tm.HaltsAt cfg u)
    (hn : n ≤ u) :
    (repeatUntilBlank i tm).runFrom (runCfg cfg) n = runCfg (tm.runFrom cfg n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [runFrom_succ, runFrom_succ, ih (by lia), step_runCfg _ (hhalt.not_halted (by lia))]

/-- From `check` on a `wordsCfg` configuration, the machine halts if the word on tape `i` is empty
and otherwise restarts `tm`, leaving the words unchanged. -/
lemma step_check (ws : Fin k → List Symbol) (out : List Symbol) :
    (repeatUntilBlank i tm).step (wordsCfg input (some .check) ws out) =
      wordsCfg input (if ws i = [] then none else some (.run tm.q₀)) ws out := by
  rw [step_of_state rfl]
  refine Cfg.ext ?_ ?_ ?_ ?_ ?_ <;> cases h : ws i <;>
    simp [repeatUntilBlank, Cfg.workTapeSymbols, tapeOfList_zero, wordsCfg, Action.apply,
      SignType.cast, h]

/-- One round of the loop. If `tm` takes `w` to `w'` and `out` to `out'` within `τ` steps and `σ`
cells, then the loop has a run path of at most `τ + 1` steps within `[-σ, σ]` from `tm`'s initial
state on `w` and `out` to `w'` and `out'`, either halted or ready for the next round. -/
lemma exists_round {w w' : Fin k → List Symbol} {out out' : List Symbol} {τ σ : ℕ}
    (hrun : tm.runFrom (wordsCfg input (some tm.q₀) w out) τ = wordsCfg input none w' out')
    (hsp : tm.spaceUsed (wordsCfg input (some tm.q₀) w out) τ ≤ σ) :
    ∃ p : (repeatUntilBlank i tm).RunPath input, p.head = wordsCfg input (some (.run tm.q₀)) w out ∧
      p.last = wordsCfg input (if w' i = [] then none else some (.run tm.q₀)) w' out' ∧
      p.length ≤ τ + 1 ∧ p.InWindow σ := by
  obtain ⟨u, hu, hhalt⟩ := exists_haltsAt (show (tm.runFrom _ τ).Halted by rw [hrun]; rfl)
  -- up to step `u` the loop mirrors `tm`, and at step `u + 1` it reads tape `i`
  have hround : (repeatUntilBlank i tm).runFrom (wordsCfg input (some (.run tm.q₀)) w out) (u + 1) =
      wordsCfg input (if w' i = [] then none else some (.run tm.q₀)) w' out' := by
    rw [runFrom_succ, ← runCfg_wordsCfg_some,
      runFrom_runCfg hhalt le_rfl, ← hhalt.runFrom_eq hu, hrun, runCfg_wordsCfg_none, step_check]
  refine ⟨.ofDeterministic _ (wordsCfg input (some (.run tm.q₀)) w out) (u + 1), rfl, hround,
    Nat.succ_le_succ hu, ?_⟩
  rintro _ ⟨⟨m, hm⟩, rfl⟩ l
  obtain hm | rfl := (Nat.lt_succ_iff.mp (show m < u + 1 + 1 from hm)).lt_or_eq
  · change Cfg.workTapePos
      ((repeatUntilBlank i tm).runFrom (runCfg (wordsCfg input (some tm.q₀) w out)) m) l ∈ _
    rw [runFrom_runCfg hhalt (by lia), workTapePos_runCfg]
    exact inWindow_ofDeterministic (fun _ => rfl) hsp _ ⟨⟨m, show m < τ + 1 by lia⟩, rfl⟩ l
  · change ((repeatUntilBlank i tm).runFrom _ (u + 1)).workTapePos l ∈ _
    simp [hround, mem_window]

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
      obtain ⟨wsn', e, hrunTm, hQ, hsp⟩ := hround n (by lia) acc input wsn (out ++ acc) hPn
      obtain ⟨q, hqhead, hqlast, hqlen, hqwin⟩ := exists_round hrunTm hsp
      rw [ite_eq_right hQ.2, List.append_assoc] at hqlast
      exact ⟨p.smash q (hlast.trans hqhead.symm), wsn', acc ++ e, by simp [hhead], by simp [hqlast],
        by simp; lia, hwin.smash hqwin, hQ.1⟩
  -- the last round halts the loop
  obtain ⟨p, wsLast, acc, hhead, hlast, hlen, hwin, hPlast⟩ := hrec rounds le_rfl
  obtain ⟨ws', e, hrunTm, hQ, hsp⟩ := hstop acc input wsLast (out ++ acc) hPlast
  obtain ⟨q, hqhead, hqlast, hqlen, hqwin⟩ := exists_round hrunTm hsp
  rw [ite_eq_left hQ.2, List.append_assoc] at hqlast
  -- the joined path is the run of the loop from `start`, which then stays halted
  set r : (repeatUntilBlank i tm).RunPath input := p.smash q (hlast.trans hqhead.symm)
  have hr : r.head = start ∧ r.last = wordsCfg input none ws' (out ++ (acc ++ e)) := by
    simp [r, hhead, hqlast]
  have hhalt : r.last.Halted := by rw [hr.2]; rfl
  refine ⟨ws', acc ++ e, ?_, hQ.1, ?_⟩
  · rw [← hr.1, runFrom_head_eq_last r hhalt (by simp [r]; lia), hr.2]
  · rw [← hr.1]
    exact (spaceUsed_head_le r hhalt _).trans ((hwin.smash hqwin).space_le.trans (by lia))

end Turing.MultiTapeTM
