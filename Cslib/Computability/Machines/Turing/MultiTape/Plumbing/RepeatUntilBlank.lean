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

`repeatUntilBlank i tm` runs `tm` over and over. After each run of `tm`, it inspects the symbol
under the head of work tape `i`: if the cell is blank the loop halts, otherwise `tm` is started
again on the tapes as it left them.

Every round starts and ends in the normal form of `TransformsTapes`, with every head on the first
cell of the word its tape holds, so the inspected cell is the first cell of tape `i`'s word: the
loop halts exactly when that word is empty. Tape `i` is therefore the loop's flag tape, and a
round signals "go on" by leaving a non-empty word on it.

The flag is inspected only after a round, so the body always runs at least once: this is a
do-while loop, not a while loop.

## Main results

* `Turing.MultiTapeTM.transformsTapes_repeatUntilBlank`: if `tm` preserves a loop invariant round by
  round and leaves tape `i` non-empty until the last round empties it, then `repeatUntilBlank i tm`
  loops `tm` until that happens, with time bound `(rounds + 1) * (t + 1)` and space bound
  `2 * k * s + k`.
-/

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}

/-- The states of `repeatUntilBlank i tm`: those of `tm`, plus a fresh state in which the flag
cell is inspected between two rounds. -/
public inductive RepeatUntilBlankState (State : Type*) where
  /-- The repeated machine is running, in its state `q`. -/
  | run (q : State)
  /-- The flag cell is being inspected, between two rounds. -/
  | check

/-- One state more than `tm` has, so finiteness is inherited. -/
public instance [Finite State] : Finite (RepeatUntilBlankState State) :=
  Finite.of_injective (fun q => match q with | .run q => some q | .check => none)
    fun q q' h => by cases q <;> cases q' <;> simp_all

/-- The looping machine. On a running state it runs `tm`, but redirects `tm`'s halting transition
to the fresh `check` state. On the `check` state it reads the symbol under tape `i`'s head: on a
blank the machine halts, over a symbol it restarts `tm` from its initial state, writing nothing and
moving no head. -/
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

/-- A configuration of `tm`, embedded into the looping machine: a halted state is sent to the
`check` state, a live state is carried by `run`. Under this map the machine mirrors `tm` step for
step while `tm` is live, and lands on the `check` state exactly when `tm` halts. -/
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

/-- A `tm`-run started with the head of tape `l` at `0` using at most `s` cells keeps that head
within `[-s, s]`. -/
lemma workTapePos_mem_Icc (cfg : Cfg k Symbol State input) {u m : ℕ} (hm : m ≤ u) (l : Fin k)
    {s : ℕ} (h0 : cfg.workTapePos l = 0) (hsp : tm.spaceUsed cfg u ≤ s) :
    (tm.runFrom cfg m).workTapePos l ∈ Finset.Icc (-(s : ℤ)) (s : ℤ) := by
  have hbound := tm.natAbs_le_spaceUsedByTape_of_mem_visited
    (tm.visitedByTapeHead_mono cfg l hm (tm.mem_visitedByTapeHead_self cfg m l))
  have hcard := (tm.spaceUsedByTape_le_spaceUsed cfg u l).trans hsp
  rw [h0, sub_zero] at hbound
  rw [Finset.mem_Icc]
  lia

/-- The state the check step moves to is a running state exactly when the word under inspection is
non-empty. -/
lemma head?_map_run_eq_some {w : List Symbol} (hne : w ≠ []) (q : State) :
    (w.head?.map fun _ => RepeatUntilBlankState.run q) = some (.run q) := by
  obtain ⟨a, l, rfl⟩ := List.exists_cons_of_ne_nil hne
  rfl

/-- The check step halts on an empty word. -/
lemma head?_map_run_eq_none {w : List Symbol} (hnil : w = []) (q : State) :
    (w.head?.map fun _ => RepeatUntilBlankState.run q) = none := by
  rw [hnil]
  rfl

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
    simp only [runFrom, Function.iterate_succ_apply']
    rw [← runFrom, ← runFrom, ih (by lia), step_runCfg _ (hhalt.not_halted (by lia))]

/-- The check step: the machine halts if the head of tape `i` is on a blank and restarts `tm` from
its initial state otherwise, leaving the words untouched either way. Started on a `wordsCfg`, that
head is on the first cell of the word the tape holds, so the cell is blank exactly when the word is
empty. -/
lemma step_check (ws : Fin k → List Symbol) (out : List Symbol) :
    (repeatUntilBlank i tm).step (wordsCfg input (some .check) ws out) =
      wordsCfg input ((ws i).head?.map fun _ => .run tm.q₀) ws out := by
  rw [step_of_state rfl]
  refine Cfg.ext ?_ ?_ ?_ ?_ ?_ <;>
    simp [repeatUntilBlank, Cfg.workTapeSymbols, tapeOfList_zero, wordsCfg, Action.apply,
      SignType.cast]

/-- **One round of the loop.** Suppose the loop is about to start a round: it is in `tm`'s
initial state on words `w` with output `out`, and `tm` would turn `w` into `w'` within `τ` steps
using at most `σ` cells, leaving the output `out'`. Then at most `τ + 1` steps later the loop has
finished that round: the tapes hold `w'`, the output is `out'`, and the machine has either halted
(the word on tape `i` is empty) or is back in `tm`'s initial state, ready for the next round.

The lemma also tracks head positions: if every head stayed within `[-σ, σ]` before the round, it
still does afterwards, because `tm` starts the round with all heads at `0` and uses at most `σ`
cells, and the check step moves no head. This is what keeps the space bound of the whole loop
independent of the number of rounds. -/
lemma exists_runFrom_round {c : Cfg k Symbol (RepeatUntilBlankState State) input} {t : ℕ}
    {w w' : Fin k → List Symbol} {out out' : List Symbol} {τ σ : ℕ}
    (ht : (repeatUntilBlank i tm).runFrom c t = wordsCfg input (some (.run tm.q₀)) w out)
    (hIcc : ∀ l, (repeatUntilBlank i tm).visitedByTapeHead c t l ⊆ Finset.Icc (-(σ : ℤ)) (σ : ℤ))
    (hrun : tm.runFrom (wordsCfg input (some tm.q₀) w out) τ = wordsCfg input none w' out')
    (hsp : tm.spaceUsed (wordsCfg input (some tm.q₀) w out) τ ≤ σ) :
    ∃ u ≤ τ, (repeatUntilBlank i tm).runFrom c (t + (u + 1)) =
        wordsCfg input ((w' i).head?.map fun _ => .run tm.q₀) w' out' ∧
      ∀ l, (repeatUntilBlank i tm).visitedByTapeHead c (t + (u + 1)) l ⊆
        Finset.Icc (-(σ : ℤ)) (σ : ℤ) := by
  obtain ⟨u, hu, hhalt⟩ := exists_haltsAt (show (tm.runFrom _ τ).Halted by rw [hrun]; rfl)
  -- up to step `u` the loop mirrors `tm`, and at step `u + 1` it inspects the flag
  have hround : (repeatUntilBlank i tm).runFrom (wordsCfg input (some (.run tm.q₀)) w out) (u + 1) =
      wordsCfg input ((w' i).head?.map fun _ => .run tm.q₀) w' out' := by
    rw [runFrom, Function.iterate_succ_apply', ← runFrom, ← runCfg_wordsCfg_some,
      runFrom_runCfg hhalt le_rfl, ← hhalt.runFrom_eq hu, hrun, runCfg_wordsCfg_none, step_check]
  refine ⟨u, hu, ?_, fun l => ?_⟩
  · rw [runFrom, Nat.add_comm, Function.iterate_add_apply, ← runFrom, ← runFrom, ht, hround]
  rw [visitedByTapeHead_add, ht]
  refine Finset.union_subset (hIcc l) (visitedByTapeHead_subset _ fun m hm => ?_)
  rcases Nat.lt_or_eq_of_le hm with hlt | rfl
  · rw [← runCfg_wordsCfg_some, runFrom_runCfg hhalt (Nat.lt_succ_iff.mp hlt), workTapePos_runCfg]
    exact workTapePos_mem_Icc _ (Nat.lt_succ_iff.mp hlt) l rfl ((spaceUsed_mono tm _ hu).trans hsp)
  · rw [hround]
    simp

end RepeatUntilBlank

open RepeatUntilBlank in
/-- **Repeating a machine until a tape goes blank.** Think of `tm` as the body of a loop and of
`P n` as the loop invariant after `n` rounds, read of the words on the tapes *and* of the word
emitted so far. If every round `n < rounds` takes the invariant from `P n` to `P (n + 1)` and
leaves a non-empty word on tape `i`, and the final round takes `P rounds` to the postcondition `R`
and empties tape `i`, then `repeatUntilBlank i tm` takes `P 0` to `R`.

A round sees the word emitted by the rounds before it, so a loop body that emits is described
exactly as it is used: each round extends the emitted word, and the loop emits the concatenation.

The time bound counts `rounds + 1` rounds of at most `t` steps, each followed by one check step.
The space bound does not grow with the number of rounds: every round starts with all heads at `0`
and uses at most `s` cells, so no head ever leaves `[-s, s]`, which is `2 * s + 1` cells on each of
the `k` tapes. -/
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
  -- After `n ≤ rounds` rounds the loop is back on `tm`'s initial state with words and an emitted
  -- word satisfying `P n`, has taken at most `n * (t + 1)` steps, and has kept every head inside
  -- `[-s, s]`.
  have hrec : ∀ n ≤ rounds, ∃ (m : ℕ) (wsn : Fin k → List Symbol) (acc : List Symbol),
      m ≤ n * (t + 1) ∧
      (repeatUntilBlank i tm).runFrom start m =
        wordsCfg input (some (.run tm.q₀)) wsn (out ++ acc) ∧
      P n input wsn acc ∧
      ∀ l, (repeatUntilBlank i tm).visitedByTapeHead start m l ⊆
        Finset.Icc (-(s : ℤ)) (s : ℤ) := by
    intro n hn
    induction n with
    | zero =>
      exact ⟨0, ws, [], Nat.zero_le _, by simp [runFrom, hstart], hP0, fun l => by
        simp [visitedByTapeHead, runFrom, hstart, Finset.subset_iff]⟩
    | succ n ih =>
      obtain ⟨m, wsn, acc, hm, hrun, hPn, hIcc⟩ := ih (by lia)
      obtain ⟨wsn', e, hrunTm, hQ, hsp⟩ := hround n (by lia) acc input wsn (out ++ acc) hPn
      obtain ⟨u, hu, hrun', hIcc'⟩ := exists_runFrom_round hrun hIcc hrunTm hsp
      refine ⟨m + (u + 1), wsn', acc ++ e, by lia, ?_, hQ.1, hIcc'⟩
      rw [hrun', head?_map_run_eq_some hQ.2, List.append_assoc]
  -- The stopping round halts the loop; from then on nothing changes.
  obtain ⟨m, wsLast, acc, hm, hrun, hPlast, hIcc⟩ := hrec rounds le_rfl
  obtain ⟨ws', e, hrunTm, hQ, hsp⟩ := hstop acc input wsLast (out ++ acc) hPlast
  obtain ⟨u, hu, hrun', hIcc'⟩ := exists_runFrom_round hrun hIcc hrunTm hsp
  rw [head?_map_run_eq_none hQ.2] at hrun'
  have hhalt : ((repeatUntilBlank i tm).runFrom start (m + (u + 1))).Halted := by rw [hrun']; rfl
  refine ⟨ws', acc ++ e, ?_, hQ.1, ?_⟩
  · rw [runFrom_eq_of_halt _ _ (by lia) hhalt, hrun', List.append_assoc]
  · rw [spaceUsed_eq_of_halt _ (by lia) hhalt]
    exact spaceUsed_le_of_visited_subset_Icc _ _ hIcc'

end Turing.MultiTapeTM
