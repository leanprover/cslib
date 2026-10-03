/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.TransformsTapes

/-!
# Repeating a machine until a tape signals stop

`repeatUntil i x tm` runs `tm` over and over. After each run of `tm`, it inspects the symbol under
the head of work tape `i`: if it is `x` the loop halts, otherwise `tm` is started again on the
tapes as it left them.

## Main results

* `Turing.MultiTapeTM.transformsTapes_repeatUntil`: if `tm` preserves a loop invariant round by
  round and eventually puts `x` under the head of tape `i`, then `repeatUntil i x tm` loops `tm`
  until that happens, with time bound `(rounds + 1) * (t + 1)` and space bound `2 * k * s + k`.
-/

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}

/-- The states of `repeatUntil tm`: those of `tm`, plus a fresh state in which the flag cell is
inspected between two rounds. -/
public inductive RepeatUntilState (State : Type*) where
  /-- The repeated machine is running, in its state `q`. -/
  | run (q : State)
  /-- The flag cell is being inspected, between two rounds. -/
  | check
  deriving Fintype

public instance [Finite State] : Finite (RepeatUntilState State) := by
  cases nonempty_fintype State
  infer_instance

/-- The looping machine. On a running state it runs `tm`, but redirects `tm`'s halting transition
to the fresh `check` state. On the `check` state it reads the symbol under tape `i`'s head: if it
is `x` the machine halts, otherwise it restarts `tm` from its initial state, writing nothing and
moving no head. -/
public def repeatUntil [DecidableEq Symbol] (i : Fin k) (x : Symbol)
    (tm : MultiTapeTM k Symbol State) : MultiTapeTM k Symbol (RepeatUntilState State) where
  q₀ := .run tm.q₀
  tr q inp work :=
    match q with
    | .run q =>
      let a := tm.tr q inp work
      { a with state := some (a.state.elim .check .run) }
    | .check =>
      { inputTape := 0, workTapes := fun _ => (none, 0), output := none,
        state := if work i = some x then none else some (.run tm.q₀) }

namespace RepeatUntil

variable {i : Fin k} {x : Symbol} {tm : MultiTapeTM k Symbol State}

/-- A configuration of `tm`, embedded into the looping machine: a halted state is sent to the
`check` state, a live state is carried by `run`. Under this map the machine mirrors `tm` step for
step while `tm` is live, and lands on the `check` state exactly when `tm` halts. -/
def runCfg (cfg : Cfg k Symbol State input) :
    Cfg k Symbol (RepeatUntilState State) input :=
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

variable [DecidableEq Symbol]

lemma q₀_repeatUntil : (repeatUntil i x tm).q₀ = .run tm.q₀ := rfl

/-- On `tm`'s live configurations, the looping machine mirrors `tm` step for step. -/
lemma step_runCfg (cfg : Cfg k Symbol State input) (h : ¬ cfg.Halted) :
    (repeatUntil i x tm).step (runCfg cfg) = runCfg (tm.step cfg) := by
  obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp h
  simp only [step, runCfg, Cfg.mapState, hq, Option.elim_some]
  rfl

/-- Up to its halting step, the looping machine mirrors `tm`. -/
lemma runFrom_runCfg {cfg : Cfg k Symbol State input} {u n : ℕ} (hhalt : tm.HaltsAt cfg u)
    (hn : n ≤ u) :
    (repeatUntil i x tm).runFrom (runCfg cfg) n = runCfg (tm.runFrom cfg n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [runFrom, Function.iterate_succ_apply']
    rw [← runFrom, ← runFrom, ih (by lia), step_runCfg _ (hhalt.not_halted (by lia))]

/-- The check step: the machine halts if tape `i` shows `x` and restarts `tm` from its initial
state otherwise, leaving the words untouched either way. -/
lemma step_check (ws : Fin k → List Symbol) (out : List Symbol) :
    (repeatUntil i x tm).step (wordsCfg input (some .check) ws out) =
      wordsCfg input (if (ws i).head? = some x then none else some (.run tm.q₀)) ws out := by
  rw [step_apply_of_state rfl]
  refine Cfg.ext ?_ ?_ ?_ ?_ ?_ <;>
    simp [repeatUntil, Cfg.workTapeSymbols, tapeOfList_zero, wordsCfg, Action.apply,
      SignType.cast]

/-- **One round of the loop.** Suppose the loop is about to start a round: it is in `tm`'s
initial state on words `w`, and `tm` would turn `w` into `w'` within `τ` steps using at most `σ`
cells. Then at most `τ + 1` steps later the loop has finished that round: the tapes hold `w'`,
and the machine has either halted (tape `i` shows `x`) or is back in `tm`'s initial state, ready
for the next round.

The lemma also tracks head positions: if every head stayed within `[-σ, σ]` before the round, it
still does afterwards, because `tm` starts the round with all heads at `0` and uses at most `σ`
cells, and the check step moves no head. This is what keeps the space bound of the whole loop
independent of the number of rounds. -/
lemma exists_runFrom_round {c : Cfg k Symbol (RepeatUntilState State) input} {t : ℕ}
    {w w' : Fin k → List Symbol} {out : List Symbol} {τ σ : ℕ}
    (ht : (repeatUntil i x tm).runFrom c t = wordsCfg input (some (.run tm.q₀)) w out)
    (hIcc : ∀ l, (repeatUntil i x tm).visitedByTapeHead c t l ⊆ Finset.Icc (-(σ : ℤ)) (σ : ℤ))
    (hrun : tm.runFrom (wordsCfg input (some tm.q₀) w out) τ = wordsCfg input none w' out)
    (hsp : tm.spaceUsed (wordsCfg input (some tm.q₀) w out) τ ≤ σ) :
    ∃ u ≤ τ, (repeatUntil i x tm).runFrom c (t + (u + 1)) =
        wordsCfg input (if (w' i).head? = some x then none else some (.run tm.q₀)) w' out ∧
      ∀ l, (repeatUntil i x tm).visitedByTapeHead c (t + (u + 1)) l ⊆
        Finset.Icc (-(σ : ℤ)) (σ : ℤ) := by
  obtain ⟨u, hu, hhalt⟩ := exists_haltsAt (show (tm.runFrom _ τ).Halted by rw [hrun]; rfl)
  -- up to step `u` the loop mirrors `tm`, and at step `u + 1` it inspects the flag
  have hround : (repeatUntil i x tm).runFrom (wordsCfg input (some (.run tm.q₀)) w out) (u + 1) =
      wordsCfg input (if (w' i).head? = some x then none else some (.run tm.q₀)) w' out := by
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

end RepeatUntil

open RepeatUntil in
/-- **Repeating a machine until a tape signals stop.** Think of `tm` as the body of a loop and of
`P n` as the loop invariant after `n` rounds. If every round `n < rounds` takes the invariant from
`P n` to `P (n + 1)` and leaves a symbol other than `x` under the head of tape `i`, and the final
round takes `P rounds` to the postcondition `R` and leaves `x` there, then `repeatUntil i x tm`
takes `P 0` to `R`.

The time bound counts `rounds + 1` rounds of at most `t` steps, each followed by one check step. The
space bound does not grow with the number of rounds: every round starts with all heads at `0` and
uses at most `s` cells, so no head ever leaves `[-s, s]`, which is `2 * s + 1` cells on each of
the `k` tapes. -/
public theorem transformsTapes_repeatUntil [DecidableEq Symbol] (i : Fin k) (x : Symbol)
    {tm : MultiTapeTM k Symbol State}
    {P : ℕ → (input : List Symbol) → (Fin k → List Symbol) → Prop}
    {R : (input : List Symbol) → (Fin k → List Symbol) → Prop} {rounds t s : ℕ}
    (hround : ∀ n < rounds, TransformsTapes tm (P n)
      (fun input _ ws' => P (n + 1) input ws' ∧ (ws' i).head? ≠ some x) t s)
    (hstop : TransformsTapes tm (P rounds)
      (fun input _ ws' => R input ws' ∧ (ws' i).head? = some x) t s) :
    TransformsTapes (repeatUntil i x tm) (P 0) (fun input _ ws' => R input ws')
      ((rounds + 1) * (t + 1)) (2 * k * s + k) := by
  intro input ws out hP0
  rw [q₀_repeatUntil]
  set start := wordsCfg (State := RepeatUntilState State) input (some (.run tm.q₀)) ws out
    with hstart
  -- After `n ≤ rounds` rounds the loop is back on `tm`'s initial state with words satisfying
  -- `P n`, has taken at most `n * (t + 1)` steps, and has kept every head inside `[-s, s]`.
  have hrec : ∀ n ≤ rounds, ∃ (m : ℕ) (wsn : Fin k → List Symbol), m ≤ n * (t + 1) ∧
      (repeatUntil i x tm).runFrom start m = wordsCfg input (some (.run tm.q₀)) wsn out ∧
      P n input wsn ∧
      ∀ l, (repeatUntil i x tm).visitedByTapeHead start m l ⊆
        Finset.Icc (-(s : ℤ)) (s : ℤ) := by
    intro n hn
    induction n with
    | zero =>
      exact ⟨0, ws, Nat.zero_le _, rfl, hP0, fun l => by
        simp [visitedByTapeHead, runFrom, hstart, Finset.subset_iff]⟩
    | succ n ih =>
      obtain ⟨m, wsn, hm, hrun, hPn, hIcc⟩ := ih (by lia)
      obtain ⟨wsn', hrunTm, hQ, hsp⟩ := hround n (by lia) input wsn out hPn
      obtain ⟨u, hu, hrun', hIcc'⟩ := exists_runFrom_round hrun hIcc hrunTm hsp
      rw [ite_eq_right hQ.2] at hrun'
      exact ⟨m + (u + 1), wsn', by lia, hrun', hQ.1, hIcc'⟩
  -- The stopping round halts the loop; from then on nothing changes.
  obtain ⟨m, wsLast, hm, hrun, hPlast, hIcc⟩ := hrec rounds le_rfl
  obtain ⟨ws', hrunTm, hQ, hsp⟩ := hstop input wsLast out hPlast
  obtain ⟨u, hu, hrun', hIcc'⟩ := exists_runFrom_round hrun hIcc hrunTm hsp
  rw [ite_eq_left hQ.2] at hrun'
  have hhalt : ((repeatUntil i x tm).runFrom start (m + (u + 1))).Halted := by rw [hrun']; rfl
  refine ⟨ws', ?_, hQ.1, ?_⟩
  · rw [runFrom_eq_of_halt _ _ (by lia) hhalt, hrun']
  · rw [spaceUsed_eq_of_halt _ (by lia) hhalt]
    exact spaceUsed_le_of_visited_subset_Icc _ _ hIcc'

end Turing.MultiTapeTM
