/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.TransformsTapes
public import Mathlib.Basic.Finite.Sum

/-!
# Repeating a machine until a tape signals stop

`repeatTM i x tm` runs `tm` over and over. After each run of `tm`, it inspects the symbol under the
head of work tape `i`: if it is `some x` the loop halts, otherwise `tm` is started again on the
tapes as it left them. This is the loop-back control combinator: the state space is `State₀ ⊕
Unit`, where `Sum.inr ()` is a fresh *check* state; `tm`'s halting transition is redirected to it,
so the inspection costs one extra step per round and the handoff back to `tm` costs no step.

The specification `exists_transformsTapes_repeat` is stated for a family indexed by `J`, with a
round predicate `P j n` describing the tapes after `n` rounds and a stopping predicate `R j`.  As
long as round `n < N j` leaves the flag unequal to `x`, the loop keeps going; round `N j` leaves it
equal to `x`, so the loop halts.  Because every round begins from a `wordsCfg` (all heads at the
start of their words), the configurations thread cleanly round to round.

The time bound is `(N j + 1) * (t j + 1)`: there are `N j + 1` rounds, each of at most `t j` steps
of `tm` plus one inspection step.  The space bound `2 * k * s j + k` is **independent of the number
of rounds**: every round starts with the heads at `0` and uses at most `s j` cells, so on each tape
that round's visited cells form an interval around `0` contained in `[-s j, s j]`; the whole run's
visited set is the union of the rounds' sets, still within `[-s j, s j]`, hence at most `2 * s j +
1` cells per tape.

## Main results

* `Turing.MultiTapeTM.exists_transformsTapes_repeat`: from a family of per-round transformations
  and a stopping transformation, a single machine that loops until tape `i` shows `x`, with time
  bound `(N j + 1) * (t j + 1)` and space bound `2 * k * s j + k`.
-/

namespace Turing.MultiTapeTM

variable {k : ℕ} {State₀ : Type*} {input : List Bool}

namespace Repeat

private lemma runFrom_add {State : Type*} (tm : MultiTapeTM k Bool State)
    (cfg : Cfg k Bool State input) (a b : ℕ) :
    tm.runFrom cfg (a + b) = tm.runFrom (tm.runFrom cfg a) b := by
  change tm.step^[a + b] cfg = tm.step^[b] (tm.step^[a] cfg)
  rw [Nat.add_comm a b, Function.iterate_add_apply]

private lemma runFrom_succ {State : Type*} (tm : MultiTapeTM k Bool State)
    (cfg : Cfg k Bool State input) (n : ℕ) :
    tm.runFrom cfg (n + 1) = tm.step (tm.runFrom cfg n) := by
  change tm.step^[n + 1] cfg = tm.step (tm.step^[n] cfg)
  rw [Function.iterate_succ_apply']

/-- The looping machine.  On a live state `Sum.inl q` it runs `tm`, but redirects `tm`'s halting
transition to the fresh check state `Sum.inr ()`.  On the check state it reads the symbol under
tape `i`'s head: if it is `some x` the machine halts, otherwise it restarts `tm` from its initial
state, writing nothing and moving no head. -/
private def repeatTM (i : Fin k) (x : Bool) (tm : MultiTapeTM k Bool State₀) :
    MultiTapeTM k Bool (State₀ ⊕ Unit) where
  q₀ := .inl tm.q₀
  tr q inp work :=
    match q with
    | .inl q =>
      let a := tm.tr q inp work
      { a with state := some (a.state.elim (.inr ()) .inl) }
    | .inr _ =>
      if work i = some x then
        { inputTape := 0, workTapes := fun _ => (none, 0), output := none, state := none }
      else
        { inputTape := 0, workTapes := fun _ => (none, 0), output := none,
          state := some (.inl tm.q₀) }

variable {i : Fin k} {x : Bool} {tm : MultiTapeTM k Bool State₀}

/-- A configuration of `tm`, embedded into the looping machine: a halted state is sent to the
check state `Sum.inr ()`, a live state is carried by `Sum.inl`.  Under this map the machine mirrors
`tm` step for step while `tm` is live, and lands on the check state exactly when `tm` halts. -/
private def leftCfg (cfg : Cfg k Bool State₀ input) : Cfg k Bool (State₀ ⊕ Unit) input :=
  cfg.mapState (fun st => some (st.elim (.inr ()) .inl))

@[simp]
private lemma workTapePos_leftCfg (cfg : Cfg k Bool State₀ input) :
    (leftCfg cfg).workTapePos = cfg.workTapePos := rfl

private lemma leftCfg_wordsCfg (q : Option State₀) (ws : Fin k → List Bool) (out : List Bool) :
    leftCfg (input := input) (wordsCfg input q ws out) =
      wordsCfg input (some (q.elim (.inr ()) .inl)) ws out := rfl

/-- On `tm`'s live configurations, the looping machine mirrors `tm` step for step. -/
private lemma step_leftCfg (cfg : Cfg k Bool State₀ input) (h : cfg.state ≠ none) :
    (repeatTM i x tm).step (leftCfg cfg) = leftCfg (tm.step cfg) := by
  obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp h
  have h1 : (leftCfg cfg).state = some (Sum.inl q : State₀ ⊕ Unit) := by
    simp [leftCfg, Cfg.mapState, hq]
  simp only [step, h1, hq]
  rfl

/-- While `tm` is live, the looping machine mirrors it. -/
private lemma runFrom_leftCfg (cfg : Cfg k Bool State₀ input) (n : ℕ)
    (h : ∀ m < n, (tm.runFrom cfg m).state ≠ none) :
    (repeatTM i x tm).runFrom (leftCfg cfg) n = leftCfg (tm.runFrom cfg n) := by
  simp only [runFrom] at h ⊢
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      ih fun m hm => h m (by omega),
      step_leftCfg _ (h n (by omega))]

/-- The run of the looping machine on a starting `wordsCfg`, while `tm` is live. -/
private lemma runFrom_left_wordsCfg (w : Fin k → List Bool) (out : List Bool) (n : ℕ)
    (hact : ∀ m < n, (tm.runFrom (wordsCfg input (some tm.q₀) w out) m).state ≠ none) :
    (repeatTM i x tm).runFrom (wordsCfg input (some (Sum.inl tm.q₀)) w out) n =
      leftCfg (tm.runFrom (wordsCfg input (some tm.q₀) w out) n) := by
  have h : wordsCfg (State := State₀ ⊕ Unit) input (some (Sum.inl tm.q₀)) w out =
      leftCfg (wordsCfg input (some tm.q₀) w out) := rfl
  rw [h, runFrom_leftCfg _ n hact]

/-- The check step, when tape `i` shows `x`: the machine halts, leaving the words untouched. -/
private lemma step_check_halt (ws : Fin k → List Bool) (out : List Bool)
    (h : (ws i).head? = some x) :
    (repeatTM i x tm).step (wordsCfg input (some (Sum.inr ())) ws out) =
      wordsCfg input none ws out := by
  have hstate : (wordsCfg (State := State₀ ⊕ Unit) input (some (Sum.inr ())) ws out).state =
      some (Sum.inr ()) := rfl
  rw [step_apply_of_state hstate]
  refine Cfg.ext ?_ ?_ ?_ ?_ ?_ <;>
    simp [repeatTM, Cfg.workTapeSymbols, tapeOfList_zero, h, wordsCfg, Action.apply, SignType.cast]

/-- The check step, when tape `i` does not show `x`: the machine restarts `tm` from its initial
state, leaving the words untouched. -/
private lemma step_check_restart (ws : Fin k → List Bool) (out : List Bool)
    (h : ¬ (ws i).head? = some x) :
    (repeatTM i x tm).step (wordsCfg input (some (Sum.inr ())) ws out) =
      wordsCfg input (some (Sum.inl tm.q₀)) ws out := by
  have hstate : (wordsCfg (State := State₀ ⊕ Unit) input (some (Sum.inr ())) ws out).state =
      some (Sum.inr ()) := rfl
  rw [step_apply_of_state hstate]
  refine Cfg.ext ?_ ?_ ?_ ?_ ?_ <;>
    simp [repeatTM, Cfg.workTapeSymbols, tapeOfList_zero, h, wordsCfg, Action.apply, SignType.cast]

/-- On the check state, the step moves no work-tape head. -/
private lemma check_step_workTapePos (c : Cfg k Bool (State₀ ⊕ Unit) input)
    (hstate : c.state = some (Sum.inr ())) (l : Fin k) :
    ((repeatTM i x tm).step c).workTapePos l = c.workTapePos l := by
  have h2 : (((repeatTM i x tm).tr (Sum.inr ()) c.inputSymbol c.workTapeSymbols).workTapes l).2
      = 0 := by
    simp only [repeatTM]
    split <;> rfl
  rw [step_workTapePos_of_state hstate l, h2]
  simp

/-- One full round takes the loop from a `wordsCfg` on `tm`'s initial state to a `wordsCfg` on
`tm`'s initial state, when tape `i` does not show `x`. -/
private lemma runFrom_round_restart (w w' : Fin k → List Bool) (out : List Bool) (u : ℕ)
    (hact : ∀ m < u, (tm.runFrom (wordsCfg input (some tm.q₀) w out) m).state ≠ none)
    (hrun_u : tm.runFrom (wordsCfg input (some tm.q₀) w out) u = wordsCfg input none w' out)
    (hrestart : ¬ (w' i).head? = some x) :
    (repeatTM i x tm).runFrom (wordsCfg input (some (Sum.inl tm.q₀)) w out) (u + 1) =
      wordsCfg input (some (Sum.inl tm.q₀)) w' out := by
  rw [runFrom_succ, runFrom_left_wordsCfg w out u hact, hrun_u]
  exact step_check_restart w' out hrestart

/-- The last round: when tape `i` shows `x`, the loop halts on a `wordsCfg`. -/
private lemma runFrom_round_halt (w w' : Fin k → List Bool) (out : List Bool) (u : ℕ)
    (hact : ∀ m < u, (tm.runFrom (wordsCfg input (some tm.q₀) w out) m).state ≠ none)
    (hrun_u : tm.runFrom (wordsCfg input (some tm.q₀) w out) u = wordsCfg input none w' out)
    (hstop : (w' i).head? = some x) :
    (repeatTM i x tm).runFrom (wordsCfg input (some (Sum.inl tm.q₀)) w out) (u + 1) =
      wordsCfg input none w' out := by
  rw [runFrom_succ, runFrom_left_wordsCfg w out u hact, hrun_u]
  exact step_check_halt w' out hstop

/-- A `tm`-run started at a `wordsCfg` (head at `0`) using at most `s0` cells stays, on each tape,
within `[-s0, s0]`. -/
private lemma visited_subset_Icc (cfg : Cfg k Bool State₀ input) (u : ℕ) (l : Fin k) (s0 : ℕ)
    (h0 : cfg.workTapePos l = 0) (hsp : tm.spaceUsed cfg u ≤ s0) :
    tm.visitedByTapeHead cfg u l ⊆ Finset.Icc (-(s0 : ℤ)) (s0 : ℤ) := by
  intro z hz
  have hbound := tm.natAbs_le_spaceUsedByTape_of_mem_visited hz
  rw [h0, sub_zero] at hbound
  have hcard := (tm.spaceUsedByTape_le_spaceUsed cfg u l).trans hsp
  rw [Finset.mem_Icc]
  omega

/-- **The per-round space confinement.** Every configuration reached within one round keeps every
work-tape head inside `[-s0, s0]`: during `tm`'s phase because that phase starts with the head at
`0` and uses at most `s0` cells, and at the check step because it moves no head. -/
private lemma round_Icc (w w' : Fin k → List Bool) (out : List Bool) (u : ℕ) (s0 : ℕ)
    (hact : ∀ m < u, (tm.runFrom (wordsCfg input (some tm.q₀) w out) m).state ≠ none)
    (hrun_u : tm.runFrom (wordsCfg input (some tm.q₀) w out) u = wordsCfg input none w' out)
    (hsp : tm.spaceUsed (wordsCfg input (some tm.q₀) w out) u ≤ s0) :
    ∀ m ≤ u + 1, ∀ l : Fin k,
      ((repeatTM i x tm).runFrom (wordsCfg input (some (Sum.inl tm.q₀)) w out) m).workTapePos l
        ∈ Finset.Icc (-(s0 : ℤ)) (s0 : ℤ) := by
  intro m hm l
  rcases Nat.lt_or_ge m (u + 1) with hlt | hge
  · -- during `tm`'s phase: the head is in `tm`'s visited set, which lies in `[-s0, s0]`
    have hmu : m ≤ u := by omega
    rw [runFrom_left_wordsCfg w out m (fun r hr => hact r (by omega)), workTapePos_leftCfg]
    apply visited_subset_Icc (tm := tm) _ u l s0 rfl hsp
    exact mem_visitedByTapeHead.mpr ⟨m, by omega, rfl⟩
  · -- the check step: the head does not move, and it sits at `0`
    have hmeq : m = u + 1 := by omega
    subst hmeq
    rw [runFrom_succ, runFrom_left_wordsCfg w out u hact, hrun_u]
    rw [check_step_workTapePos _ (by rw [leftCfg_wordsCfg]; rfl) l]
    rw [leftCfg_wordsCfg]
    simp only [Finset.mem_Icc, wordsCfg_workTapePos]
    omega

end Repeat

open Repeat in
/-- **Repeating a machine until a tape signals stop.**  Given a family of per-round
transformations `hround` (each of which advances the round predicate `P j n` to `P j (n+1)` while
leaving tape `i`'s head symbol unequal to `x`) and a stopping transformation `hstop` (which
establishes `R j` while leaving tape `i`'s head symbol equal to `x`), a single machine loops `tm`,
inspecting tape `i` after each round, until that head symbol equals `x`.  It performs `N j + 1`
rounds, so the time bound is `(N j + 1) * (t j + 1)`; because every round starts with the heads at
the start of their words and uses at most `s j` cells, the space bound `2 * k * s j + k` is
independent of the number of rounds. -/
public theorem exists_transformsTapes_repeat {J : Type*} {k : ℕ} (i : Fin k) (x : Bool)
    {State₀ : Type} [Finite State₀] {tm : MultiTapeTM k Bool State₀}
    {P : J → ℕ → (input : List Bool) → (Fin k → List Bool) → Prop}
    {R : J → (input : List Bool) → (Fin k → List Bool) → Prop}
    {N : J → ℕ} {t s : J → ℕ}
    (hround : ∀ (j : J) (n : ℕ), n < N j → TransformsTapes tm (P j n)
      (fun input _ ws' => P j (n + 1) input ws' ∧ (ws' i).head? ≠ some x) (t j) (s j))
    (hstop : ∀ j : J, TransformsTapes tm (P j (N j))
      (fun input _ ws' => R j input ws' ∧ (ws' i).head? = some x) (t j) (s j)) :
    ∃ (State : Type) (_ : Finite State) (tm' : MultiTapeTM k Bool State), ∀ j : J,
      TransformsTapes tm' (P j 0) (fun input _ ws' => R j input ws')
        ((N j + 1) * (t j + 1)) (2 * k * s j + k) := by
  refine ⟨State₀ ⊕ Unit, inferInstance, repeatTM i x tm, fun j input ws out hP0 => ?_⟩
  rw [show (repeatTM i x tm).q₀ = Sum.inl tm.q₀ from rfl]
  set start := wordsCfg (State := State₀ ⊕ Unit) input (some (Sum.inl tm.q₀)) ws out with hstart
  -- After `n ≤ N j` rounds, the loop is back on `tm`'s initial state with words satisfying `P j n`,
  -- has taken at most `n * (t j + 1)` steps, and has kept every head inside `[-s j, s j]`.
  have hrec : ∀ n, n ≤ N j → ∃ (T : ℕ) (wsn : Fin k → List Bool),
      (repeatTM i x tm).runFrom start T = wordsCfg input (some (Sum.inl tm.q₀)) wsn out ∧
      P j n input wsn ∧ T ≤ n * (t j + 1) ∧
      ∀ m ≤ T, ∀ l, ((repeatTM i x tm).runFrom start m).workTapePos l
        ∈ Finset.Icc (-(s j : ℤ)) (s j : ℤ) := by
    intro n
    induction n with
    | zero =>
      intro _
      refine ⟨0, ws, by simp only [runFrom, Function.iterate_zero, id_eq, hstart],
        hP0, by omega, fun m hm l => ?_⟩
      have : m = 0 := by omega
      subst this
      simp only [runFrom, Function.iterate_zero, id_eq, hstart]
      simp only [Finset.mem_Icc, wordsCfg_workTapePos]
      omega
    | succ n ih =>
      intro hn
      obtain ⟨T, wsn, hrun, hPn, hT, hIcc⟩ := ih (by omega)
      obtain ⟨wsn', hrunTm, hQ, hsp⟩ := hround j n (by omega) input wsn out hPn
      obtain ⟨u, hu, huhalt, huactive⟩ := exists_minimal_halting_time tm
        (wordsCfg input (some tm.q₀) wsn out) (t j) (by rw [hrunTm]; rfl)
      have hu_run : tm.runFrom (wordsCfg input (some tm.q₀) wsn out) u =
          wordsCfg input none wsn' out := by
        rw [← runFrom_eq_of_halt tm _ hu huhalt, hrunTm]
      have hsp_u : tm.spaceUsed (wordsCfg input (some tm.q₀) wsn out) u ≤ s j :=
        le_trans (spaceUsed_mono tm _ hu) hsp
      refine ⟨T + (u + 1), wsn', ?_, hQ.1, ?_, ?_⟩
      · rw [runFrom_add]
        rw [hrun, runFrom_round_restart wsn wsn' out u huactive hu_run hQ.2]
      · have hexp : (n + 1) * (t j + 1) = n * (t j + 1) + (t j + 1) := by rw [add_mul, one_mul]
        omega
      · intro m hm l
        rcases Nat.lt_or_ge m (T + 1) with hmT | hmT
        · exact hIcc m (by omega) l
        · obtain ⟨m', rfl⟩ : ∃ m', m = T + m' := ⟨m - T, by omega⟩
          rw [runFrom_add]
          rw [hrun]
          exact round_Icc wsn wsn' out u (s j) huactive hu_run hsp_u m' (by omega) l
  -- The stopping round: apply `hstop`, take the minimal halting time, and read off `R j`.
  obtain ⟨T, wsN, hrun, hPN, hT, hIcc⟩ := hrec (N j) le_rfl
  obtain ⟨ws', hrunTm, hQ, hsp⟩ := hstop j input wsN out hPN
  obtain ⟨u, hu, huhalt, huactive⟩ := exists_minimal_halting_time tm
    (wordsCfg input (some tm.q₀) wsN out) (t j) (by rw [hrunTm]; rfl)
  have hu_run : tm.runFrom (wordsCfg input (some tm.q₀) wsN out) u =
      wordsCfg input none ws' out := by
    rw [← runFrom_eq_of_halt tm _ hu huhalt, hrunTm]
  have hsp_u : tm.spaceUsed (wordsCfg input (some tm.q₀) wsN out) u ≤ s j :=
    le_trans (spaceUsed_mono tm _ hu) hsp
  -- The head stays in `[-s j, s j]` for the whole run.
  have hIccAll : ∀ m ≤ T + (u + 1), ∀ l,
      ((repeatTM i x tm).runFrom start m).workTapePos l ∈ Finset.Icc (-(s j : ℤ)) (s j : ℤ) := by
    intro m hm l
    rcases Nat.lt_or_ge m (T + 1) with hmT | hmT
    · exact hIcc m (by omega) l
    · obtain ⟨m', rfl⟩ : ∃ m', m = T + m' := ⟨m - T, by omega⟩
      rw [runFrom_add]
      rw [hrun]
      exact round_Icc wsN ws' out u (s j) huactive hu_run hsp_u m' (by omega) l
  have htime : T + (u + 1) ≤ (N j + 1) * (t j + 1) := by
    have hexp : (N j + 1) * (t j + 1) = N j * (t j + 1) + (t j + 1) := by
      rw [add_mul, one_mul]
    omega
  have hrunLoop : (repeatTM i x tm).runFrom start (T + (u + 1)) =
      wordsCfg input none ws' out := by
    rw [runFrom_add]
    rw [hrun, runFrom_round_halt wsN ws' out u huactive hu_run hQ.2]
  have hhaltLoop : ((repeatTM i x tm).runFrom start (T + (u + 1))).state = none := by
    rw [hrunLoop]
    rfl
  refine ⟨ws', ?_, hQ.1, ?_⟩
  · -- the run ends in the halting `wordsCfg`
    rw [runFrom_eq_of_halt _ _ htime hhaltLoop, hrunLoop]
  · -- space bound: each tape's visited set lies in `[-s j, s j]`, so has at most `2 * s j + 1`
    -- cells, and there are `k` tapes
    rw [spaceUsed_eq_of_halt _ htime hhaltLoop]
    have hbound : ∀ l : Fin k,
        (repeatTM i x tm).spaceUsedByTape start (T + (u + 1)) l ≤ 2 * s j + 1 := by
      intro l
      have hsub : (repeatTM i x tm).visitedByTapeHead start (T + (u + 1)) l ⊆
          Finset.Icc (-(s j : ℤ)) (s j : ℤ) := by
        intro z hz
        obtain ⟨m, hm, rfl⟩ := mem_visitedByTapeHead.mp hz
        exact hIccAll m (by omega) l
      calc (repeatTM i x tm).spaceUsedByTape start (T + (u + 1)) l
          ≤ (Finset.Icc (-(s j : ℤ)) (s j : ℤ)).card := Finset.card_le_card hsub
        _ = 2 * s j + 1 := by rw [Int.card_Icc]; omega
    calc (repeatTM i x tm).spaceUsed start (T + (u + 1))
        = ∑ l : Fin k, (repeatTM i x tm).spaceUsedByTape start (T + (u + 1)) l := rfl
      _ ≤ ∑ _l : Fin k, (2 * s j + 1) := Finset.sum_le_sum fun l _ => hbound l
      _ = 2 * k * s j + k := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id,
            Nat.mul_add, Nat.mul_one, ← Nat.mul_assoc, Nat.mul_comm k 2]

end Turing.MultiTapeTM
