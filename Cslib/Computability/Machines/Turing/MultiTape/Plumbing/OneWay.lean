/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic
public import Mathlib.Data.Fintype.Prod

/-!
# Machines reading the input once from left to right

A one-way machine has no work tapes, never moves left on the input and halts on the blank after
the input. It is a finite-state transducer: it is given by a step function, which maps a state and
an input symbol to an output word and a successor state, and by a final output word for each state.

Since such a machine is constructed from this data, its output is a function on words defined by
recursion, and showing that the machine computes a given function is a statement about words only.

A machine emits at most one symbol per step, so emitting an output word of length `n` takes
`max 1 n` steps, and the input head moves only with the last of them. The machine counts the
emitted symbols in its state, so it takes a bound `m` on the length of the words that are emitted
at a time as a parameter. Such a bound exists if the state and symbol types are finite, see
`Turing.MultiTapeTM.exists_oneWay_length_le`.

## Main definitions

* `Turing.MultiTapeTM.oneWay`: the one-way machine with a given step function and final output.
* `Turing.MultiTapeTM.oneWayOutput`: the word such a machine outputs.
* `Turing.MultiTapeTM.oneWayTime`: the number of steps it takes.

`Turing.MultiTapeTM.oneWayAction` is an auxiliary definition for the construction of the machine.

## Main results

* `Turing.MultiTapeTM.computesInTimeAndSpace_oneWay`: a one-way machine outputs `oneWayOutput` in
  `oneWayTime` steps and in zero space.
* `Turing.MultiTapeTM.oneWayTime_le`: it takes at most one step per input and output symbol plus
  one.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {Symbol State : Type*}

/-- The word a one-way machine outputs when started in state `q` on the rest `w` of the input. -/
def oneWayOutput (step : State → Symbol → List Symbol × State) (final : State → List Symbol) :
    State → List Symbol → List Symbol
  | q, [] => final q
  | q, a :: w => (step q a).1 ++ oneWayOutput step final (step q a).2 w

/-- The number of steps a one-way machine takes when started in state `q` on the rest `w` of the
input: emitting a word takes one step per symbol, and at least one. -/
def oneWayTime (step : State → Symbol → List Symbol × State) (final : State → List Symbol) :
    State → List Symbol → ℕ
  | q, [] => max 1 (final q).length
  | q, a :: w => max 1 (step q a).1.length + oneWayTime step final (step q a).2 w

section Equations

variable (step : State → Symbol → List Symbol × State) (final : State → List Symbol)

@[simp]
theorem oneWayOutput_nil (q : State) : oneWayOutput step final q [] = final q := rfl

@[simp]
theorem oneWayOutput_cons (q : State) (a : Symbol) (w : List Symbol) :
    oneWayOutput step final q (a :: w) =
      (step q a).1 ++ oneWayOutput step final (step q a).2 w := rfl

@[simp]
theorem oneWayTime_nil (q : State) : oneWayTime step final q [] = max 1 (final q).length := rfl

@[simp]
theorem oneWayTime_cons (q : State) (a : Symbol) (w : List Symbol) :
    oneWayTime step final q (a :: w) =
      max 1 (step q a).1.length + oneWayTime step final (step q a).2 w := rfl

/-- A one-way machine takes at most one step per input and output symbol plus one. -/
theorem oneWayTime_le (q : State) (w : List Symbol) :
    oneWayTime step final q w ≤ w.length + (oneWayOutput step final q w).length + 1 := by
  induction w generalizing q with
  | nil => simp only [oneWayTime_nil, oneWayOutput_nil, List.length_nil]; lia
  | cons a w ih =>
    have := ih (step q a).2
    simp only [oneWayTime_cons, oneWayOutput_cons, List.length_cons, List.length_append]
    lia

end Equations

/-- The action of a one-way machine that is emitting `out` and has already emitted its first `i`
symbols: it emits the next symbol, and with the last one it moves by `move` and enters `next`. -/
def oneWayAction {m : ℕ} (out : List Symbol) (i : Fin (m + 1)) (q : State) (move : SignType)
    (next : Option State) : Action 0 Symbol (State × Fin (m + 1)) :=
  if i.val + 1 < out.length then
    ⟨0, Fin.elim0, out[i.val]?, some (q, ⟨(i.val + 1) % (m + 1), Nat.mod_lt _ (by lia)⟩)⟩
  else ⟨move, Fin.elim0, out[i.val]?, next.map (·, 0)⟩

variable {input : List Symbol}

/-- A machine that follows `oneWayAction` for the output word `out` on the current input cell
emits the rest of `out`, and then moves and changes its state as given. -/
private lemma runFrom_emit {m : ℕ} {tm : MultiTapeTM 0 Symbol (State × Fin (m + 1))}
    {out : List Symbol} {q : State} {move : SignType} {next : Option State} {sym : Option Symbol}
    (htr : ∀ j ws, tm.tr (q, j) sym ws = oneWayAction out j q move next) (hlen : out.length ≤ m)
    (i : Fin (m + 1)) (c : Cfg 0 Symbol (State × Fin (m + 1)) input)
    (hq : c.state = some (q, i)) (hsym : c.inputSymbol = sym) :
    (tm.runFrom c (max 1 (out.length - i))).state = next.map (·, 0) ∧
      (tm.runFrom c (max 1 (out.length - i))).inputPos = moveInputPos c.inputPos move ∧
      (tm.runFrom c (max 1 (out.length - i))).output = c.output ++ out.drop i := by
  have hstep : tm.step c = (oneWayAction out i q move next).apply c := by
    rw [step_of_state hq, hsym, htr]
  by_cases h : i.val + 1 < out.length
  · have hmod : (i.val + 1) % (m + 1) = i.val + 1 := Nat.mod_eq_of_lt (by lia)
    obtain ⟨hs, hp, ho⟩ := runFrom_emit htr hlen ⟨(i.val + 1) % (m + 1), Nat.mod_lt _ (by lia)⟩
      (tm.step c) (by rw [hstep]; simp [oneWayAction, h, Action.apply])
      (by rw [hstep, ← hsym]; simp [oneWayAction, h, Action.apply, Cfg.inputSymbol])
    have hn : max 1 (out.length - i.val) = 1 + max 1 (out.length - (i.val + 1)) := by lia
    simp only [hmod] at hs hp ho
    rw [hn, runFrom_add, runFrom_one]
    refine ⟨hs, ?_, ?_⟩
    · rw [hp, hstep]; simp [oneWayAction, h, Action.apply]
    · rw [ho, hstep]
      simp [oneWayAction, h, Action.apply, show i.val < out.length by lia]
  · have hn : max 1 (out.length - i.val) = 1 := by lia
    rw [hn, runFrom_one, hstep]
    refine ⟨by simp [oneWayAction, h, Action.apply], by simp [oneWayAction, h, Action.apply], ?_⟩
    simp only [oneWayAction, h, Action.apply, ↓reduceIte]
    rcases Nat.lt_or_ge i.val out.length with hi | hi
    · rw [List.getElem?_eq_getElem hi, List.drop_eq_getElem_cons hi,
        List.drop_of_length_le (by lia)]
      rfl
    · simp [List.getElem?_eq_none hi, List.drop_of_length_le hi]
termination_by out.length - i.val
decreasing_by lia

/-- The one-way machine with start state `q₀`: on an input symbol it emits the output word of
`step`, moves right and enters the successor state, and on the blank after the input it emits the
output word of `final` and halts. The second component of its state counts the symbols already
emitted of the current output word, so `m` has to bound the length of these words. -/
def oneWay (m : ℕ) (q₀ : State) (step : State → Symbol → List Symbol × State)
    (final : State → List Symbol) : MultiTapeTM 0 Symbol (State × Fin (m + 1)) :=
  ofTr (q₀, 0) fun s inp _ =>
    inp.elim (oneWayAction (final s.1) s.2 s.1 0 none) fun a =>
      oneWayAction (step s.1 a).1 s.2 s.1 1 (some (step s.1 a).2)

/-- For finite state and symbol types, the words that a one-way machine emits at a time have
bounded length. -/
theorem exists_oneWay_length_le [Finite Symbol] [Finite State]
    (step : State → Symbol → List Symbol × State) (final : State → List Symbol) :
    ∃ m, (∀ q a, (step q a).1.length ≤ m) ∧ ∀ q, (final q).length ≤ m := by
  have := Fintype.ofFinite Symbol
  have := Fintype.ofFinite State
  exact ⟨max (Finset.univ.sup fun p : State × Symbol => (step p.1 p.2).1.length)
      (Finset.univ.sup fun q => (final q).length),
    fun q a => le_max_of_le_left
      (Finset.le_sup (f := fun p : State × Symbol => (step p.1 p.2).1.length)
        (Finset.mem_univ (q, a))),
    fun q => le_max_of_le_right
      (Finset.le_sup (f := fun q => (final q).length) (Finset.mem_univ q))⟩

variable {m : ℕ} {q₀ : State} {step : State → Symbol → List Symbol × State}
  {final : State → List Symbol}

/-- Started in state `q` with the input head on the first symbol of a suffix `rest` of the input,
a one-way machine halts after `oneWayTime step final q rest` steps, and has then emitted
`oneWayOutput step final q rest`. -/
private lemma runFrom_oneWay (hstep : ∀ q a, (step q a).1.length ≤ m)
    (hfinal : ∀ q, (final q).length ≤ m) (rest pre : List Symbol) (q : State)
    (c : Cfg 0 Symbol (State × Fin (m + 1)) input)
    (h : input = pre ++ rest) (hq : c.state = some (q, 0))
    (hp : c.inputPos.val = pre.length + 1) :
    ((oneWay m q₀ step final).runFrom c (oneWayTime step final q rest)).state = none ∧
      ((oneWay m q₀ step final).runFrom c (oneWayTime step final q rest)).output =
        c.output ++ oneWayOutput step final q rest := by
  induction rest generalizing pre q c with
  | nil =>
    have hsym : c.inputSymbol = none :=
      inputSymbol_eq_none_of_boundary (.inr (by simp [h, hp]))
    obtain ⟨hs, -, ho⟩ := runFrom_emit (tm := oneWay m q₀ step final) (out := final q) (q := q)
      (move := 0) (next := none) (fun j ws => by simp [oneWay, tr_ofTr]) (hfinal q) 0 c hq hsym
    exact ⟨by simpa using hs, by simpa using ho⟩
  | cons a w ih =>
    subst h
    have hsym : c.inputSymbol = some a := by
      simpa using inputSymbolInner (cfg := c) pre.length (by lia) (by simp)
    obtain ⟨hs, hpos, ho⟩ := runFrom_emit (tm := oneWay m q₀ step final) (out := (step q a).1)
      (q := q) (move := 1) (next := some (step q a).2) (fun j ws => by simp [oneWay, tr_ofTr])
      (hstep q a) 0 c hq hsym
    simp only [Fin.val_zero, tsub_zero, List.drop_zero, Option.map_some] at hs hpos ho
    obtain ⟨hs', ho'⟩ := ih (pre ++ [a]) (step q a).2 _ (by simp) (by simpa using hs) (by
      rw [hpos, show (1 : SignType) = .pos from rfl,
        moveInputPos_pos_of_ne_right _ (by simp; lia)]
      simp [hp])
    rw [oneWayTime_cons, runFrom_add]
    exact ⟨hs', by rw [ho', ho]; simp⟩

/-- A one-way machine outputs `oneWayOutput` of its input, in `oneWayTime` steps and in zero
space, provided that `m` bounds the length of the words it emits at a time. -/
theorem computesInTimeAndSpace_oneWay (q₀ : State) {step : State → Symbol → List Symbol × State}
    {final : State → List Symbol} (hstep : ∀ q a, (step q a).1.length ≤ m)
    (hfinal : ∀ q, (final q).length ≤ m) (input : List Symbol) :
    (oneWay m q₀ step final).ComputesInTimeAndSpace input (oneWayOutput step final q₀ input)
      (oneWayTime step final q₀ input) 0 := by
  obtain ⟨hs, ho⟩ := runFrom_oneWay (q₀ := q₀) hstep hfinal input [] q₀
    ((oneWay m q₀ step final).initCfg input) rfl rfl rfl
  exact ⟨⟨_, hs, by simpa using ho⟩, runsInTime_of_halted hs, by simp⟩

end Turing.MultiTapeTM
