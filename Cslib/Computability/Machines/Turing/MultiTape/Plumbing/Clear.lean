/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.SingleTapeAction
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.TransformsTapes

/-!
# A machine that clears a work tape

A two-state machine that erases the word on one designated work tape `i` and returns the head to
the start; every other tape is never written and its head never moves. In state `scan` the machine
moves right over the word until it reads the first blank, one cell past the word. In state `sweep`
it moves back left, blanking every cell it reads. On the way down the cells to the
left of the head still hold their symbols, so the first blank read while sweeping is the cell at
position `-1`; the halting transition moves the head right, back to position `0`.

The machine is only correct when started in the normal form used by `TransformsTapes`
(`wordsCfg`): every head, including the input head, is at the start, and every work tape holds a
word in cells `0, 1, …`. The correctness proof makes no claim about runs from other
configurations.

On a word of length `l` the run takes `2 * l + 2` steps and visits the cells `-1, …, l` of tape
`i` and only the cell `0` of every other tape, so the machine runs in time `3 * (l + 1)` and space
`l + 1 + k`.

## Main results

* `Turing.MultiTapeTM.exists_transformsTapes_clear`: the machine that replaces the word on tape
  `i` by the empty word and leaves every other tape unchanged.
-/

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol : Type*} {input : List Symbol}

/-- The control states of the clearing machine: `scan` moves right to the end of the word, `sweep`
moves back left and blanks the word. -/
inductive ClearState : Type
  | scan
  | sweep
  deriving DecidableEq

instance : Fintype ClearState := ⟨{.scan, .sweep}, fun q => by cases q <;> simp⟩

/-- The clearing machine for tape `i`. In state `scan` it moves right over the word on tape `i`;
on the first blank it turns around into state `sweep`. In state `sweep` it moves left, blanking
every cell it reads; on the first blank — the cell at position `-1` — it moves right and halts.
No other tape is ever written or moved, and the input head never moves. -/
def clearTape (i : Fin k) : MultiTapeTM k Symbol ClearState where
  q₀ := .scan
  tr q _ work :=
    match q, work i with
    | .scan, some _ => .onTape i none 1 (some .scan)
    | .scan, none => .onTape i none (-1) (some .sweep)
    | .sweep, some _ => .onTape i (some none) (-1) (some .sweep)
    | .sweep, none => .onTape i none 1 none

namespace Clear

variable {i : Fin k} {w : List Symbol} {ws : Fin k → List Symbol} {out : List Symbol}
  {tape : ℤ → Option Symbol} {p : ℤ}

/-- A configuration of the clearing machine: state `q`, tape `i` holding `tape` with its head at
`p`, every other tape `l` holding the word `ws l` with its head at `0`, the input head at the start
and output `out`. -/
def cfg (input : List Symbol) (i : Fin k) (q : Option ClearState) (tape : ℤ → Option Symbol) (p : ℤ)
    (ws : Fin k → List Symbol) (out : List Symbol) : Cfg k Symbol ClearState input :=
  ⟨q, 1, fun l => if l = i then tape else tapeOfList (ws l), fun l => if l = i then p else 0, out⟩

/-- A word configuration is a `cfg` whose tape `i` holds the word `ws i`. -/
lemma wordsCfg_eq_cfg (q : Option ClearState) (hws : ws i = w) :
    wordsCfg input q ws out = cfg input i q (tapeOfList w) 0 ws out := by
  apply Cfg.ext <;> simp [cfg, ← hws, funext_iff, ite_apply]; grind

/-- The halting `cfg` with a blank tape `i` is the word configuration in which the word on tape
`i` has been replaced by the empty word. -/
lemma cfg_halt_eq_wordsCfg :
    cfg input i none (fun _ => none) 0 ws out =
      wordsCfg input none (Function.update ws i []) out := by
  apply Cfg.ext <;> simp [cfg, funext_iff, Function.update_apply, apply_ite]

/-- In state `scan`, over a symbol the head moves right and nothing is written. -/
lemma step_scan (htape : tape p ≠ none) :
    (clearTape i).step (cfg input i (some .scan) tape p ws out) =
      cfg input i (some .scan) tape (p + 1) ws out := by
  obtain ⟨s, htape⟩ := Option.ne_none_iff_exists'.mp htape
  refine Cfg.ext ?_ ?_ (funext fun l => ?_) (funext fun l => ?_) ?_ <;> try by_cases h : l = i
  all_goals simp_all [step, cfg, clearTape, Cfg.workTapeSymbols]

/-- In state `scan`, on the blank one cell past the word, the head moves left and the machine
enters state `sweep`. -/
lemma step_turn (htape : tape p = none) :
    (clearTape i).step (cfg input i (some .scan) tape p ws out) =
      cfg input i (some .sweep) tape (p - 1) ws out := by
  refine Cfg.ext ?_ ?_ (funext fun l => ?_) (funext fun l => ?_) ?_ <;> try by_cases h : l = i
  all_goals simp_all [step, cfg, clearTape, Cfg.workTapeSymbols, sub_eq_add_neg]

/-- In state `sweep`, over a symbol the cell is blanked and the head moves left. -/
lemma step_sweep (htape : tape p ≠ none) :
    (clearTape i).step (cfg input i (some .sweep) tape p ws out) =
      cfg input i (some .sweep) (Function.update tape p none) (p - 1) ws out := by
  obtain ⟨s, htape⟩ := Option.ne_none_iff_exists'.mp htape
  refine Cfg.ext ?_ ?_ (funext fun l => ?_) (funext fun l => ?_) ?_ <;> try by_cases h : l = i
  all_goals simp_all [step, cfg, clearTape, Cfg.workTapeSymbols, sub_eq_add_neg]

/-- In state `sweep`, on the blank at position `-1`, the head moves right and the machine
halts. -/
lemma step_halt (htape : tape p = none) :
    (clearTape i).step (cfg input i (some .sweep) tape p ws out) =
      cfg input i none tape (p + 1) ws out := by
  refine Cfg.ext ?_ ?_ (funext fun l => ?_) (funext fun l => ?_) ?_ <;> try by_cases h : l = i
  all_goals simp_all [step, cfg, clearTape, Cfg.workTapeSymbols]

/-- After `n ≤ w.length` steps the machine is still scanning: the tape holds `w` untouched and
the head is at position `n`. -/
lemma runFrom_scan (n : ℕ) (hn : n ≤ w.length) :
    (clearTape i).runFrom (cfg input i (some .scan) (tapeOfList w) 0 ws out) n =
      cfg input i (some .scan) (tapeOfList w) n ws out := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [runFrom, Function.iterate_succ_apply', ← runFrom, ih (by omega),
      step_scan (by simp; omega)]
    congr 1

/-- After `w.length + 1 + m` steps, for `m ≤ w.length`, the machine is sweeping: the last `m`
cells of the word have been blanked and the head is just left of the remaining word. -/
lemma runFrom_sweep (m : ℕ) (hm : m ≤ w.length) :
    (clearTape i).runFrom (cfg input i (some .scan) (tapeOfList w) 0 ws out)
        (w.length + 1 + m) =
      cfg input i (some .sweep) (tapeOfList (w.take (w.length - m)))
        ((w.length - m : ℕ) - 1) ws out := by
  induction m with
  | zero =>
    rw [runFrom, Function.iterate_succ_apply', ← runFrom, runFrom_scan _ le_rfl,
      step_turn (by simp)]
    congr 1
    simp
  | succ m ih =>
    obtain ⟨n, hn⟩ : ∃ n, w.length - m = n + 1 := ⟨w.length - m - 1, by omega⟩
    rw [← add_assoc, runFrom, Function.iterate_succ_apply', ← runFrom, ih (by omega), hn,
      step_sweep (by simp; omega)]
    rw [show w.length - (m + 1) = n by omega]
    congr 1
    · simpa using update_tapeOfList_take_succ w n
    · omega

/-- The complete run: after `2 * w.length + 2` steps the machine has halted with tape `i` blank
and its head back at `0`. -/
lemma runFrom_full :
    (clearTape i).runFrom (cfg input i (some .scan) (tapeOfList w) 0 ws out)
        (2 * w.length + 2) =
      cfg input i none (fun _ => none) 0 ws out := by
  rw [show 2 * w.length + 2 = w.length + 1 + w.length + 1 by omega, runFrom,
    Function.iterate_succ_apply', ← runFrom, runFrom_sweep _ le_rfl, step_halt (by simp)]
  congr 1 <;> simp

/-- At every step of the run the configuration has the shape `cfg`, with the head of tape `i`
between the positions `-1` and `w.length`. -/
lemma runFrom_shape (w : List Symbol) (t : ℕ) (ht : t ≤ 2 * w.length + 2) :
    ∃ (q : Option ClearState) (tape : ℤ → Option Symbol) (p : ℤ), -1 ≤ p ∧ p ≤ w.length ∧
      (clearTape i).runFrom (cfg input i (some .scan) (tapeOfList w) 0 ws out) t =
        cfg input i q tape p ws out := by
  by_cases h : t ≤ w.length
  · exact ⟨_, _, t, by omega, by omega, runFrom_scan t h⟩
  by_cases h2 : t ≤ 2 * w.length + 1
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le (show w.length + 1 ≤ t by omega)
    exact ⟨_, _, _, by omega, by omega, runFrom_sweep m (by omega)⟩
  obtain rfl : t = 2 * w.length + 2 := by omega
  exact ⟨_, _, 0, by omega, by omega, runFrom_full⟩

/-- The run visits the cells `-1, …, w.length` of tape `i` and only the cell `0` of every other
tape, so it uses at most `w.length + 1 + k` cells in total. -/
lemma spaceUsed_le :
    (clearTape i).spaceUsed (cfg input i (some .scan) (tapeOfList w) 0 ws out)
        (2 * w.length + 2) ≤ w.length + 1 + k := by
  calc _ ≤ ∑ l : Fin k, ((if l = i then w.length + 1 else 0) + 1) :=
        Finset.sum_le_sum fun l _ => ?_
    _ = _ := by simp [Finset.sum_add_distrib]
  have hsub : (clearTape i).visitedByTapeHead
      (cfg input i (some .scan) (tapeOfList w) 0 ws out) (2 * w.length + 2) l ⊆
        if l = i then Finset.Icc (-1) (w.length : ℤ) else {0} := by
    intro z hz
    obtain ⟨t, ht, rfl⟩ := mem_visitedByTapeHead.mp hz
    obtain ⟨q, tape, p, hp₁, hp₂, heq⟩ := runFrom_shape w t (by omega)
    rw [heq]
    split_ifs with h <;> simp [cfg, h, hp₁, hp₂]
  refine (Finset.card_le_card hsub).trans ?_
  split_ifs <;> simp

end Clear

/-- **The machine that clears a work tape.** One machine per tape index `i` (uniform over the
words `w`): it replaces the word on tape `i` by the empty word and leaves every other tape
unchanged, in at most `3 * (w.length + 1)` steps and `w.length + 1 + k` cells. -/
public theorem exists_transformsTapes_clear {Symbol : Type*} {k : ℕ} (i : Fin k) :
    ∃ (c : ℕ) (State : Type) (_ : Finite State) (tm : MultiTapeTM k Symbol State),
      ∀ w : List Symbol,
        TransformsTapes tm (fun _ ws => ws i = w)
          (fun _ ws ws' => ws' = Function.update ws i [])
          (c * (w.length + 1)) (w.length + 1 + k) := by
  refine ⟨3, ClearState, inferInstance, clearTape i, fun w input ws out hws => ?_⟩
  rw [show some (clearTape i).q₀ = some .scan from rfl, Clear.wordsCfg_eq_cfg _ hws]
  have hhalt : ((clearTape i).runFrom (Clear.cfg input i (some .scan) (tapeOfList w) 0 ws out)
      (2 * w.length + 2)).state = none := by
    rw [Clear.runFrom_full]; rfl
  refine ⟨_, ?_, rfl, ?_⟩
  · rw [runFrom_eq_of_halt _ _ (by omega) hhalt, Clear.runFrom_full, Clear.cfg_halt_eq_wordsCfg]
  · rw [(clearTape i).spaceUsed_eq_of_halt _ (by omega) hhalt]
    exact Clear.spaceUsed_le

end Turing.MultiTapeTM
