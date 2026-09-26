/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.TransformsTapes

/-!
# A machine that clears a work tape

A two-state machine that erases the word on one designated work tape `i` and returns the head to
the start; every other tape is never written and its head never moves. In its first state the
machine scans right over the word until it reads the first blank, one cell past the word. In its
second state it sweeps back left, blanking every cell it reads. On the way down the cells to the
left of the head still hold their symbols, so the first blank read while sweeping is the cell at
position `-1`; the halting transition moves the head right, back to position `0`.

On a word of length `L` the run takes `2 * L + 2` steps and visits the cells `-1, …, L` of tape
`i` and only the cell `0` of every other tape, so the machine runs in time `3 * (L + 1)` and space
`L + 1 + k`.

## Main results

* `Turing.MultiTapeTM.exists_transformsTapes_clear`: the machine that replaces the word on tape
  `i` by the empty word and leaves every other tape unchanged.
-/

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol : Type*} {input : List Symbol}

/-- The clearing machine for tape `i`. In state `false` it scans right over the word on tape `i`;
on the first blank it turns around into state `true`. In state `true` it sweeps left, blanking
every cell it reads; on the first blank — the cell at position `-1` — it moves right and halts.
No other tape is ever written or moved, and the input head never moves. -/
def clearTape (i : Fin k) : MultiTapeTM k Symbol Bool where
  q₀ := false
  tr q _ work :=
    match q, work i with
    | false, some _ =>
        { inputTape := 0, workTapes := fun l => (none, if l = i then 1 else 0),
          output := none, state := some false }
    | false, none =>
        { inputTape := 0, workTapes := fun l => (none, if l = i then -1 else 0),
          output := none, state := some true }
    | true, some _ =>
        { inputTape := 0,
          workTapes := fun l => (if l = i then some none else none, if l = i then -1 else 0),
          output := none, state := some true }
    | true, none =>
        { inputTape := 0, workTapes := fun l => (none, if l = i then 1 else 0),
          output := none, state := none }

namespace Clear

variable {i : Fin k} {w : List Symbol} {ws : Fin k → List Symbol} {out : List Symbol}
  {T : ℤ → Option Symbol} {p : ℤ}

/-- A configuration of the clearing machine: state `q`, tape `i` holding `T` with its head at `p`,
every other tape `l` holding the word `ws l` with its head at `0`, the input head at the start and
output `out`. -/
def cfg (input : List Symbol) (i : Fin k) (q : Option Bool) (T : ℤ → Option Symbol) (p : ℤ)
    (ws : Fin k → List Symbol) (out : List Symbol) : Cfg k Symbol Bool input :=
  ⟨q, 1, fun l => if l = i then T else tapeOfList (ws l), fun l => if l = i then p else 0, out⟩

/-- Configurations of the shape `cfg` are equal as soon as the tape-`i` contents and head position
agree. -/
lemma cfg_congr {q : Option Bool} {T T' : ℤ → Option Symbol} {p p' : ℤ} (hT : T = T')
    (hp : p = p') : cfg input i q T p ws out = cfg input i q T' p' ws out := by
  rw [hT, hp]

/-- The head of tape `i` is at `p`. -/
lemma cfg_workTapePos_self (q : Option Bool) :
    (cfg input i q T p ws out).workTapePos i = p := by
  simp [cfg]

/-- The head of every other tape is at `0`. -/
lemma cfg_workTapePos_ne {l : Fin k} (h : l ≠ i) (q : Option Bool) :
    (cfg input i q T p ws out).workTapePos l = 0 := by
  simp [cfg, h]

/-- A word configuration is a `cfg` whose tape `i` holds the word `ws i`. -/
lemma wordsCfg_eq_cfg (q : Option Bool) (hws : ws i = w) :
    wordsCfg input q ws out = cfg input i q (tapeOfList w) 0 ws out := by
  apply Cfg.ext <;> simp [wordsCfg, cfg, ← hws, funext_iff]

/-- The halting `cfg` with a blank tape `i` is the word configuration in which the word on tape
`i` has been replaced by the empty word. -/
lemma cfg_halt_eq_wordsCfg :
    cfg input i none (fun _ => none) 0 ws out =
      wordsCfg input none (Function.update ws i []) out := by
  refine Cfg.ext rfl rfl (funext fun l => ?_) (by simp [cfg, wordsCfg]) rfl
  by_cases h : l = i <;> simp [cfg, wordsCfg, h]

/-- Scanning right in state `false`: over a symbol the head moves right and nothing is written. -/
lemma step_scan {s : Symbol} (hT : T p = some s) :
    (clearTape i).step (cfg input i (some false) T p ws out) =
      cfg input i (some false) T (p + 1) ws out := by
  simp only [step, cfg, clearTape, Cfg.workTapeSymbols, ↓reduceIte, hT]
  refine Cfg.ext rfl (by simp) (funext fun l => ?_) (funext fun l => ?_) (by simp)
  all_goals by_cases h : l = i <;> simp [h]

/-- Turning around: on the blank one cell past the word, state `false` moves left and enters
state `true`. -/
lemma step_turn (hT : T p = none) :
    (clearTape i).step (cfg input i (some false) T p ws out) =
      cfg input i (some true) T (p - 1) ws out := by
  simp only [step, cfg, clearTape, Cfg.workTapeSymbols, ↓reduceIte, hT]
  refine Cfg.ext rfl (by simp) (funext fun l => ?_) (funext fun l => ?_) (by simp)
  all_goals by_cases h : l = i <;> simp [h, sub_eq_add_neg]

/-- Sweeping left in state `true`: over a symbol the cell is blanked and the head moves left. -/
lemma step_sweep {s : Symbol} (hT : T p = some s) :
    (clearTape i).step (cfg input i (some true) T p ws out) =
      cfg input i (some true) (Function.update T p none) (p - 1) ws out := by
  simp only [step, cfg, clearTape, Cfg.workTapeSymbols, ↓reduceIte, hT]
  refine Cfg.ext rfl (by simp) (funext fun l => ?_) (funext fun l => ?_) (by simp)
  all_goals by_cases h : l = i <;> simp [h, sub_eq_add_neg]

/-- Halting: on the blank at position `-1`, state `true` moves right and halts. -/
lemma step_halt (hT : T p = none) :
    (clearTape i).step (cfg input i (some true) T p ws out) =
      cfg input i none T (p + 1) ws out := by
  simp only [step, cfg, clearTape, Cfg.workTapeSymbols, ↓reduceIte, hT]
  refine Cfg.ext rfl (by simp) (funext fun l => ?_) (funext fun l => ?_) (by simp)
  all_goals by_cases h : l = i <;> simp [h]

/-- Blanking the cell just past the end of a word shortens the word by one symbol. -/
lemma update_tapeOfList_eq_tapeOfList_take (w : List Symbol) (p : ℕ) :
    Function.update (tapeOfList (w.take (p + 1))) (p : ℤ) none = tapeOfList (w.take p) := by
  funext z
  rcases eq_or_ne z (p : ℤ) with rfl | hz
  · rw [Function.update_self, tapeOfList_ofNat]
    exact (List.getElem?_eq_none (by simp)).symm
  · rw [Function.update_of_ne hz]
    cases z with
    | negSucc n => simp
    | ofNat n =>
      change (w.take (p + 1))[n]? = (w.take p)[n]?
      have hn : n ≠ p := by rintro rfl; exact hz rfl
      rcases Nat.lt_or_ge n p with h | h
      · rw [List.getElem?_take_of_lt (by omega), List.getElem?_take_of_lt h]
      · have h' : p < n := by omega
        rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]

/-- After `n ≤ w.length` steps the machine is still scanning: the tape holds `w` untouched and
the head is at position `n`. -/
lemma runFrom_scan (w : List Symbol) (n : ℕ) (hn : n ≤ w.length) :
    (clearTape i).runFrom (cfg input i (some false) (tapeOfList w) 0 ws out) n =
      cfg input i (some false) (tapeOfList w) n ws out := by
  induction n with
  | zero => simp [runFrom]
  | succ n ih =>
    have hsym : tapeOfList w (n : ℤ) = some (w[n]'(by omega)) := by
      rw [tapeOfList_ofNat]
      exact List.getElem?_eq_getElem (by omega)
    rw [runFrom, Function.iterate_succ_apply', ← runFrom, ih (by omega), step_scan hsym]
    exact cfg_congr rfl (by omega)

/-- After `w.length + 1 + m` steps, for `m ≤ w.length`, the machine is sweeping: the last `m`
cells of the word have been blanked and the head is at position `w.length - 1 - m`. -/
lemma runFrom_sweep (w : List Symbol) (m : ℕ) (hm : m ≤ w.length) :
    (clearTape i).runFrom (cfg input i (some false) (tapeOfList w) 0 ws out)
        (w.length + 1 + m) =
      cfg input i (some true) (tapeOfList (w.take (w.length - m)))
        ((w.length : ℤ) - 1 - m) ws out := by
  induction m with
  | zero =>
    have hsym : tapeOfList w ((w.length : ℕ) : ℤ) = none := by simp
    rw [Nat.add_zero, runFrom, Function.iterate_succ_apply', ← runFrom,
      runFrom_scan w w.length le_rfl, step_turn hsym]
    exact cfg_congr (by simp) (by omega)
  | succ m ih =>
    have hidx : (w.length : ℤ) - 1 - m = ((w.length - 1 - m : ℕ) : ℤ) := by omega
    have hsym : tapeOfList (w.take (w.length - m)) ((w.length - 1 - m : ℕ) : ℤ) =
        some (w[w.length - 1 - m]'(by omega)) := by
      rw [tapeOfList_ofNat, List.getElem?_take_of_lt (by omega)]
      exact List.getElem?_eq_getElem (by omega)
    rw [show w.length + 1 + (m + 1) = w.length + 1 + m + 1 from rfl,
      runFrom, Function.iterate_succ_apply', ← runFrom,
      ih (by omega), hidx, step_sweep hsym]
    refine cfg_congr ?_ (by omega)
    rw [show w.length - m = (w.length - 1 - m) + 1 from by omega,
      update_tapeOfList_eq_tapeOfList_take,
      show w.length - 1 - m = w.length - (m + 1) from by omega]

/-- The complete run: after `2 * w.length + 2` steps the machine has halted with tape `i` blank
and its head back at `0`. -/
lemma runFrom_full (w : List Symbol) :
    (clearTape i).runFrom (cfg input i (some false) (tapeOfList w) 0 ws out)
        (2 * w.length + 2) =
      cfg input i none (fun _ => none) 0 ws out := by
  rw [show 2 * w.length + 2 = w.length + 1 + w.length + 1 from by omega,
    runFrom, Function.iterate_succ_apply', ← runFrom,
    runFrom_sweep w w.length le_rfl, step_halt (by simp)]
  exact cfg_congr (by simp) (by omega)

/-- At every step of the run the configuration has the shape `cfg`, with the head of tape `i`
between the positions `-1` and `w.length`. -/
lemma runFrom_shape (w : List Symbol) (t : ℕ) (ht : t ≤ 2 * w.length + 2) :
    ∃ (q : Option Bool) (T : ℤ → Option Symbol) (p : ℤ), -1 ≤ p ∧ p ≤ w.length ∧
      (clearTape i).runFrom (cfg input i (some false) (tapeOfList w) 0 ws out) t =
        cfg input i q T p ws out := by
  by_cases h : t ≤ w.length
  · exact ⟨some false, tapeOfList w, t, by omega, by omega, runFrom_scan w t h⟩
  by_cases h2 : t ≤ 2 * w.length + 1
  · obtain ⟨m, hm, rfl⟩ : ∃ m, m ≤ w.length ∧ t = w.length + 1 + m :=
      ⟨t - (w.length + 1), by omega, by omega⟩
    exact ⟨some true, tapeOfList (w.take (w.length - m)), (w.length : ℤ) - 1 - m, by omega,
      by omega, runFrom_sweep w m hm⟩
  rw [show t = 2 * w.length + 2 from by omega]
  exact ⟨none, fun _ => none, 0, by omega, by omega, runFrom_full w⟩

/-- The run visits the cells `-1, …, w.length` of tape `i` and only the cell `0` of every other
tape, so it uses at most `w.length + 1 + k` cells in total. -/
lemma spaceUsed_le (w : List Symbol) :
    (clearTape i).spaceUsed (cfg input i (some false) (tapeOfList w) 0 ws out)
        (2 * w.length + 2) ≤ w.length + 1 + k := by
  set c₀ := cfg input i (some false) (tapeOfList w) 0 ws out
  set τ := 2 * w.length + 2
  have hi : (clearTape i).spaceUsedByTape c₀ τ i ≤ w.length + 2 := by
    have hsub : (clearTape i).visitedByTapeHead c₀ τ i ⊆
        Finset.Icc (-1 : ℤ) (w.length : ℤ) := by
      intro z hz
      obtain ⟨t, ht, rfl⟩ := mem_visitedByTapeHead.mp hz
      obtain ⟨q, T, p, hp₁, hp₂, heq⟩ := runFrom_shape w t (by omega)
      rw [heq, cfg_workTapePos_self]
      exact Finset.mem_Icc.mpr ⟨hp₁, hp₂⟩
    refine (Finset.card_le_card hsub).trans_eq ?_
    rw [Int.card_Icc]
    omega
  have hne : ∀ l, l ≠ i → (clearTape i).spaceUsedByTape c₀ τ l ≤ 1 := by
    intro l hl
    have hsub : (clearTape i).visitedByTapeHead c₀ τ l ⊆ {0} := by
      intro z hz
      obtain ⟨t, ht, rfl⟩ := mem_visitedByTapeHead.mp hz
      obtain ⟨q, T, p, _, _, heq⟩ := runFrom_shape w t (by omega)
      rw [heq, cfg_workTapePos_ne hl]
      simp
    exact (Finset.card_le_card hsub).trans_eq (Finset.card_singleton 0)
  have hsplit : (clearTape i).spaceUsed c₀ τ = (clearTape i).spaceUsedByTape c₀ τ i +
      ∑ l ∈ Finset.univ.erase i, (clearTape i).spaceUsedByTape c₀ τ l :=
    (Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)).symm
  have hsum : ∑ l ∈ Finset.univ.erase i, (clearTape i).spaceUsedByTape c₀ τ l ≤ k - 1 := by
    have := Finset.sum_le_card_nsmul (Finset.univ.erase i)
      (fun l => (clearTape i).spaceUsedByTape c₀ τ l) 1
      (fun l hl => hne l (Finset.mem_erase.mp hl).1)
    simpa [Finset.card_erase_of_mem] using this
  have hk : 0 < k := i.pos
  omega

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
  refine ⟨3, Bool, inferInstance, clearTape i, fun w input ws out hws => ?_⟩
  have hstart : wordsCfg input (some (clearTape i : MultiTapeTM k Symbol Bool).q₀) ws out =
      Clear.cfg input i (some false) (tapeOfList w) 0 ws out :=
    Clear.wordsCfg_eq_cfg _ hws
  refine ⟨Function.update ws i [], ?_, rfl, ?_⟩
  · have hrun := Clear.runFrom_full (input := input) (i := i) (ws := ws) (out := out) w
    exact (clearTape i).runFrom_eq_of_halt (τ := 2 * w.length + 2) _ (by omega)
      (by rw [hstart, hrun]; rfl) |>.trans
      (by rw [hstart, hrun, Clear.cfg_halt_eq_wordsCfg])
  · rw [hstart, (clearTape i).spaceUsed_eq_of_halt (τ := 2 * w.length + 2) _ (by omega)
      (by rw [Clear.runFrom_full]; rfl)]
    exact Clear.spaceUsed_le w

end Turing.MultiTapeTM
