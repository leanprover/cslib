/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Mathlib.Basic.Finite.Sum
public import Mathlib.Tactic.FinCases
public import Cslib.Computability.Machines.Turing.MultiTape.Combinators.Id
public import Cslib.Computability.Machines.Turing.MultiTape.Combinators.TidyZeroSpace
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.ClearWork
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.OnWords
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.RepeatUntilBlank

/-!
# Iterating a function while its result is non-empty

`tm.iterateWhile mark` applies `tm` to its input, then to the result, and so on, as long as the
result is non-empty. As soon as `tm` produces the empty word, it outputs the last non-empty
result. The computation need not terminate.

The machine keeps the current word on one work tape and the next one on another. A round copies
the next word to the current tape with a tidy identity machine, `Turing.MultiTapeTM.tidyCopy`, and
computes the new next word from it with `tm`. Rounds are repeated by
`Turing.MultiTapeTM.repeatUntilBlank` until the next word is empty.

## Main definitions

* `Turing.MultiTapeTM.tidyCopy`: the identity as a tidy machine without work tapes.
* `Turing.MultiTapeTM.iterateWhile`: the iterating machine.

## Main results

* `Turing.MultiTapeTM.computesTidily_iterateWhile`: if `tm` computes `w (n + 1)` from `w n` tidily
  for every `n ≤ r`, and `w (n + 1)` is empty exactly for `n = r`, then `tm.iterateWhile mark`
  computes `w r` from `w 0` tidily.
* `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.iterateWhile`: if `f` is tidily computable,
  so is `a ↦ f^[r a] a`, where `r a` is the number of applications of `f` after which the
  encoding of the next value is empty.
* `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpaceOfLength.iterateWhile`: the same, with bounds
  on the number of rounds and on the lengths of all intermediate values in terms of the length
  of the input.
-/

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State : Type*}

/-! ### The identity as a tidy machine -/

/-- The identity as a tidy machine without work tapes: copy the input to the output, then move the
input head back to the start. -/
public noncomputable def tidyCopy (Symbol : Type*) : MultiTapeTM 0 Symbol (Unit ⊕ RewindState) :=
  copy.seq (rewindInput Symbol)

/-- `tidyCopy` computes the identity tidily, in time linear in the length of the word. -/
public theorem computesTidily_tidyCopy (w : List Symbol) :
    (tidyCopy Symbol).ComputesTidilyInTimeAndSpace w w (2 * w.length + 4) 0 :=
  TransformsTapes.mono (Copy.computesInTimeAndSpace w).computesTidily_seq_rewindInput (by omega)
    le_rfl

/-! ### The tapes of the iterating machine -/

namespace IterateWhile

variable (k) in
/-- The tape holding the current word: the input tape of `Turing.MultiTapeTM.onWords`. -/
abbrev curTape : Fin (k + 1 + 2) := Fin.natAdd (k + 1) 0

variable (k) in
/-- The tape holding the next word: the output tape of `Turing.MultiTapeTM.onWords`. -/
abbrev nextTape : Fin (k + 1 + 2) := (Fin.last k).castAdd 2

variable (k) in
/-- The flag tape of `Turing.MultiTapeTM.onWords`. -/
abbrev flagTape : Fin (k + 1 + 2) := Fin.natAdd (k + 1) 1

/-- Places the tapes of `(tidyCopy Symbol).onWords mark`: its output tape on the current tape, its
input tape on the next tape, its flag tape on the flag tape. -/
def copyEmb : Fin (0 + 1 + 2) ↪ Fin (k + 1 + 2) :=
  ⟨![curTape k, nextTape k, flagTape k], by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp [Fin.ext_iff] at h ⊢ <;> omega⟩

/-- Places the tapes of `(tidyCopy Symbol).inputFromWord mark`: its virtual input tape on the
current tape, its flag tape on the flag tape. -/
def emitEmb : Fin (0 + 2) ↪ Fin (k + 1 + 2) :=
  ⟨![curTape k, flagTape k], by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp [Fin.ext_iff] at h ⊢⟩

@[simp] lemma copyEmb_zero : copyEmb (k := k) 0 = curTape k := rfl
@[simp] lemma copyEmb_one : copyEmb (k := k) 1 = nextTape k := rfl
@[simp] lemma copyEmb_two : copyEmb (k := k) 2 = flagTape k := rfl
@[simp] lemma emitEmb_zero : emitEmb (k := k) 0 = curTape k := rfl
@[simp] lemma emitEmb_one : emitEmb (k := k) 1 = flagTape k := rfl

/-- The words between two phases: `vc` on the current tape, `vn` on the next tape, all other
tapes blank. -/
def words (vc vn : List Symbol) : Fin (k + 1 + 2) → List Symbol :=
  Function.update (Function.update (fun _ => []) (curTape k) vc) (nextTape k) vn

lemma curTape_ne_nextTape : curTape k ≠ nextTape k := Fin.ne_of_val_ne (by simp)

lemma flagTape_ne_nextTape : flagTape k ≠ nextTape k :=
  Fin.ne_of_val_ne (by simp only [Fin.val_natAdd, Fin.val_castAdd, Fin.val_last]; omega)

@[simp]
lemma words_cur (vc vn : List Symbol) : words (k := k) vc vn (curTape k) = vc := by
  simp [words, curTape_ne_nextTape]

@[simp]
lemma words_next (vc vn : List Symbol) : words (k := k) vc vn (nextTape k) = vn := by
  simp [words]

lemma update_words_cur (vc vn v : List Symbol) :
    Function.update (words (k := k) vc vn) (curTape k) v = words v vn := by
  rw [words, Function.update_comm curTape_ne_nextTape.symm, Function.update_idem, ← words]

lemma update_words_next (vc vn v : List Symbol) :
    Function.update (words (k := k) vc vn) (nextTape k) v = words vc v := by
  rw [words, Function.update_idem, ← words]

lemma words_nil_next (v : List Symbol) :
    words (k := k) v [] = Function.update (fun _ => []) (curTape k) v :=
  Function.update_eq_self_iff.mpr (by simp [curTape_ne_nextTape.symm])

lemma words_nil_cur (v : List Symbol) :
    words (k := k) [] v = Function.update (fun _ => []) (nextTape k) v := by
  rw [words]
  congr 1
  exact Function.update_eq_self _ _

lemma words_nil_nil : words (k := k) (Symbol := Symbol) [] [] = fun _ => [] := by
  rw [words_nil_next]
  exact Function.update_eq_self _ _

end IterateWhile

open IterateWhile

/-! ### The machine -/

variable (tm : MultiTapeTM k Symbol State) (mark : Symbol)

/-- One round: clear the current tape, copy the next word to it, clear the next tape and run `tm`
from the current tape to the next tape. -/
noncomputable def iterateWhileRound := ((clearWork Symbol).extendTapes (tapeEmb (curTape k))).seq
  ((((tidyCopy Symbol).onWords mark).extendTapes copyEmb).seq
    (((clearWork Symbol).extendTapes (tapeEmb (nextTape k))).seq (tm.onWords mark)))

/-- `tm`, applied repeatedly while its result is non-empty: copy the input to the next tape, repeat
rounds until the next tape is empty, then output the current word and clear its tape. -/
public noncomputable def iterateWhile :=
  (((tidyCopy Symbol).outputToWord).extendTapes (tapeEmb (nextTape k))).seq
    ((repeatUntilBlank (nextTape k) (iterateWhileRound tm mark)).seq
      ((((tidyCopy Symbol).inputFromWord mark).extendTapes emitEmb).seq
        ((clearWork Symbol).extendTapes (tapeEmb (curTape k)))))

/-! ### The phases -/

namespace IterateWhile

variable (Symbol) in
/-- Clearing the current tape. -/
lemma clearCur (vc vn : List Symbol) :
    TransformsTapes ((clearWork Symbol).extendTapes (tapeEmb (curTape k)))
      (fun _ ws => ws = words vc vn) (fun _ _ ws' e => ws' = words [] vn ∧ e = [])
      (3 * (vc.length + 1)) (vc.length + 1 + (k + 1 + 2)) :=
  (transformsTapes_clearWork_tapeEmb _ vc).imp (fun _ _ h => by rw [h, words_cur])
    (fun _ _ _ _ h ⟨h', he⟩ => ⟨by rw [h', h, update_words_cur], he⟩) le_rfl le_rfl

variable (Symbol) in
/-- Clearing the next tape. -/
lemma clearNext (vc vn : List Symbol) :
    TransformsTapes ((clearWork Symbol).extendTapes (tapeEmb (nextTape k)))
      (fun _ ws => ws = words vc vn) (fun _ _ ws' e => ws' = words vc [] ∧ e = [])
      (3 * (vn.length + 1)) (vn.length + 1 + (k + 1 + 2)) :=
  (transformsTapes_clearWork_tapeEmb _ vn).imp (fun _ _ h => by rw [h, words_next])
    (fun _ _ _ _ h ⟨h', he⟩ => ⟨by rw [h', h, update_words_next], he⟩) le_rfl le_rfl

/-- Copying the next word to the empty current tape. -/
lemma copy (v : List Symbol) :
    TransformsTapes (((tidyCopy Symbol).onWords mark).extendTapes (copyEmb (k := k)))
      (fun _ ws => ws = words [] v) (fun _ _ ws' e => ws' = words v v ∧ e = [])
      (3 * v.length + 10) (4 * v.length + k + 15) := by
  refine (((computesTidily_tidyCopy v).onWords mark).extendTapes copyEmb).imp
    (fun _ ws hws => ?_) (fun _ ws ws' _ hws ⟨⟨hv, he⟩, hx⟩ => ⟨?_, he⟩) (by omega) (by omega)
  · subst hws
    funext j
    fin_cases j <;> simp [words, curTape_ne_nextTape, flagTape_ne_nextTape]
  · subst hws
    funext l
    by_cases hl : l ∈ Set.range (copyEmb (k := k))
    · obtain ⟨j, rfl⟩ := hl
      have := congrFun hv j
      fin_cases j <;> simp_all [words, Function.update_apply, Fin.ext_iff]
    · have hc : l ≠ curTape k := fun h => hl ⟨0, h.symm⟩
      have hn : l ≠ nextTape k := fun h => hl ⟨1, h.symm⟩
      rw [hx l hl]
      simp [words, hc, hn]

variable {tm} in
/-- Applying `tm` from the current tape to the empty next tape. -/
lemma step {v v' : List Symbol} {t s : ℕ} (h : tm.ComputesTidilyInTimeAndSpace v v' t s) :
    TransformsTapes (tm.onWords mark) (fun _ ws => ws = words v [])
      (fun _ _ ws' e => ws' = words v v' ∧ e = [])
      (t + v'.length + 6) (s + 2 * v.length + 2 * v'.length + 3 * k + 15) :=
  (h.onWords mark).imp (fun _ _ hws => hws.trans (words_nil_next v))
    (fun _ _ _ _ hws ⟨h', he⟩ => ⟨by rw [h', hws, update_words_next], he⟩) le_rfl le_rfl

variable {tm} in
/-- One round: from `vp` on the current tape and `v` on the next tape to `v` on the current tape
and `v'` on the next tape. -/
lemma round {vp v v' : List Symbol} {t s : ℕ} (h : tm.ComputesTidilyInTimeAndSpace v v' t s) :
    TransformsTapes (iterateWhileRound tm mark) (fun _ ws => ws = words vp v)
      (fun _ _ ws' e => ws' = words v v' ∧ e = [])
      (t + 3 * vp.length + 6 * v.length + v'.length + 22)
      (s + vp.length + 7 * v.length + 2 * v'.length + 6 * k + 38) := by
  refine (transformsTapes_seq (clearCur Symbol vp v) (transformsTapes_seq (copy mark v)
    (transformsTapes_seq (clearNext Symbol v v) (step mark h) fun _ _ _ _ _ hQ => hQ.1)
    fun _ _ _ _ _ hQ => hQ.1) fun _ _ _ _ _ hQ => hQ.1).imp (fun _ _ h => h) ?_ (by omega)
    (by omega)
  rintro _ _ _ _ _ ⟨_, _, _, ⟨-, rfl⟩,
    ⟨_, _, _, ⟨-, rfl⟩, ⟨_, _, _, ⟨-, rfl⟩, ⟨h, rfl⟩, rfl⟩, rfl⟩, rfl⟩
  exact ⟨h, rfl⟩

/-- Copying the input to the next tape. -/
lemma load (v : List Symbol) :
    TransformsTapes (((tidyCopy Symbol).outputToWord).extendTapes (tapeEmb (nextTape k)))
      (fun inp ws => inp = v ∧ ws = fun _ => []) (fun _ _ ws' e => ws' = words [] v ∧ e = [])
      (3 * v.length + 6) (2 * v.length + k + 5) :=
  ((computesTidily_tidyCopy v).outputToWord.tapeEmb (nextTape k)).imp
    (fun _ _ ⟨hin, hws⟩ => ⟨hin, by rw [hws]⟩)
    (fun _ _ ws' _ ⟨_, hws⟩ ⟨u, ⟨hu, he⟩, hws'⟩ => ⟨by rw [hws', hws, hu, words_nil_cur]; simp, he⟩)
    (by omega) (by omega)

/-- Emitting the current word. -/
lemma emit (v : List Symbol) :
    TransformsTapes (((tidyCopy Symbol).inputFromWord mark).extendTapes (emitEmb (k := k)))
      (fun _ ws => ws = words v []) (fun _ _ ws' e => ws' = words v [] ∧ e = v)
      (2 * v.length + 8) (2 * v.length + k + 11) := by
  obtain ⟨hrun, hspace⟩ := computesTidily_iff.mp (computesTidily_tidyCopy v)
  refine ((transformsTapes_inputFromWord_of_runFrom mark hrun hspace).extendTapes emitEmb).imp
    (fun _ ws hws => ?_) (fun _ ws ws' _ hws ⟨⟨hv, he⟩, hx⟩ => ⟨?_, he⟩) (by omega) (by omega)
  · subst hws
    funext j
    fin_cases j <;> simp [words, Function.update_apply, Fin.ext_iff] <;> rfl
  · rw [← hws]
    funext l
    by_cases hl : l ∈ Set.range (emitEmb (k := k))
    · obtain ⟨j, rfl⟩ := hl
      rw [congrFun hv j]
      subst hws
      fin_cases j <;> simp [words, Function.update_apply, Fin.ext_iff] <;> rfl
    · exact hx l hl

end IterateWhile

open IterateWhile in
/-- If `tm` computes `w (n + 1)` from `w n` tidily within `t n` steps and `s n` cells for every
`n ≤ r`, and `w (n + 1)` is empty exactly for `n = r`, then `tm.iterateWhile mark` computes `w r`
from `w 0` tidily. Each of the `r + 1` rounds costs `tm`'s time plus a term linear in the lengths
of the words; the space is linear in the largest space and the largest word length. -/
public theorem computesTidily_iterateWhile {tm : MultiTapeTM k Symbol State}
    {w : ℕ → List Symbol} {t s : ℕ → ℕ} {r : ℕ}
    (h : ∀ n ≤ r, tm.ComputesTidilyInTimeAndSpace (w n) (w (n + 1)) (t n) (s n))
    (hne : ∀ n < r, w (n + 1) ≠ []) (hnil : w (r + 1) = []) (mark : Symbol) :
    (tm.iterateWhile mark).ComputesTidilyInTimeAndSpace (w 0) (w r)
      ((r + 1) * ((Finset.range (r + 1)).sup t +
        10 * (Finset.range (r + 1)).sup (fun n => (w n).length) + 24) +
        8 * (Finset.range (r + 1)).sup (fun n => (w n).length) + 17)
      (2 * (k + 3) * ((Finset.range (r + 1)).sup s +
        10 * (Finset.range (r + 1)).sup (fun n => (w n).length) + 6 * k + 38) +
        5 * (Finset.range (r + 1)).sup (fun n => (w n).length) + 4 * k + 23) := by
  set T := (Finset.range (r + 1)).sup t
  set S := (Finset.range (r + 1)).sup s
  set L := (Finset.range (r + 1)).sup fun n => (w n).length
  have hT (n : ℕ) (hn : n ≤ r) : t n ≤ T := Finset.le_sup (Finset.mem_range.mpr (by omega))
  have hS (n : ℕ) (hn : n ≤ r) : s n ≤ S := Finset.le_sup (Finset.mem_range.mpr (by omega))
  have hL (n : ℕ) (hn : n ≤ r) : (w n).length ≤ L :=
    Finset.le_sup (f := fun n => (w n).length) (Finset.mem_range.mpr (by omega))
  have hL' (n : ℕ) (hn : n ≤ r) : (w (n + 1)).length ≤ L := by
    rcases Nat.lt_or_eq_of_le hn with hn | rfl
    · exact hL _ hn
    · simp [hnil]
  -- the word on the current tape at the start of round `n`
  let prev : ℕ → List Symbol := fun | 0 => [] | n + 1 => w n
  have hprev (n : ℕ) (hn : n ≤ r) : (prev n).length ≤ L := by
    cases n with
    | zero => simp [prev]
    | succ n => exact hL n (by omega)
  -- each round, within uniform bounds
  have hround (n : ℕ) (hn : n ≤ r) := (round mark (vp := prev n) (h n hn)).mono
    (t' := T + 10 * L + 23) (s' := S + 10 * L + 6 * k + 38)
    (by have := hT n hn; have := hprev n hn; have := hL n hn; have := hL' n hn; omega)
    (by have := hS n hn; have := hprev n hn; have := hL n hn; have := hL' n hn; omega)
  have hloop := transformsTapes_repeatUntilBlank (nextTape k) (tm := iterateWhileRound tm mark)
    (P := fun n _ ws emitted => ws = words (prev n) (w n) ∧ emitted = [])
    (R := fun _ ws emitted => ws = words (w r) [] ∧ emitted = [])
    (fun n hn _ => (hround n hn.le).imp (fun _ _ hP => hP.1)
      (fun _ _ _ _ ⟨_, hem⟩ ⟨hws', he⟩ => ⟨⟨hws', by simp [hem, he]⟩,
        by rw [hws', words_next]; exact hne n hn⟩) le_rfl le_rfl)
    (fun _ => (hround r le_rfl).imp (fun _ _ hP => hP.1)
      (fun _ _ _ _ ⟨_, hem⟩ ⟨hws', he⟩ => ⟨⟨by rw [hws', hnil], by simp [hem, he]⟩,
        by rw [hws', words_next, hnil]⟩) le_rfl le_rfl)
  refine (transformsTapes_seq (load (k := k) (w 0)) (transformsTapes_seq hloop
    (transformsTapes_seq (emit mark (w r)) (clearCur Symbol (w r) []) fun _ _ _ _ _ hQ => hQ.1)
    fun _ _ _ _ _ hQ => hQ.1) fun _ _ _ _ _ hQ => ⟨hQ.1, rfl⟩).imp (fun _ _ h => h) ?_ ?_ ?_
  · rintro _ _ _ _ _ ⟨_, _, _, ⟨-, rfl⟩,
      ⟨_, _, _, ⟨-, rfl⟩, ⟨_, _, _, ⟨-, rfl⟩, ⟨hws, rfl⟩, rfl⟩, rfl⟩, rfl⟩
    exact ⟨hws.trans words_nil_nil, by simp⟩
  · have : (r + 1) * (T + 10 * L + 23 + 1) = (r + 1) * (T + 10 * L + 24) := rfl
    have := hL 0 (Nat.zero_le _)
    have := hL r le_rfl
    omega
  · have : 2 * (k + 1 + 2) * (S + 10 * L + 6 * k + 38) =
        2 * (k + 3) * (S + 10 * L + 6 * k + 38) := rfl
    have := hL 0 (Nat.zero_le _)
    have := hL r le_rfl
    omega

/-! ### Iterating a computable function -/

/-- If `f` is tidily computable, so is `a ↦ f^[r a] a`, where `r a` is the number of applications of
`f` after which the encoding of the next value is empty. Each of the `r a + 1` rounds costs the time
of `f` on the current value plus a term linear in the lengths of the encodings; the space is linear
in the largest space of `f` on an intermediate value and the longest intermediate encoding. -/
public theorem ComputableTidilyInTimeAndSpace.iterateWhile {α : Type*} {f : α → α}
    {enc : α ↪ List Bool} {t s r : α → ℕ} (hf : ComputableTidilyInTimeAndSpace f enc enc t s)
    (hr : ∀ a, (∀ n < r a, enc (f^[n + 1] a) ≠ []) ∧ enc (f^[r a + 1] a) = []) :
    ∃ c, ComputableTidilyInTimeAndSpace (fun a => f^[r a] a) enc enc
      (fun a => (r a + 1) * ((Finset.range (r a + 1)).sup (fun n => t (f^[n] a)) +
        10 * (Finset.range (r a + 1)).sup (fun n => (enc (f^[n] a)).length) + 24) +
        8 * (Finset.range (r a + 1)).sup (fun n => (enc (f^[n] a)).length) + 17)
      (fun a => c * ((Finset.range (r a + 1)).sup (fun n => s (f^[n] a)) +
        (Finset.range (r a + 1)).sup (fun n => (enc (f^[n] a)).length) + 1)) := by
  obtain ⟨k, State, _, tm, htm⟩ := hf
  refine ⟨2 * (k + 3) * (6 * k + 48) + (4 * k + 28), k + 1 + 2, _, inferInstance,
    tm.iterateWhile true, fun a => ?_⟩
  have h := computesTidily_iterateWhile (w := fun n => enc (f^[n] a)) (t := fun n => t (f^[n] a))
    (s := fun n => s (f^[n] a)) (r := r a)
    (fun n _ => by simpa only [Function.iterate_succ_apply'] using htm (f^[n] a))
    (hr a).1 (hr a).2 true
  refine TransformsTapes.mono h le_rfl ?_
  beta_reduce
  generalize (Finset.range (r a + 1)).sup (fun n => s (f^[n] a)) = S
  generalize (Finset.range (r a + 1)).sup (fun n => (enc (f^[n] a)).length) = L
  -- the space of the loop, and the rest
  have h₁ : S + 10 * L + 6 * k + 38 ≤ (6 * k + 48) * (S + L + 1) := by
    have := Nat.mul_le_mul_right S (show 1 ≤ 6 * k + 48 by omega)
    have := Nat.mul_le_mul_right L (show 10 ≤ 6 * k + 48 by omega)
    rw [Nat.mul_add, Nat.mul_add]
    omega
  have h₂ : 5 * L + 4 * k + 23 ≤ (4 * k + 28) * (S + L + 1) := by
    have := Nat.mul_le_mul_right L (show 5 ≤ 4 * k + 28 by omega)
    rw [Nat.mul_add, Nat.mul_add]
    omega
  generalize 2 * (k + 3) = N
  have := Nat.mul_le_mul_left N h₁
  calc N * (S + 10 * L + 6 * k + 38) + 5 * L + 4 * k + 23
      ≤ N * ((6 * k + 48) * (S + L + 1)) + (4 * k + 28) * (S + L + 1) := by omega
    _ = (N * (6 * k + 48) + (4 * k + 28)) * (S + L + 1) := by
      rw [Nat.add_mul (N * (6 * k + 48)), Nat.mul_assoc]

/-- If `f` is tidily computable in time `t` and space `s` of the length of its input, for monotone
`t` and `s`, so is `a ↦ f^[r a] a`, where `r a` is the number of applications of `f` after which
the encoding of the next value is empty, provided that the number of rounds is at most `ρ n` and
the encodings of all intermediate values have length at most `l n`, for inputs of length `n`. -/
public theorem ComputableTidilyInTimeAndSpaceOfLength.iterateWhile {α : Type*} {f : α → α}
    {enc : α ↪ List Bool} {t s l ρ : ℕ → ℕ} {r : α → ℕ} (ht : Monotone t) (hs : Monotone s)
    (hf : ComputableTidilyInTimeAndSpaceOfLength f enc enc t s)
    (hr : ∀ a, (∀ n < r a, enc (f^[n + 1] a) ≠ []) ∧ enc (f^[r a + 1] a) = [])
    (hρ : ∀ a, r a ≤ ρ (enc a).length)
    (hl : ∀ a, ∀ n ≤ r a, (enc (f^[n] a)).length ≤ l (enc a).length) :
    ∃ c, ComputableTidilyInTimeAndSpaceOfLength (fun a => f^[r a] a) enc enc
      (fun n => (ρ n + 1) * (t (l n) + 10 * l n + 24) + 8 * l n + 17)
      (fun n => c * (s (l n) + l n + 1)) := by
  obtain ⟨c, h⟩ := ComputableTidilyInTimeAndSpace.iterateWhile hf hr
  refine ⟨c, h.mono (fun a => ?_) (fun a => ?_)⟩
  all_goals
    have hmem (n : ℕ) (hn : n ∈ Finset.range (r a + 1)) : n ≤ r a :=
      Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
    have hL : (Finset.range (r a + 1)).sup (fun n => (enc (f^[n] a)).length) ≤
        l (enc a).length := Finset.sup_le fun n hn => hl a n (hmem n hn)
  · have hT : (Finset.range (r a + 1)).sup (fun n => t (enc (f^[n] a)).length) ≤
        t (l (enc a).length) := Finset.sup_le fun n hn => ht (hl a n (hmem n hn))
    exact Nat.add_le_add_right (Nat.add_le_add (Nat.mul_le_mul (by have := hρ a; omega)
      (by omega)) (by omega)) _
  · have hS : (Finset.range (r a + 1)).sup (fun n => s (enc (f^[n] a)).length) ≤
        s (l (enc a).length) := Finset.sup_le fun n hn => hs (hl a n (hmem n hn))
    exact Nat.mul_le_mul_left c (by omega)

end Turing.MultiTapeTM
