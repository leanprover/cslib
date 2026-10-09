/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Mathlib.Algebra.BigOperators.Fin
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.ExtendTapes
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.ForwardWork
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.RewindWork
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Sequential

/-!
# A machine that clears a work tape

`clearWork Symbol` erases the word on its work tape and returns the head to the start. It never
moves the input head and never outputs. It is the sequential composition of two one-tape machines:

* `forwardWork Symbol` moves the head right over the word until it reads the first blank, the
  frontier just past the word, and halts there (see `Plumbing.ForwardWork`).
* `rewindWork Symbol (some none)` rewinds the head to the start, erasing every symbol it walks
  over.

On a word of length `l` the forward pass takes `l + 1` steps and the erasing rewind `l + 2` steps.
The head stays within the cells `-1, …, l`, so the machine runs in time `3 * (l + 1)` and space
`l + 2`; placed on tape `i` of `k` tapes, the remaining tapes contribute one cell each.

## Main results

* `Turing.MultiTapeTM.clearWork`: the one-tape machine that clears its tape.
* `Turing.MultiTapeTM.transformsTapes_clearWork`: `clearWork` replaces the word on its tape by the
  empty word.
* `Turing.MultiTapeTM.transformsTapes_clearWork_tapeEmb`: placed on tape `i` of a `k`-tape machine
  it does so on that tape and leaves every other tape unchanged.
-/

open Turing.MultiTapeNTM

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol : Type*} {input : List Symbol}

/-- The one-tape machine that clears its tape: it moves to the end of the word and erases it on
the way back. -/
public def clearWork (Symbol : Type*) :
    MultiTapeTM 1 Symbol (Unit ⊕ RewindWorkState) :=
  { (forwardWork Symbol).seq (rewindWork Symbol (some none)) with
    deterministic := (forwardWork Symbol).deterministic.seq
      (rewindWork Symbol (some none)).deterministic }

open Sequential in
/-- **The machine that clears its work tape** replaces the word on it by the empty word, in at most
`3 * (w.length + 1)` steps and `w.length + 2` cells. -/
public theorem transformsTapes_clearWork (w : List Symbol) :
    TransformsTapes (clearWork Symbol).toMultiTapeNTM (fun _ ws => ws 0 = w)
      (fun _ _ ws' emitted => ws' = (fun _ => []) ∧ emitted = [])
      (3 * (w.length + 1)) (w.length + 2) := by
  -- the forward pass takes `w.length + 1` steps, the erasing rewind `w.length + 2`
  refine TransformsTapes.mono (t := w.length + 1 + (w.length + 2)) ?_ (by lia) le_rfl
  dsimp only [clearWork]
  intro input ws out hws
  obtain rfl : ws = fun _ => w := funext fun x => Fin.fin_one_eq_zero x ▸ hws
  have h₀ := runFrom_forwardWork (input := input) 1 w out (zero_add _)
  have h₁ := runFrom_rewindWork_erase (input := input) 1 (tapeOfList w) out rfl
  let p : (forwardWork Symbol).RunPath input :=
    { length := w.length + 1
      toFun n := (forwardWork Symbol).runFrom (wordsCfg input (some ()) (fun _ ↦ w) out) n
      step n := by simp [step_iff, runFrom, Function.iterate_succ_apply'] }
  let q : (rewindWork Symbol (some none)).RunPath input :=
    { length := w.length + 2
      toFun n := (rewindWork Symbol (some none)).runFrom
        ⟨some (rewindWork Symbol (some none)).q₀, 1,
          fun _ ↦ tapeOfList w, fun _ ↦ w.length, out⟩ n
      step n := by simp [step_iff, runFrom, Function.iterate_succ_apply'] }
  have hp : p.last = ⟨none, 1, fun _ ↦ tapeOfList w, fun _ ↦ w.length, out⟩ := h₀
  have hq : q.last = wordsCfg input none (fun _ ↦ []) out := by
    simpa [q, RelSeries.last, wordsCfg] using h₁
  obtain ⟨r, hr, hr', ht, _, hpos⟩ := p.exists_seq_of_invariant q
    (by rw [hp]) (by rw [hp]; rfl)
    (P := fun c ↦ c.workTapePos 0 ∈ Set.Icc (-1) (w.length : ℤ))
    (fun _ ⟨m, hm⟩ _ ↦ hm ▸ Set.Icc_subset_Icc_left (by lia)
      (workTapePos_runFrom_forwardWork (input := input) 1 w out (Nat.zero_le w.length) m))
    (fun _ ⟨n, hn⟩ ↦ hn ▸ workTapePos_runFrom_rewindWork (some none)
      (input := input) 1 (tapeOfList w) out rfl le_rfl n)
  refine ⟨fun _ ↦ [], [], r, hr, ?_, ⟨rfl, rfl⟩, ht, ?_⟩
  · rw [hr', hq, List.append_nil]
    rfl
  · rw [RunPath.space, Fin.sum_univ_one]
    exact (RunPath.spaceUsedByTape_le_card r (S := .Icc (-1) (w.length : ℤ))
      fun c hc ↦ Finset.mem_Icc.2 (hpos c hc)).trans (by simp; lia)

/-! ### Clearing one of several work tapes -/

/-- **The machine that clears a work tape**, placed on tape `i` of a `k`-tape machine, replaces the
word on that tape by the empty word and leaves every other tape unchanged, in at most
`3 * (w.length + 1)` steps and `w.length + 1 + k` cells. -/
public theorem transformsTapes_clearWork_tapeEmb (i : Fin k) (w : List Symbol) :
    TransformsTapes ((clearWork Symbol).extendTapes (tapeEmb i)) (fun _ ws => ws i = w)
      (fun _ ws ws' emitted => ws' = Function.update ws i [] ∧ emitted = [])
      (3 * (w.length + 1)) (w.length + 1 + k) :=
  ((transformsTapes_clearWork (Symbol := Symbol) w).tapeEmb i).imp (fun _ _ h => h)
    (fun _ ws ws' _ _ ⟨v, ⟨hv, he⟩, hws'⟩ => ⟨by rw [hws', hv], he⟩) le_rfl
    (by have := i.pos; lia)

end Turing.MultiTapeTM
