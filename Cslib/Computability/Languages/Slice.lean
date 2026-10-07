/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Cslib.Init
public import Mathlib.Computability.Language

/-!
# Slices of languages

A language is the union of its slices, one for each word length. The slice at length `n` is a
Boolean-valued function of the `n` letters of a word, so it can be handled by models of
computation with a fixed number of inputs, such as circuits. Conversely, one such function for
each length assembles into a language, and slicing that language recovers the functions.

Membership in an arbitrary language is not decidable, so a slice is defined classically. This is
what lets notions defined for Boolean-valued functions, such as circuit complexity, apply to every
language rather than only to decidable ones.
-/

@[expose] public section

namespace Language

variable {α : Type*}

/-- The words of length `n` in `L`, as a Boolean-valued function of their letters. -/
noncomputable def slice (L : Language α) (n : ℕ) : (Fin n → α) → Bool :=
  open scoped Classical in fun x => decide (List.ofFn x ∈ L)

@[simp] theorem slice_eq_true_iff {L : Language α} {n : ℕ} {x : Fin n → α} :
    L.slice n x = true ↔ List.ofFn x ∈ L :=
  @decide_eq_true_iff _ (Classical.propDecidable _)

/-- The language whose slice at each length `n` is `f n`. -/
def ofSlices (f : ∀ n, (Fin n → α) → Bool) : Language α :=
  {w | f w.length (fun i => w[i]) = true}

theorem mem_ofSlices {f : ∀ n, (Fin n → α) → Bool} {w : List α} :
    w ∈ ofSlices f ↔ f w.length (w[·]) := Iff.rfl

@[simp] theorem ofFn_mem_ofSlices {f : ∀ n, (Fin n → α) → Bool} {n : ℕ} {x : Fin n → α} :
    .ofFn x ∈ ofSlices f ↔ f n x := by
  congrm f $List.length_ofFn $((Fin.heq_fun_iff List.length_ofFn).mpr ?_)
  simp

@[simp] theorem slice_ofSlices (f : ∀ n, (Fin n → α) → Bool) (n : ℕ) :
    (ofSlices f).slice n = f n := by
  ext x
  rw [Bool.eq_iff_iff, slice_eq_true_iff, ofFn_mem_ofSlices]

end Language
