/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Cslib.Foundations.Data.BitString
public import Mathlib.Computability.Language

/-!
# Slices of languages over bits

A language over `Bool` is the union of its slices, one for each word length. The slice at length
`n` is a Boolean function of `n` bits, so it can be handled by models of computation with a fixed
number of inputs, such as circuits. Conversely, a Boolean function for each length assembles into
a language, and slicing that language recovers the functions.

Membership in an arbitrary language is not decidable, so a slice is defined classically. This is
what lets notions defined for Boolean functions, such as circuit complexity, apply to every
language rather than only to decidable ones.
-/

@[expose] public section

namespace Language

/-- The words of length `n` in `L`, as a Boolean function of their letters. -/
noncomputable def slice (L : Language Bool) (n : ℕ) : Cslib.BooleanFunction n :=
  open scoped Classical in fun x => decide (List.ofFn x ∈ L)

@[simp] theorem slice_eq_true_iff {L : Language Bool} {n : ℕ} {x : Cslib.BitString n} :
    L.slice n x = true ↔ List.ofFn x ∈ L := by
  simp [slice]

/-- The language whose slice at each length `n` is `f n`. -/
def ofSlices (f : ∀ n, Cslib.BooleanFunction n) : Language Bool :=
  {w | f w.length (fun i => w[i]) = true}

@[simp] theorem slice_ofSlices (f : ∀ n, Cslib.BooleanFunction n) (n : ℕ) :
    (ofSlices f).slice n = f n := by
  funext x
  have h : (⟨_, fun i => (List.ofFn x)[i]⟩ : Σ m, Cslib.BitString m) = ⟨n, x⟩ :=
    List.ofFn_inj'.mp List.ofFn_getElem
  rw [Bool.eq_iff_iff, slice_eq_true_iff]
  exact (congrArg (fun p : Σ m, Cslib.BitString m => f p.1 p.2 = true) h).to_iff

end Language
