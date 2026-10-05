/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.FastCatalogue

/-!
# Coverage certificates in bounded blocks

Splitting a catalogue's profile word into blocks bounds the memory needed by each kernel check.
The block words can then be combined without repeating the individual profile computations.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Code

/-- Combine lower and upper blocks of bits. -/
def joinWords (width lower upper : ℕ) : ℕ := Nat.lor lower (Nat.shiftLeft upper width)

/-- A profile word is the union of words for successive bounded blocks of models. -/
theorem profileWord_eq_chunks {m p width count : ℕ} (profiles : ℕ → ℕ → ℕ)
    (hw : 0 < width) (hc : m ≤ width * count) :
    profileWord m p profiles = orBelow (fun b =>
      profileWord (min width (m - b * width)) p (fun i q => profiles (b * width + i) q)) count := by
  apply Nat.eq_of_testBit_eq
  intro mask
  rw [← bitAt_eq_testBit, ← bitAt_eq_testBit, Bool.eq_iff_iff, bitAt_profileWord, bitAt_orBelow]
  simp only [bitAt_profileWord]
  constructor
  · rintro ⟨i, hi, q, hq, he⟩
    have hdiv : i / width < count := (Nat.div_lt_iff_lt_mul hw).mpr (by
      rw [Nat.mul_comm]
      exact lt_of_lt_of_le hi hc)
    have hmod := Nat.mod_lt i hw
    have hsum : i / width * width + i % width = i := by
      simpa only [Nat.mul_comm, Nat.add_comm] using Nat.mod_add_div i width
    refine ⟨i / width, hdiv, i % width, ?_, q, hq, ?_⟩
    · apply lt_min hmod
      omega
    · simpa only [hsum] using he
  · rintro ⟨b, _, i, hi, q, hq, he⟩
    have hi' := (lt_min_iff.mp hi).2
    exact ⟨b * width + i, by omega, q, hq, he⟩

/-- Replace every block by its independently verified word. -/
theorem profileWord_eq_of_chunks {m p width count : ℕ} (profiles : ℕ → ℕ → ℕ)
    (hw : 0 < width) (hc : m ≤ width * count) (words : ℕ → ℕ)
    (hwords : ∀ b < count,
      profileWord (min width (m - b * width)) p (fun i q => profiles (b * width + i) q) =
        words b) :
    profileWord m p profiles = orBelow words count := by
  rw [profileWord_eq_chunks profiles hw hc]
  apply Nat.eq_of_testBit_eq
  intro mask
  rw [← bitAt_eq_testBit, ← bitAt_eq_testBit, Bool.eq_iff_iff, bitAt_orBelow, bitAt_orBelow]
  constructor
  · rintro ⟨b, hb, h⟩
    exact ⟨b, hb, by simpa only [hwords b hb] using h⟩
  · rintro ⟨b, hb, h⟩
    exact ⟨b, hb, by simpa only [hwords b hb] using h⟩

end Cslib.RelationAlgebra.Code
