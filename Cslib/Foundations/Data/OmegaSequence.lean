/-
Copyright (c) 2025 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou, Fabrizio Montesi
-/

import Mathlib.Data.Nat.Notation
import Mathlib.Data.FunLike.Basic

/-! # ω-sequences -/

/-- An `ωSequence α` is an infinite sequence of elements of type `α`. Elements are accessed by means
of function application. -/
structure ωSequence (α : Type _) where
  get : ℕ → α

instance : FunLike (ωSequence α) ℕ α where
  coe s := s.get
  coe_injective' := by
    rintro ⟨get1⟩ ⟨get2⟩
    grind

instance : Coe (ℕ → α) (ωSequence α) where
  coe f := ⟨f⟩

namespace ωSequence

/-- Drops the first `n` elements of an ω-sequence. -/
@[scoped grind =]
def drop (n : ℕ) (s : ωSequence α) : ωSequence α := fun i => s (i + n)

/-- Drops can be contracted by adding the numbers of dropped elements. -/
theorem drop_add {s : ωSequence α} (n1 n2 : ℕ) : (s.drop n1).drop n2 = s.drop (n1 + n2) := by
  simp only [drop, DFunLike.coe]
  congr
  ext i
  grind

/-- Applies a function to each element of an ω-sequence, returning the resulting ω-sequence. -/
@[scoped grind =]
def map (f : α → β) (s : ωSequence α) : ωSequence β := fun i => f (s i)

end ωSequence
