/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Init
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Appending tuples

Lemmas about `Fin.append` not (yet) in Mathlib: the two parts of an appended tuple never overlap
and appending commutes with post-composition and with updating an entry on either side.
-/

@[expose] public section

namespace Fin

variable {α β : Sort*} {m n : ℕ}

/-- The two parts of `Fin.append` never overlap. -/
theorem castAdd_ne_natAdd (i : Fin m) (j : Fin n) : castAdd n i ≠ natAdd m j :=
  Fin.ne_of_lt ((castAdd_lt n i).trans_le (Nat.le_add_right m j))

/-- Post-composition commutes with `Fin.append`. -/
theorem comp_append (f : α → β) (a : Fin m → α) (b : Fin n → α) :
    f ∘ append a b = append (f ∘ a) (f ∘ b) := by
  funext i
  cases i using addCases <;> simp

/-- Updating an entry of the left tuple is updating the appended tuple at `castAdd`. -/
theorem append_update_left (a : Fin m → α) (b : Fin n → α) (i : Fin m) (x : α) :
    append (Function.update a i x) b = Function.update (append a b) (castAdd n i) x := by
  funext l
  cases l using addCases with
  | left j => simp [Function.update_apply]
  | right j => simp [Function.update_of_ne (castAdd_ne_natAdd i j).symm]

/-- Updating an entry of the right tuple is updating the appended tuple at `natAdd`. -/
theorem append_update_right (a : Fin m → α) (b : Fin n → α) (i : Fin n) (x : α) :
    append a (Function.update b i x) = Function.update (append a b) (natAdd m i) x := by
  funext l
  cases l using addCases with
  | left j => simp [Function.update_of_ne (castAdd_ne_natAdd j i)]
  | right j => simp [Function.update_apply]

end Fin
