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

Lemmas about `Fin.append` not (yet) in Mathlib: appending constant tuples gives a constant tuple,
and appending commutes with post-composition and with updating an entry on either side.
-/

@[expose] public section

namespace Fin

variable {α β : Type*} {m n : ℕ}

/-- The two parts of `Fin.append` never overlap. -/
theorem castAdd_ne_natAdd (i : Fin m) (j : Fin n) : castAdd n i ≠ natAdd m j :=
  ne_of_val_ne (by simp only [val_castAdd, val_natAdd]; omega)

/-- Appending two constant tuples gives a constant tuple. -/
theorem append_const (x : α) : append (fun _ : Fin m => x) (fun _ : Fin n => x) = fun _ => x := by
  funext i
  refine addCases (fun j => ?_) (fun j => ?_) i <;> simp

/-- Post-composition commutes with `Fin.append`. -/
theorem comp_append (f : α → β) (a : Fin m → α) (b : Fin n → α) :
    f ∘ append a b = append (f ∘ a) (f ∘ b) := by
  funext i
  refine addCases (fun j => ?_) (fun j => ?_) i <;> simp

/-- Updating an entry of the left tuple is updating the appended tuple at `castAdd`. -/
theorem append_update_left (a : Fin m → α) (b : Fin n → α) (i : Fin m) (x : α) :
    append (Function.update a i x) b = Function.update (append a b) (castAdd n i) x := by
  funext l
  refine addCases (fun j => ?_) (fun j => ?_) l
  · simp [Function.update_apply]
  · simp [Function.update_of_ne (castAdd_ne_natAdd i j).symm]

/-- Updating an entry of the right tuple is updating the appended tuple at `natAdd`. -/
theorem append_update_right (a : Fin m → α) (b : Fin n → α) (i : Fin n) (x : α) :
    append a (Function.update b i x) = Function.update (append a b) (natAdd m i) x := by
  funext l
  refine addCases (fun j => ?_) (fun j => ?_) l
  · simp [Function.update_of_ne (castAdd_ne_natAdd j i)]
  · simp [Function.update_apply]

end Fin
