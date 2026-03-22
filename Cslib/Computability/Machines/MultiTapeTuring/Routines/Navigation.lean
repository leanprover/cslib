/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.MultiTapeTuring.StructuralMachines
public import Cslib.Computability.Machines.MultiTapeTuring.Routines.Skip


namespace Turing
namespace Routines


@[simp]
public lemma right_on_nonempty_list {k : ℕ} {i : Fin k}
    {views : Fin k → TapeView}
    (h_valid : ((views i).current.atPath [0]).isSome) :
    (right i).eval_struct views = .some
      (Function.update views i ((views i).appendPath 0 h_valid)) := by
  simp [MultiTapeTM.eval_struct]
  ext1 j
  by_cases h_ij : i = j
  · subst h_ij
    simp
    apply (Function.Injective.eq_iff TapeView.toBiTape_injective).mp
    sorry
  · have h : j ≠ i := by aesop
    simp [h]
    -- TODO should be easy since toBitape is injective.
    sorry

def skipRight_n {k : ℕ} (n : ℕ) (i : Fin k) : MultiTapeTM k Char :=
  match n with
  | 0 => noop
  | n + 1 => skipRight_n n i ;ₜ skipRight i

lemma skipRight_n.eval_struct {j n : ℕ} {k : ℕ} {i : Fin k} {views : Fin k → TapeView}
    {parent : TapeView}
    (h_valid : (parent.current.atPath [j + n]).isSome)
    (h_parent : (views i) = parent.appendPath j
          (Data.atPath_isSome_of_le_isSome (by simp) h_valid)) :
    (skipRight_n n i).eval_struct views = .some (Function.update views i
      ((views i).parent.appendPath (j + n) (by simp [h_parent, h_valid]))) := by
  induction n with
  | zero => simp [skipRight_n, h_parent]
  | succ n ih =>
     simp only [skipRight_n, seq_eval_struct]
     rw [ih (Data.atPath_isSome_of_le_isSome (by simp) h_valid) h_parent]
     simp only [Part.bind_some]
     rw [skipRight_eval_struct h_valid (by simp [h_parent])]
     simp [h_parent]
     grind

/-- Navigate to the `idx`-th element of a `Data.list` encoding on tape `i`.
Moves past `(` and then skips `idx` Data elements.
If `i` is larger than the length of the list, does nothing. -/
public def toElem {k : ℕ} (idx : ℕ) (i : Fin k) : MultiTapeTM k Char :=
  right i ;ₜ skipRight_n idx i

/-- `toElem idx i` moves to the `idx`th element of the `Data.list` currently pointed to
on tape `i`. -/
@[simp]
public lemma toElem_eval_struct {k : ℕ} {idx : ℕ} {i : Fin k} {views : Fin k → TapeView}
  (h_valid : ((views i).current.atPath [idx]).isSome) :
  (toElem idx i).eval_struct views = .some
    (Function.update views i ((views i).appendPath idx h_valid)) := by
  have h : 0 ≤ idx := by omega
  simp only [toElem, seq_eval_struct, Data.atPath_isSome_of_le_isSome h h_valid,
    right_on_nonempty_list, TapeView.appendPath, Part.bind_some]
  rw [skipRight_n.eval_struct (j := 0) (parent := views i) (by simp [h_valid]) (by simp)]
  simp

-- lemma outOfList_inner {k : ℕ} {i : Fin k} {views : Fin k → TapeView} :
--   (right i ;ₜ skipLeft i ;ₜ left i).eval (toBiTape ∘ views) =
--     if (views i).current = some (Data.num 0) then some views else
--       if (views i).current = some (Data.list []) then some views else
--         if (views i).current = some (Data.list (_ :: _)) then
--           some (Function.update views i ⟨(views i).data, (views i).path.dropLast⟩)
--         else some views := by sorry

/-- If positioned on the element of a list, navigates to the list containing it. -/
public def outOfList {k : ℕ} (i : Fin k) : MultiTapeTM k Char :=
  left i ;ₜ while_eq ')' i (right i ;ₜ skipLeft i ;ₜ left i) ;ₜ
    -- This part handles the case where we started out with a number on the tape or
    -- an empty tape.
    if_eq '(' i noop (right i)


/-- `outOfArg argIdx i` ascends back from the `argIdx`-th element,
    removing it from the end of the path. If the path ends with `argIdx`,
    strips it. If the path is empty or the tape is empty, does not change
    the `TapeView`. -/
@[simp]
public lemma outOfList_eval_struct_valid {k : ℕ} {i : Fin k}
    {views : Fin k → TapeView} :
    (outOfList i).eval_struct views = some
      (Function.update views i (views i).parent) := by sorry

end Routines
end Turing
