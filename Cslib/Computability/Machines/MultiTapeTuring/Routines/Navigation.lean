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
    {ls : List Data}
    (h_list : (views i).current = some (Data.list ls))
    (h_nonempty : 0 < ls.length) :
    (right i).eval_struct views = some
      (Function.update views i ⟨(views i).data, (views i).path ++ [0]⟩) := by
  sorry

def skipRight_n {k : ℕ} (n : ℕ) (i : Fin k) : MultiTapeTM k Char :=
  match n with
  | 0 => noop
  | n + 1 => skipRight_n n i ;ₜ skipRight i

lemma skipRight_n.eval_struct {j n : ℕ} {k : ℕ} {i : Fin k} {views : Fin k → TapeView}
    {parent : TapeView}
    {list : List Data}
    (h_len : j + n < list.length)
    (h_parent : parent.current = some (Data.list list))
    (h_list : views i = ⟨parent.data, parent.path ++ [j]⟩) :
    (skipRight_n n i).eval_struct views = some
      (Function.update views i ⟨parent.data, parent.path ++ [j + n]⟩) := by
  induction n with
  | zero => simp [skipRight_n, h_list]
  | succ n ih =>
     simp only [skipRight_n, seq_eval_struct, Part.coe_some]
     rw [ih (by omega)]
     simp only [Part.coe_some, Part.bind_some]
     have h_next : (TapeView.mk parent.data (parent.path ++ [j + n])).next.isSome := by
       simp [TapeView.currentList, h_parent, h_len, Nat.add_assoc]
     rw [skipRight_eval_struct (by grind)]
     simp [Nat.add_assoc]

/-- Navigate to the `idx`-th element of a `Data.list` encoding on tape `i`.
Moves past `(` and then skips `idx` Data elements.
If `i` is larger than the length of the list, does nothing. -/
public def toElem {k : ℕ} (idx : ℕ) (i : Fin k) : MultiTapeTM k Char :=
  right i ;ₜ skipRight_n idx i


/-- `toElem idx i` moves to the `idx`th element of the `Data.list` currently pointed to
on tape `i`. -/
@[simp]
public lemma toElem_eval_struct {k : ℕ} {idx : ℕ} {i : Fin k} {views : Fin k → TapeView}
  {list : List Data}
  {h_isList : (views i).current = some (Data.list list)}
  {h_len : idx < list.length} :
  (toElem idx i).eval_struct views = some
    (Function.update views i ⟨(views i).data, (views i).path ++ [idx]⟩) := by
  have h_nonempty : 0 < list.length := by omega
  simp only [toElem, seq_eval_struct, h_isList, Option.some.injEq, Data.list.injEq, h_nonempty,
    right_on_nonempty_list, TapeView.toElem?, Part.coe_some, Part.bind_some]
  rw [skipRight_n.eval_struct (j := 0) (by simp [h_len]) h_isList (by simp)]
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
      (Function.update views i
        ⟨(views i).data, (views i).path.dropLast⟩) := by sorry

end Routines
end Turing
