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

-- ═══════════════════════════════════════════════════════════════════════════
-- Argument navigation (for Data.list values)
-- ═══════════════════════════════════════════════════════════════════════════

def skipRight_n {k : ℕ} (n : ℕ) (i : Fin k) : MultiTapeTM k Char :=
  match n with
  | 0 => noop
  | n + 1 => skipRight_n n i ;ₜ skipRight i

@[simp]
lemma skipRight_n.eval_struct {k : ℕ} {n : ℕ} {i : Fin k} {views : Fin k → TapeView}
    (path : List ℕ)
    (h_path : (views i).path = path ++ [idx])
    (h_hasNextN : ((views i).data.atPath (path ++ [idx + n])).isSome) :
    (skipRight_n n i).eval_struct views = some
      (Function.update views i
        ⟨(views i).data, path ++ [idx + n]⟩) := by
  induction n generalizing path with
  | zero => simp [skipRight_n]; ext1 <;> simp [h_path]
  | succ n ih =>
    simp [skipRight_n]
    let ih' := ih path h_path (by sorry)--simp [← Nat.add_assoc] at h_hasNextN; simp [h_hasNextN])
    rw [ih']
    simp



    sorry

/-- Navigate to the `idx`-th element of a `Data.list` encoding on tape `i`.
Moves past `(` and then skips `idx` Data elements.
If `i` is larger than the length of the list, does nothing. -/
public def toElem {k : ℕ} (idx : ℕ) (i : Fin k) : MultiTapeTM k Char :=
  right i

/-- If positioned on the element of a list, navigates to the list containing it. -/
public def outOfList {k : ℕ} (i : Fin k) : MultiTapeTM k Char :=
  left i ;ₜ while_eq ')' i (right i ;ₜ skipLeft i ;ₜ left i) ;ₜ
    -- This part handles the case where we started out with a number on the tape or
    -- an empty tape.
    if_eq '(' i noop (right i)


/-- `toElem idx i` moves to the `idx`th element of the `Data.list` currently pointed to
on tape `i`. Only descends if the current element is a `Data.list` with at least `idx` elements,
otherwise, the `TapeView` is unchanged. -/
@[simp]
public lemma toElem_eval_struct {k : ℕ} {idx : ℕ} {i : Fin k} {views : Fin k → TapeView} :
  (toElem idx i).eval_struct views = some
    (Function.update views i (((views i).toElem? idx).getD (views i))) := by sorry

-- lemma outOfList_inner {k : ℕ} {i : Fin k} {views : Fin k → TapeView} :
--   (right i ;ₜ skipLeft i ;ₜ left i).eval (toBiTape ∘ views) =
--     if (views i).current = some (Data.num 0) then some views else
--       if (views i).current = some (Data.list []) then some views else
--         if (views i).current = some (Data.list (_ :: _)) then
--           some (Function.update views i ⟨(views i).data, (views i).path.dropLast⟩)
--         else some views := by sorry

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
