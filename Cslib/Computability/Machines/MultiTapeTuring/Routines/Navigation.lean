/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.MultiTapeTuring.StructuralMachines
public import Cslib.Computability.Machines.MultiTapeTuring.Routines.Iterate
public import Cslib.Computability.Machines.MultiTapeTuring.Routines.Skip


namespace Turing
namespace Routines


@[simp]
public lemma right_on_nonempty_list {k : ℕ} {i : Fin k}
    {views : Fin k → TapeView}
    (h_left : (views i).headPos = .leftEnd) :
    (right i).eval_struct views = .some (Function.update views i (
      if h_empty : (views i).current = Data.list [] then
        (views i).toRightEnd
      else
        (views i).appendPath 0 (by simp [h_empty]))) := by
  let effect :=
      if h_empty : (views i).current = .list [] then
        (views i).toRightEnd
      else
        (views i).appendPath 0 (by simp [h_empty])
  have h : Function.update (TapeView.toBiTape ∘ views) i (views i).toBiTape.move_right =
      fun j => ((Function.update views i effect) j).toBiTape := by
    ext1 j
    by_cases h_ij : i = j
    · subst h_ij
      simp only [effect, Function.update_self, TapeView.appendPath]
      by_cases h_empty : (views i).current = .list []
      · simp only [h_empty, dite_true]
        rw [TapeView.toBiTape_toRightEnd]
        have h_eq : (views i).toLeftEnd = views i := by
          ext <;> simp_all
        rw [h_eq, h_empty]
        simp [Data.enc_list]
      · -- h_empty : ¬((views i).current = Data.list [])
        simp only [h_empty, dite_false, h_left]
        rw [TapeView.toBitape_of_appendPath]
        simp [List.take]
    · have : j ≠ i := by aesop
      simp [this]
  simp [h, TapeView.ofBiTapes?, MultiTapeTM.eval_struct, effect]

def skipRight_n {k : ℕ} (n : ℕ) (i : Fin k) : MultiTapeTM k Char :=
  iterate_n (skipRight i) n

lemma skipRight_n.eval_struct {j n : ℕ} {k : ℕ} {i : Fin k} {views : Fin k → TapeView}
    {parent : TapeView}
    (h_valid : (parent.current.atPath [j + n]).isSome)
    (h_left : parent.headPos = .leftEnd)
    (h_parent : (views i) = parent.appendPath j
          (Data.atPath_isSome_of_le_isSome (by simp) h_valid)) :
    (skipRight_n n i).eval_struct views = .some (Function.update views i
      ((views i).parent.appendPath (j + n) (by simpa [h_parent] using h_valid))) := by
  induction n generalizing j views with
  | zero => simp [skipRight_n, iterate_n_zero, h_parent]
  | succ n ih =>
     -- skipRight_n (n+1) = skipRight ;ₜ skipRight_n n
     simp only [skipRight_n, iterate_n_succ, seq_eval_struct]
     -- First do one skipRight: j → j+1
     have h_j_valid : (parent.current.atPath [j + 1]).isSome :=
       Data.atPath_isSome_of_le_isSome (by omega) h_valid
     rw [skipRight_eval_struct (by simp [h_parent]) (by simp [h_parent, h_left])]
     simp only [Part.bind_some, h_parent]
     -- The skipRight result needs simplification.
     -- Use convert to match with IH, then resolve side goals
     have h_valid' : (parent.current.atPath [j + 1 + n]).isSome := by
       have : j + 1 + n = j + (n + 1) := by omega
       rw [this]; exact h_valid
     rw [show iterate_n (skipRight i) n = skipRight_n n i from rfl]
     -- First, show the skipRight output is parent.appendPath (j+1)
     suffices h_eq :
       (let idx := (parent.appendPath j _).path.getLast?.get _
        if h_next : ((parent.appendPath j _).parent.current.atPath [idx.succ]).isSome then
          (parent.appendPath j _).parent.appendPath idx.succ h_next
        else
          (parent.appendPath j _).parent.toRightEnd) =
       parent.appendPath (j + 1) h_j_valid by
       rw [h_eq, ih h_valid' (by simp)]
       simp only [Function.update_idem, Function.update_self,
         TapeView.appendPath, TapeView.parent, List.dropLast_concat]
       simp only [show j + 1 + n = j + (n + 1) from by omega]
     -- Prove h_eq
     simp only [TapeView.appendPath, TapeView.parent, List.dropLast_concat,
       List.getLast?_concat, Option.get_some, Nat.succ_eq_add_one]
     rw [dif_pos h_j_valid]

/-- Navigate to the `idx`-th element of a `Data.list` encoding on tape `i`.
Moves past `(` and then skips `idx` Data elements.
If `i` is larger than the length of the list, does nothing. -/
public def toElem {k : ℕ} (idx : ℕ) (i : Fin k) : MultiTapeTM k Char :=
  right i;ₜ skipRight_n idx i

/-- `toElem idx i` moves to the `idx`th element of the `Data.list` currently pointed to
on tape `i`. -/
@[simp]
public lemma toElem_eval_struct {k : ℕ} {idx : ℕ} {i : Fin k} {views : Fin k → TapeView}
  (h_valid : ((views i).current.atPath [idx]).isSome)
  -- (h_left : (views i).headPos = .leftEnd)
  :
  (toElem idx i).eval_struct views = .some
    (Function.update views i ((views i).appendPath idx h_valid)) := by
  sorry

-- TODO for this to work, we need to encode numbers using `()`

/-- If positioned on the element of a list, navigates to the list containing it. -/
public def outOfList {k : ℕ} (i : Fin k) : MultiTapeTM k Char :=
  left i;ₜ while_eq ')' i (right i;ₜ skipLeft i;ₜ left i)

-- ((1)(2)(3))

lemma outOfList_inner {k : ℕ} {i : Fin k}
    (views : Fin k → TapeView)
    {tv : TapeView}
    (idx : ℕ)
    (path : List ℕ)
    (h_path : tv.path = path ++ [idx.succ])
    (h_left : tv.headPos = .leftEnd) :
  (right i;ₜ skipLeft i;ₜ left i).eval_tot (by grind)
    (Function.update (TapeView.toBiTape ∘ views) i tv.toBiTape.move_left) =
     Function.update (TapeView.toBiTape ∘ views) i
       (tv.parent.appendPath idx (by
           apply Data.atPath_isSome_of_succ_isSome
           sorry
         )).toBiTape.move_left := by
  sorry

/-- `outOfArg i` ascends back from within a list to the list itself. -/
@[simp]
public lemma outOfList_eval_struct_valid {k : ℕ} {i : Fin k}
    {views : Fin k → TapeView}
    {h_valid : !(views i).path.isEmpty} :
    (outOfList i).eval_struct views = some
      (Function.update views i (views i).parent) := by sorry

/-- Move into the given path, then execute `tm` and then move out again. -/
public def at_path {k : ℕ} (path : List ℕ) (i : Fin k) (tm : MultiTapeTM k Char) :
    MultiTapeTM k Char :=
  match path with
  | [] => tm
  | n :: path' => toElem n i;ₜ at_path path' i tm;ₜ outOfList i

end Routines
end Turing
