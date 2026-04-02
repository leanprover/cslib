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



/-- Run `tm` at the left end of the current item, restoring to the original position afterwards. -/
public def atLeft {k : ℕ} (i : Fin k) (tm : MultiTapeTM k Char) : MultiTapeTM k Char :=
  if_eq '(' i tm (toLeftEnd i;ₜ tm;ₜ toRightEnd i)

@[simp]
public lemma atLeft_eval_struct {k : ℕ} {i : Fin k} (tm : MultiTapeTM k Char)
  {views : Fin k → TapeView} :
    (atLeft i tm).eval_struct views =
      (tm.eval_struct (Function.update views i ((views i).toLeftEnd))).map
        (fun views' => Function.update views' i ((views' i).setHeadPosOf (views i))) := by
  simp [atLeft]
  sorry -- TOOD prove by AI


@[simp]
public lemma right_of_leftEnd {k : ℕ} {i : Fin k}
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
      · simp [h_empty, h_left]
      · simp only [h_empty, ↓reduceDIte]
        rw [show (views i).headPos = HeadPos.leftEnd from h_left]
        rw [TapeView.toBitape_of_appendPath]
        simp [List.take]
    · have : j ≠ i := by aesop
      simp [this]
  simp [h, TapeView.ofBiTapes?, MultiTapeTM.eval_struct, effect]

@[simp]
public lemma right_eval_struct {k : ℕ} {i : Fin k} {views : Fin k → TapeView} :
  (right i).eval_struct views =
    if h_left : (views i).headPos = .leftEnd then
      Part.some (Function.update views i (
        if h_empty : (views i).current = Data.list [] then
          (views i).toRightEnd
        else
          (views i).appendPath 0 (by simp [h_empty])))
    else
      if let some (idx : ℕ) := (views i).path.getLast? then
        Part.some (Function.update views i (
          if h_next : ((views i).parent.current.atPath [idx.succ]).isSome then
            (views i).parent.appendPath' idx.succ h_next
          else
            (views i).parent.toRightEnd))
      else
        Part.none -- not an encoding of Data, we are one cell to the right of it.
    := by
  by_cases h_left : (views i).headPos = .leftEnd
  · let effect :=
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
        · simp [h_empty, h_left]
        · simp only [h_empty, ↓reduceDIte]
          rw [show (views i).headPos = HeadPos.leftEnd from h_left]
          rw [TapeView.toBitape_of_appendPath]
          simp [List.take]
      · have : j ≠ i := by aesop
        simp [this]
    simp [h, TapeView.ofBiTapes?, MultiTapeTM.eval_struct, effect, h_left]
  · cases h_last : (views i).path.getLast? with
    | none =>
      simp [h_left]
      have h_path : (views i).path = [] := by
        cases h : (views i).path <;> simp_all [List.getLast?]
      have h_head : (views i).headPos = .rightEnd := by
        cases h : (views i).headPos <;> simp_all
      have h_encodedPos := TapeView.encodedPos_of_path_eq_nil_right (views i) h_path h_head
      sorry
    | some idx =>
      by_cases h_next : ((views i).parent.current.atPath [idx.succ]).isSome
      · simp only [h_next, h_left]
        simp
        sorry
      · simp only [h_next, h_left, ↓reduceDIte, Bool.false_eq_true]
        have h_right : (views i).headPos = .rightEnd := by
          cases h : (views i).headPos <;> simp_all
        have h_enc : (views i).encodedPos + 1 = (views i).parent.toRightEnd.encodedPos :=
          TapeView.encodedPos_last_child_succ (views i) h_last h_right h_next
        have h_data : (views i).data = (views i).parent.toRightEnd.data := by
          simp [TapeView.parent]
        have h_move : (views i).toBiTape.move_right = (views i).parent.toRightEnd.toBiTape := by
          simp only [TapeView.toBiTape, h_data]
          show BiTape.move_right (BiTape.move_right^[(views i).encodedPos]
            (BiTape.mk₁ (views i).parent.data.enc)) =
            BiTape.move_right^[(views i).parent.toRightEnd.encodedPos]
            (BiTape.mk₁ (views i).parent.data.enc)
          rw [show (views i).parent.toRightEnd.encodedPos =
            (views i).encodedPos + 1 from h_enc.symm]
          rw [Nat.add_comm, Function.iterate_add_apply, Function.iterate_one]
        have h_update : Function.update (TapeView.toBiTape ∘ views) i
            (views i).toBiTape.move_right =
            TapeView.toBiTape ∘ Function.update views i (views i).parent.toRightEnd := by
          rw [h_move, TapeView.toBiTape_comp_update]
        simp [MultiTapeTM.eval_struct, right.eval, h_update, TapeView.ofBiTapes?]

def skipRight_n {k : ℕ} (n : ℕ) (i : Fin k) : MultiTapeTM k Char :=
  iterate_n (skipRight i) n

-- TODO maybe we can change this to
-- lemma skipRight_n.eval_struct {j n : ℕ} {k : ℕ} {i : Fin k}
--     {views : Fin k → TapeView}
--     (h_valid : ((views i).parent.current.atPath [j + n]).isSome)
--     (h_parent : (views i) = (views i).parent.appendPath j
--           (Data.atPath_isSome_of_le_isSome (by simp) h_valid))
--     (h_left : (views i).headPos = .leftEnd) :


lemma skipRight_n.eval_struct {j n : ℕ} {k : ℕ} {i : Fin k}
    {views : Fin k → TapeView}
    {parent : TapeView}
    (h_valid : (parent.current.atPath [j + n]).isSome)
    (h_left : parent.headPos = .leftEnd)
    (h_parent : (views i) = parent.appendPath j
          (Data.atPath_isSome_of_le_isSome (by simp) h_valid)) :
    (skipRight_n n i).eval_struct views = .some (Function.update views i
      ((views i).parent.appendPath (j + n)
        (by simpa [h_parent] using h_valid))) := by
  induction n generalizing j views with
  | zero => simp [skipRight_n, iterate_n_zero, h_parent]
  | succ n ih =>
    have h_j1 : (parent.current.atPath [j + 1]).isSome :=
      Data.atPath_isSome_of_le_isSome (by omega) h_valid
    simp only [skipRight_n, iterate_n_succ, seq_eval_struct]
    rw [skipRight_eval_struct
      (by simp [h_parent]) (by simp [h_parent, h_left])]
    simp only [Part.bind_some, h_parent,
      TapeView.appendPath, TapeView.parent, List.dropLast_concat,
      List.getLast?_concat, Option.get_some, Nat.succ_eq_add_one]
    rw [dif_pos h_j1,
      show iterate_n (skipRight i) n = skipRight_n n i from rfl,
      ih (by rwa [show j + 1 + n = j + (n + 1) from by omega])
        (by simp)]
    simp only [Function.update_idem, Function.update_self,
      TapeView.appendPath, TapeView.parent, List.dropLast_concat,
      show j + 1 + n = j + (n + 1) from by omega]


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
public lemma outOfList_eval_struct {k : ℕ} {i : Fin k} {views : Fin k → TapeView} :
  (outOfList i).eval_struct views = some (Function.update views i (views i).parent) := by sorry


/-- Navigate to the `idx`-th element of a `Data.list` encoding on tape `i`.
Moves past `(` and then skips `idx` Data elements.
If `i` is larger than the length of the list, does nothing. -/
public def toElem {k : ℕ} (idx : ℕ) (i : Fin k) : MultiTapeTM k Char :=
  toLeftEnd i;ₜ right i;ₜ skipRight_n idx i

/-- `toElem idx i` moves to the `idx`th element of the `Data.list` currently pointed to
on tape `i`. -/
@[simp]
public lemma toElem_eval_struct {k : ℕ} {idx : ℕ} {i : Fin k} {views : Fin k → TapeView}
  (h_valid : ((views i).current.atPath [idx]).isSome) :
  (toElem idx i).eval_struct views = .some
    (Function.update views i ((views i).appendPath' idx h_valid)) := by
  have h_ne : (views i).current ≠ Data.list [] :=
    Data.atPath_zero_isSome_of_nonempty.mp
      (Data.atPath_isSome_of_le_isSome (by omega) h_valid)
  simp only [toElem, seq_eval_struct, toLeftEnd_eval_struct, Part.bind_some, right_eval_struct,
    Part.bind_some, Function.update_idem, Function.update_self,
    show ¬(views i).toLeftEnd.current = Data.list [] from h_ne, ↓reduceDIte]
  rw [skipRight_n.eval_struct (j := 0) (parent := (views i).toLeftEnd)
      (by simpa using h_valid) (by simp) (by simp)]
  simp

-- TODO this has a double toLeftEnd which is not needed.

/-- Execute `tm` at a certain element of the list. -/
public def atElem {k : ℕ} (idx : ℕ) (i : Fin k) (tm : MultiTapeTM k Char) : MultiTapeTM k Char :=
  atLeft i (toElem idx i;ₜ tm;ₜ outOfList i)

@[simp]
public lemma atElem_eval_struct {k : ℕ} {idx : ℕ} {i : Fin k} {tm : MultiTapeTM k Char}
    {views : Fin k → TapeView}
    (h_valid : ((views i).current.atPath [idx]).isSome) :
    (atElem idx i tm).eval_struct views = (tm.eval_struct
      (Function.update views i ((views i).appendPath' idx h_valid))).map
        fun views' => Function.update views' i ((views' i).parent.setHeadPosOf (views i)) := by
  simp [atElem, h_valid, Part.bind_some_eq_map]

/-- Move into the given path, then execute `tm` and then move out again. -/
public def atPath {k : ℕ} (path : List ℕ) (i : Fin k) (tm : MultiTapeTM k Char) :
    MultiTapeTM k Char :=
  match path with
  | [] => tm
  | n :: path' => toElem n i;ₜ atPath path' i tm;ₜ outOfList i

end Routines
end Turing
