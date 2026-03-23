/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.MultiTapeTuring.Data

namespace Turing

-- ═══════════════════════════════════════════════════════════════════════════
-- TapeView
-- ═══════════════════════════════════════════════════════════════════════════

/-- A structured view of a tape's contents, abstracting away
    character-level encoding.

    - `data`: an optional `Data` value on the tape. `none` means the tape
      is empty, `some d` means the tape contains exactly `Data.enc d`.
    - `path`: a navigation path into the `Data` value.
      `[]` means the head is at the start of the encoding.
      `[k]` means the head points to the `k`-th element of a `Data.list`.
      `[k₁, k₂]` means we descended into element `k₁` (a list),
      then element `k₂`.

    Examples:
    - `⟨Data.num 5, []⟩` — tape contains `[12]`, head at start
    - `⟨Data.list [a, b], [1]⟩` — tape contains `(enc(a) enc(b))`,
      head at start of `enc(b)`
    - `⟨Data.list [], []⟩` — tape is empty -/
@[ext]
public structure TapeView where
  /-- The `Data` value on the tape. -/
  data : Data
  /-- Navigation path into the `Data` value. -/
  path : List ℕ
  /-- The path is valid. -/
  h_path : (data.atPath path).isSome

instance : Inhabited TapeView := ⟨⟨Data.list [], [], by rfl⟩⟩

namespace TapeView

/-- A tape containing a single Data value with the head at the start. -/
@[expose]
public abbrev ofData (d : Data) : TapeView := ⟨d, [], by rfl⟩

@[expose]
public abbrev ofList (ls : List Data) : TapeView := ofData (Data.list ls)

/-- An empty tape (represented as an empty list). -/
@[expose]
public abbrev empty : TapeView := ofList []

/-- A tape containing a single typed value with the head at the start. -/
@[expose]
public abbrev ofEnc {α : Type*} [StrEnc α] (x : α) : TapeView :=
  ofData (StrEnc.toData x)

/-- The Data element currently pointed to by the head (at the path
    position). Note that this is not tagged `@[simp]` because many
    preconditions on simp lemmas use `(views i).current = ...`. -/
@[expose]
public def current (tv : TapeView) : Data :=
  (tv.data.atPath tv.path).get tv.h_path

@[simp]
public lemma current_append {data : Data} {path : List ℕ}
    {h : (data.atPath path).isSome} :
  (TapeView.mk data path h).current =
    (data.atPath path).get h := by simp [current]

@[simp]
public lemma mk_data_path (tv : TapeView)
    (h : (tv.data.atPath tv.path).isSome) :
    TapeView.mk tv.data tv.path h = tv := by
  cases tv; rfl

-- TODO it looks weird to make that a simp. is it OK?
@[simp]
public lemma current_rev (tv : TapeView) :
  tv.data.atPath tv.path = tv.current := by simp [current]

/-- The current value as a natural number, if it is a `Data.num`.
    Returns `none` if the tape is empty, the path is invalid,
    or the value at the path is a `Data.list`. -/
public def currentNum (tv : TapeView) : Option ℕ :=
  match tv.current with
  | Data.num n => some n
  | _ => none

/-- The current value as a list, if it is a `List`.
    Returns `none` if the tape is empty, the path is invalid,
    or the value at the path is not a `Data.list`. -/
@[expose]
public abbrev currentList? (tv : TapeView) : Option (List Data) :=
  match tv.current with
  | Data.list ls => some ls
  | _ => none

@[simp]
public lemma current_of_currentList (tv : TapeView) (ls : List Data)
    (h_currentList : tv.currentList? = some ls) :
  tv.current = Data.list ls := by grind

@[expose, simp]
public def parent (tv : TapeView) : TapeView :=
  match tv.path with
  | [] => tv
  | _ => ⟨tv.data, tv.path.dropLast, by simp⟩

@[expose, simp]
public def appendPath (tv : TapeView) (idx : ℕ)
    (h : (tv.current.atPath [idx]).isSome) : TapeView :=
  ⟨tv.data, tv.path ++ [idx], by simpa using h⟩

/-- Attempt to decode the current value as a typed value of type `α`.
    Returns `none` if the tape is empty, the path is invalid,
    or the `Data` at the path does not represent a valid value of
    type `α`. -/
public def currentAs (α : Type*) [StrEnc α] (tv : TapeView) :
    Option α :=
  StrEnc.fromData tv.current

/-- The position of the head in the encoded version of the
    `TapeView`. -/
@[expose]
public def encodedPos : (tv : TapeView) → ℕ
  | ⟨_, [], _⟩ => 0
  | ⟨Data.num _, _ :: _, _⟩ => 0 -- unreachable
  | ⟨Data.list ds, p :: path, h_valid⟩ =>
      have h : p < ds.length := by grind [Data.atPath]
      1 +
        ((ds.take p).map fun d => d.enc.length).sum +
        encodedPos ⟨ds[p], path, by grind [Data.atPath]⟩
  termination_by tv => tv.path.length

@[simp]
public lemma encodedPos_of_path_eq_nil (tv : TapeView)
    (h_path : tv.path = []) :
  tv.encodedPos = 0 := by
  unfold encodedPos
  split <;> simp_all

@[simp]
public lemma encodedPos_appendPath (tv : TapeView) (idx : ℕ)
    (h : (tv.data.atPath (tv.path ++ [idx])).isSome) :
  (TapeView.mk tv.data (tv.path ++ [idx]) h).encodedPos =
      tv.encodedPos + 1 +
      (((tv.currentList?.getD []).take idx).map
        fun d => d.enc.length).sum := by
  unfold encodedPos
  sorry

/-- Convert a `TapeView` to the corresponding `BiTape Char`. -/
@[expose]
public def toBiTape (tv : TapeView) : BiTape Char :=
  BiTape.move_right^[tv.encodedPos] (BiTape.mk₁ tv.data.enc)

@[simp]
public lemma toBiTape_ofData (d : Data) :
  (TapeView.ofData d).toBiTape = BiTape.mk₁ (Data.enc d) := by
  simp [toBiTape, encodedPos]

public def ofBiTape? (t : BiTape Char) : Option TapeView := sorry

@[expose]
public def ofBiTapes? {k : ℕ}
    (tapes : Fin k → BiTape Char) :
    Option (Fin k → TapeView) :=
  if h: ∀ i, (ofBiTape? (tapes i)).isSome then
    some (fun i => (ofBiTape? (tapes i)).get (h i))
  else none

@[simp]
public lemma toBiTape_ofBiTape (tv : TapeView) :
  (ofBiTape? tv.toBiTape) = tv := by sorry

@[simp]
public lemma toBiTape_comp_update {k : ℕ} {i : Fin k}
    {views : Fin k → TapeView} {tv : TapeView} :
  Function.update (toBiTape ∘ views) i tv.toBiTape =
    toBiTape ∘ (Function.update views i tv) := by
  ext j
  by_cases h : i = j
  · subst h; simp
  · simp only [Function.comp_apply, Function.update_apply]
    split <;> simp_all

@[simp]
public lemma ofBiTapes?_toBiTape {k : ℕ}
    {views : Fin k → TapeView} :
    TapeView.ofBiTapes? (TapeView.toBiTape ∘ views) =
      some views := by
  simp [ofBiTapes?]

@[simp]
public lemma ofBiTape_get_toBiTape (tape : BiTape Char)
    (h : (ofBiTape? tape).isSome) :
  ((ofBiTape? tape).get h).toBiTape = tape := by sorry

@[simp]
public lemma toBiTape_injective :
    Function.Injective TapeView.toBiTape := by
  sorry -- use the above

@[simp]
public lemma toBitape_of_appendPath (tv : TapeView) (idx : ℕ)
    (h : (tv.data.atPath (tv.path ++ [idx])).isSome) :
  (TapeView.mk tv.data (tv.path ++ [idx]) h).toBiTape =
    BiTape.move_right^[1 +
      (((tv.currentList?.getD []).take idx).map
        fun d => d.enc.length).sum]
      tv.toBiTape := by
  sorry

/-- Prepend a `Data` value to the front of a list on tape.
    If the path is `[]` and `data` is `Data.list ds`,
    returns `⟨Data.list (d :: ds), [], _⟩`.
    Otherwise, returns the `TapeView` unchanged. -/
@[expose]
public def pushList (d : Data) (tv : TapeView) : TapeView :=
  match tv with
  | ⟨Data.list ds, [], _⟩ => ⟨Data.list (d :: ds), [], rfl⟩
  | other => other

@[simp]
public lemma pushList_list {d : Data} {ds : List Data} :
    (TapeView.mk (Data.list ds) [] sorry).pushList d =
      TapeView.mk (Data.list (d :: ds)) [] rfl := by
  unfold pushList; rfl

@[simp]
public lemma pushList_num {d : Data} {n : ℕ} {p : List ℕ} :
    (TapeView.mk (Data.num n) p sorry).pushList d =
      TapeView.mk (Data.num n) p sorry := by
  unfold pushList; rfl

@[simp]
public lemma pushList_nonempty_path {d : Data} {dat : Data}
    {k : ℕ} {rest : List ℕ} :
    (TapeView.mk dat (k :: rest) sorry).pushList d =
      TapeView.mk dat (k :: rest) sorry := by
  unfold pushList; cases dat with
  | num _ => rfl
  | list _ => rfl

public def asWritableList (tv : TapeView) : Option (List Data) :=
  match tv with
  | ⟨Data.list l, [], _⟩ => some l
  | _ => none

/-- Remove the first element from a list on tape. -/
public def popList (tv : TapeView) : TapeView :=
  (tv.asWritableList.map fun ls =>
    TapeView.ofList ls.tail).getD tv

/-- If `tv` currently points at a non-empty list, returns its head,
    otherwise returns none. -/
public def currentListHead (tv : TapeView) : Option Data :=
  match tv.current with
  | Data.list (d :: _) => some d
  | _ => none

public def updateListHead (tv : TapeView)
    (f : Data → Data) : TapeView :=
  match tv with
  | ⟨Data.list (d :: ds), [], _⟩ =>
    ⟨Data.list (f d :: ds), [], rfl⟩
  | other => other

public def updateListHeadTyped
    {α β : Type} [StrEnc α] [StrEnc β]
    (tv : TapeView) (f : α → β) : TapeView := (do
  let ls <- tv.asWritableList
  let d <- ls.head?
  let x <- StrEnc.fromData d
  return TapeView.ofList ((StrEnc.toData (f x)) :: ls.tail)).getD tv


end TapeView

end Turing
