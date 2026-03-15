/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.MultiTapeTuring.Basic

namespace Turing

public instance : Fintype Char := by sorry

/-- Dyadic encoding of natural numbers. -/
public def dyadic (n : ℕ) : List Char :=
  if n = 0 then []
  else if Even n then
    dyadic (n / 2 - 1) ++ ['2']
  else
    dyadic ((n - 1) / 2) ++ ['1']

/-- Dyadic decoding of natural numbers. -/
public def dyadic_inv : List Char → Option ℕ := sorry

@[simp, grind =]
public lemma dyadic_inv_zero : dyadic_inv [] = .some 0 := by
  sorry

@[simp, grind =]
public lemma dyadic_inv_dyadic (n : ℕ) : dyadic_inv (dyadic n) = n := by sorry

/-- Universal data type for structured TM computation.
    All types processed by TM routines are first mapped to `Data`.
    Numbers are encoded with `[dyadic]` and lists with `(elem₁…elemₙ)`. -/
public inductive Data where
  /-- A natural number. -/
  | num : ℕ → Data
  /-- A list of data values. -/
  | list : List Data → Data

public instance : DecidableEq Data := sorry

/-- Encoding of `Data` into a list of characters.
    - `Data.num n` is encoded as `[dyadic(n)]`
    - `Data.list ds` is encoded as `(enc(d₁) ++ … ++ enc(dₙ))` -/
public def Data.enc : Data → List Char
  | Data.num n => ['['] ++ dyadic n ++ [']']
  | Data.list ds => ['('] ++ (ds.map Data.enc).flatten ++ [')']

@[simp]
public lemma Data.enc_num (n : ℕ) :
    Data.enc (Data.num n) = ['['] ++ dyadic n ++ [']'] := by
  unfold Data.enc; rfl

@[simp]
public lemma Data.enc_list (ds : List Data) :
    Data.enc (Data.list ds) = ['('] ++ (ds.map Data.enc).flatten ++ [')'] := by
  unfold Data.enc; rfl

public lemma Data.enc_injective : Function.Injective Data.enc := by sorry

/-- Typeclass for types that can be encoded as `Data` for TM computation. -/
public class StrEnc (α : Type*) where
  /-- Map a value to its `Data` representation. -/
  toData : α → Data
  /-- Attempt to decode a `Data` value back into the type.
      Returns `none` if the `Data` does not represent a valid value of the type. -/
  fromData : Data → Option α
  /-- Decoding after encoding always succeeds and returns the original value. -/
  fromData_toData : ∀ x : α, fromData (toData x) = some x

/-- Encoding of a value of type `α` via its `Data` representation. -/
public abbrev StrEnc.enc {α : Type*} [StrEnc α] (w : α) : List Char :=
  Data.enc (StrEnc.toData w)

/-- `toData` is injective, since `fromData` is a left inverse. -/
public lemma StrEnc.toData_injective (α : Type*) [StrEnc α] :
    Function.Injective (StrEnc.toData (α := α)) := by
  intro a b h
  have ha := StrEnc.fromData_toData a
  have hb := StrEnc.fromData_toData b
  rw [h] at ha
  rw [ha] at hb
  exact Option.some_injective _ hb

public instance : StrEnc Data where
  toData := id
  fromData := some
  fromData_toData _ := rfl

public instance : StrEnc ℕ where
  toData := Data.num
  fromData
    | Data.num n => some n
    | _ => none
  fromData_toData _ := rfl

public instance : StrEnc Bool where
  toData
    | false => Data.num 0
    | true => Data.num 1
  fromData
    | Data.num 0 => some false
    | Data.num 1 => some true
    | _ => none
  fromData_toData
    | false => rfl
    | true => rfl

@[simp]
public lemma StrEnc.toData_false : StrEnc.toData false = Data.num 0 := rfl

@[simp]
public lemma StrEnc.toData_true : StrEnc.toData true = Data.num 1 := rfl

@[simp]
public lemma StrEnc.fromData_num_nat (n : ℕ) : StrEnc.fromData (Data.num n) = some n := rfl

@[simp]
public lemma StrEnc.fromData_list_nat (ds : List Data) :
    (StrEnc.fromData (Data.list ds) : Option ℕ) = none := rfl

@[simp]
public lemma StrEnc.fromData_data (d : Data) : StrEnc.fromData d = some d := rfl

@[simp]
public lemma StrEnc.fromData_false : StrEnc.fromData (Data.num 0) = some false := rfl

@[simp]
public lemma StrEnc.fromData_true : StrEnc.fromData (Data.num 1) = some true := rfl

public instance (α : Type*) [StrEnc α] : StrEnc (List α) where
  toData l := Data.list (l.map StrEnc.toData)
  fromData
    | Data.list ds => ds.mapM StrEnc.fromData
    | _ => none
  fromData_toData l := by
    simp only
    induction l with
    | nil => rfl
    | cons a as ih =>
      simp only [List.map, List.mapM_cons]
      simp [StrEnc.fromData_toData a, ih]

-- ═══════════════════════════════════════════════════════════════════════════
-- Data.atPath
-- ═══════════════════════════════════════════════════════════════════════════

/-- Navigate into a `Data` value at the given path.
    Returns the sub-`Data` element at the path, or `none` if the path is invalid
    (e.g., indexing into a `num` or out-of-bounds on a `list`). -/
public def Data.atPath : Data → List ℕ → Option Data
  | d, [] => some d
  | Data.list ds, k :: rest =>
    if h : k < ds.length then (ds[k]).atPath rest else none
  | Data.num _, _ :: _ => none

@[simp]
public lemma Data.atPath_nil (d : Data) : d.atPath [] = some d := by
  unfold Data.atPath; rfl

@[simp]
public lemma Data.atPath_list_cons (ds : List Data) (k : ℕ) (rest : List ℕ)
    (h : k < ds.length) :
    (Data.list ds).atPath (k :: rest) = (ds[k]).atPath rest := by
  simp [Data.atPath, h]

-- ═══════════════════════════════════════════════════════════════════════════
-- TapeView
-- ═══════════════════════════════════════════════════════════════════════════

/-- A structured view of a tape's contents, abstracting away character-level encoding.

    - `data`: an optional `Data` value on the tape. `none` means the tape is empty,
      `some d` means the tape contains exactly `Data.enc d`.
    - `path`: a navigation path into the `Data` value.
      `[]` means the head is at the start of the encoding.
      `[k]` means the head points to the `k`-th element of a `Data.list`.
      `[k₁, k₂]` means we descended into element `k₁` (a list), then element `k₂`.

    Examples:
    - `⟨Data.num 5, []⟩` — tape contains `[12]`, head at start
    - `⟨Data.list [a, b], [1]⟩` — tape contains `(enc(a) enc(b))`,
      head at start of `enc(b)`
    - `⟨Data.list [], []⟩` — tape is empty -/
public structure TapeView where
  /-- The `Data` value on the tape. -/
  data : Data
  /-- Navigation path into the `Data` value. -/
  path : List ℕ

instance : Inhabited TapeView := ⟨⟨Data.list [], []⟩⟩

namespace TapeView

/-- An empty tape (represented as an empty list). -/
public def empty : TapeView := ⟨Data.list [], []⟩

/-- A tape containing a single Data value with the head at the start. -/
public def ofData (d : Data) : TapeView := ⟨d, []⟩

public def ofList (ls : List Data) : TapeView := ofData (Data.list ls)

/-- A tape containing a single typed value with the head at the start. -/
public def ofEnc {α : Type*} [StrEnc α] (x : α) : TapeView :=
  ofData (StrEnc.toData x)

/-- The Data element currently pointed to by the head (at the path position).
    Returns `none` if the path is invalid. -/
public def current (tv : TapeView) : Option Data :=
  tv.data.atPath tv.path

/-- The current value as a natural number, if it is a `Data.num`.
    Returns `none` if the tape is empty, the path is invalid,
    or the value at the path is a `Data.list`. -/
public def currentNum (tv : TapeView) : Option ℕ :=
  match tv.current with
  | some (Data.num n) => some n
  | _ => none

/-- The current value as a list, if it is a `List`.
    Returns `none` if the tape is empty, the path is invalid,
    or the value at the path is not a `Data.list`. -/
public def currentList (tv : TapeView) : Option (List Data) :=
  match tv.current with
  | some (Data.list ls) => some ls
  | _ => none

/-- Attempt to decode the current value as a typed value of type `α`.
    Returns `none` if the tape is empty, the path is invalid,
    or the `Data` at the path does not represent a valid value of type `α`. -/
public def currentAs (α : Type*) [StrEnc α] (tv : TapeView) : Option α :=
  tv.current.bind StrEnc.fromData

/-- Convert a `TapeView` to the corresponding `BiTape Char`. -/
public def toBiTape (tv : TapeView) : BiTape Char := sorry

@[simp]
public lemma toBiTape_empty : TapeView.empty.toBiTape = BiTape.mk₁ ['(', ')'] := by sorry

@[simp]
public lemma toBiTape_ofData (d : Data) :
    (TapeView.ofData d).toBiTape = BiTape.mk₁ (Data.enc d) := by sorry

@[simp]
public lemma toBiTape_ofEnc {α : Type*} [StrEnc α] (x : α) :
    (TapeView.ofEnc x).toBiTape = BiTape.mk₁ (StrEnc.enc x) := by sorry

@[simp]
public lemma toBiTape_data_empty_path (d : Data) :
    (TapeView.mk d []).toBiTape = BiTape.mk₁ (Data.enc d) := by sorry

public lemma toBiTape_injective : Function.Injective TapeView.toBiTape := by sorry

/-- Prepend a `Data` value to the front of a list on tape.
    If the path is `[]` and `data` is `Data.list ds`,
    returns `⟨Data.list (d :: ds), []⟩`.
    Otherwise, returns the `TapeView` unchanged. -/
@[expose]
public def pushList (d : Data) (tv : TapeView) : TapeView :=
  match tv with
  | ⟨Data.list ds, []⟩ => ⟨Data.list (d :: ds), []⟩
  | other => other

@[simp]
public lemma pushList_list {d : Data} {ds : List Data} :
    (TapeView.mk (Data.list ds) []).pushList d =
      TapeView.mk (Data.list (d :: ds)) [] := by
  unfold pushList; rfl

@[simp]
public lemma pushList_num {d : Data} {n : ℕ} {p : List ℕ} :
    (TapeView.mk (Data.num n) p).pushList d =
      TapeView.mk (Data.num n) p := by
  unfold pushList; rfl

@[simp]
public lemma pushList_nonempty_path {d : Data} {dat : Data}
    {k : ℕ} {rest : List ℕ} :
    (TapeView.mk dat (k :: rest)).pushList d =
      TapeView.mk dat (k :: rest) := by
  unfold pushList; cases dat with
  | num _ => rfl
  | list _ => rfl

public def asWritableList (tv : TapeView) : Option (List Data) :=
  match tv with
  | ⟨Data.list l, []⟩ => some l
  | _ => none

/-- Remove the first element from a list on tape. -/
public def popList (tv : TapeView) : TapeView :=
  (tv.asWritableList.map fun ls => TapeView.ofList ls.tail).getD tv

/-- If `tv` currently points at a non-empty list, returns its head, otherwise returns none. -/
public def currentListHead (tv : TapeView) : Option Data :=
  match tv.current with
  | Data.list (d :: _) => some d
  | _ => none

public def updateListHead (tv : TapeView) (f : Data → Data) : TapeView :=
  match tv with
  | ⟨Data.list (d :: ds), []⟩ => ⟨Data.list (f d :: ds), []⟩
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
