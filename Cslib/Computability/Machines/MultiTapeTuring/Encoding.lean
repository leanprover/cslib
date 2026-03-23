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

@[simp]
public lemma StrEnc.fromData_toData_apply (α : Type*) [StrEnc α] (x : α) :
    StrEnc.fromData (StrEnc.toData x) = some x := by
  apply StrEnc.fromData_toData

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
public lemma Bool.toData (d : Bool) :
  StrEnc.toData d = match d with | false => Data.num 0 | true => Data.num 1  := rfl

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
@[expose]
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

@[simp]
public lemma Data.atPath_append {d : Data} {path₁ path₂ : List ℕ} :
    d.atPath (path₁ ++ path₂) = d.atPath path₁ >>= fun d => d.atPath path₂ := by
  induction path₁ generalizing d with
  | nil => simp [Data.atPath]
  | cons k rest ih =>
    cases d with
    | num n => grind [Data.atPath]
    | list ds => grind [Data.atPath]

@[simp]
public lemma Data.atPath_dropLast_isSome_of_isSome {d : Data} {path : List ℕ}
    (h_is_some : (d.atPath path).isSome) :
  (d.atPath path.dropLast).isSome := by
  sorry

public lemma Data.atPath_isSome_of_le_isSome {d : Data} {i₁ i₂ : ℕ} (h_le : i₁ ≤ i₂)
  (h_is_some : (d.atPath [i₂]).isSome) :
  (d.atPath [i₁]).isSome := by
  sorry

-- TODO redundant?
@[simp]
public lemma Data.atPath_isSome_of_succ_isSome {d : Data} {idx : ℕ}
  (h_succ_is_some : (d.atPath [idx + 1]).isSome) :
  (d.atPath [idx]).isSome := by
  sorry



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

/-- The Data element currently pointed to by the head (at the path position).
Note that this is not tagged `@[simp]` because many preconditions on simp lemmas
use `(views i).current = ...`. -/
@[expose]
public def current (tv : TapeView) : Data :=
  (tv.data.atPath tv.path).get tv.h_path

@[simp]
public lemma current_append {data : Data} {path : List ℕ} {h : (data.atPath path).isSome} :
  (TapeView.mk data path h).current = (data.atPath path).get h := by simp [current]

@[simp]
public lemma mk_data_path (tv : TapeView) (h : (tv.data.atPath tv.path).isSome) :
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
public def appendPath (tv : TapeView) (idx : ℕ) (h : (tv.current.atPath [idx]).isSome) : TapeView :=
  ⟨tv.data, tv.path ++ [idx], by simpa using h⟩

/-- Attempt to decode the current value as a typed value of type `α`.
    Returns `none` if the tape is empty, the path is invalid,
    or the `Data` at the path does not represent a valid value of type `α`. -/
public def currentAs (α : Type*) [StrEnc α] (tv : TapeView) : Option α :=
  StrEnc.fromData tv.current

/-- The position of the head in the encoded version of the `TapeView`. -/
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
public lemma encodedPos_of_path_eq_nil (tv : TapeView) (h_path : tv.path = []) :
  tv.encodedPos = 0 := by
  unfold encodedPos
  split <;> simp_all

@[simp]
public lemma encodedPos_appendPath (tv : TapeView) (idx : ℕ)
    (h : (tv.data.atPath (tv.path ++ [idx])).isSome) :
  (TapeView.mk tv.data (tv.path ++ [idx]) h).encodedPos =
      tv.encodedPos + 1 + (((tv.currentList?.getD []).take idx).map fun d => d.enc.length).sum := by
  unfold encodedPos
  sorry
  -- obtain ⟨ds, h_current, h_idx⟩ := Data.isList_of_atPath_singleton_isSome h
  -- obtain ⟨data, path, h_valid⟩ := tv
  -- simp only [current, current_append] at h_current
  -- induction path generalizing data ds with
  -- | nil =>
  --   simp only [current, Data.atPath_nil, Option.get_some] at h_current
  --   subst h_current
  --   simp [appendPath, encodedPos, current]
  -- | cons p rest ih =>
  --   match data with
  --   | Data.num _ =>
  --     exfalso; simp [Data.atPath] at h_valid
  --   | Data.list ds' =>
  --     have h_p : p < ds'.length := by
  --       simp only [Data.atPath] at h_valid
  --       split at h_valid <;> simp_all
  --     simp only [current, current_append, Data.atPath_list_cons, h_p] at h_current
  --     have h_children : (TapeView.mk (Data.list ds') (p :: rest) h_valid).current.children = ds := by
  --       simp only [current, current_append, Data.atPath_list_cons, h_p]
  --       rw [show ((ds'[p].atPath rest).get h_valid).children =
  --         (Data.list ds).children from by rw [h_current]]
  --       simp [Data.children]
  --     rw [h_children]
  --     simp only [appendPath, encodedPos, List.cons_append, h_p, Nat.add_assoc]
  --     have h_valid' : (ds'[p].atPath rest).isSome := by
  --       simp [Data.atPath, h_p] at h_valid; exact h_valid
  --     have h_curr : (TapeView.mk ds'[p] rest h_valid').current = Data.list ds := by
  --       simp only [current, current_append]; exact h_current
  --     have h' : ((TapeView.mk ds'[p] rest h_valid').current.atPath [idx]).isSome := by
  --       rw [h_curr]; simp [Data.atPath, h_idx]
  --     have := ih ds h_idx _ h_valid' h' h_curr
  --     simp only [appendPath] at this
  --     omega

/-- Convert a `TapeView` to the corresponding `BiTape Char`. -/
@[expose]
public def toBiTape (tv : TapeView) : BiTape Char :=
  BiTape.move_right^[tv.encodedPos] (BiTape.mk₁ tv.data.enc)

@[simp]
public lemma toBiTape_ofData (d : Data) :
  (TapeView.ofData d).toBiTape = BiTape.mk₁ (Data.enc d) := by simp [toBiTape, encodedPos]

public def ofBiTape? (t : BiTape Char) : Option TapeView := sorry

@[expose]
public def ofBiTapes? {k : ℕ} (tapes : Fin k → BiTape Char) : Option (Fin k → TapeView) :=
  if h: ∀ i, (ofBiTape? (tapes i)).isSome then
    some (fun i => (ofBiTape? (tapes i)).get (h i))
  else none

@[simp]
public lemma toBiTape_ofBiTape (tv : TapeView) :
  (ofBiTape? tv.toBiTape) = tv := by sorry

@[simp]
public lemma toBiTape_comp_update {k : ℕ} {i : Fin k}
    {views : Fin k → TapeView} {tv : TapeView} :
  Function.update (TapeView.toBiTape ∘ views) i tv.toBiTape =
    TapeView.toBiTape ∘ (Function.update views i tv) := by
  ext j
  by_cases h : i = j
  · subst h; simp
  · simp only [Function.comp_apply, Function.update_apply]
    split <;> simp_all

@[simp]
public lemma ofBiTapes?_toBiTape {k : ℕ} {views : Fin k → TapeView} :
    TapeView.ofBiTapes? (TapeView.toBiTape ∘ views) = some views := by
  simp [ofBiTapes?]

@[simp]
public lemma ofBiTape_get_toBiTape (tape : BiTape Char) (h : (ofBiTape? tape).isSome) :
  ((ofBiTape? tape).get h).toBiTape = tape := by sorry

@[simp]
public lemma toBiTape_injective : Function.Injective TapeView.toBiTape := by sorry -- use the above

@[simp]
public lemma toBitape_of_appendPath (tv : TapeView) (idx : ℕ)
    (h : (tv.data.atPath (tv.path ++ [idx])).isSome) :
  (TapeView.mk tv.data (tv.path ++ [idx]) h).toBiTape =
    BiTape.move_right^[1 + (((tv.currentList?.getD []).take idx).map fun d => d.enc.length).sum]
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
  (tv.asWritableList.map fun ls => TapeView.ofList ls.tail).getD tv

/-- If `tv` currently points at a non-empty list, returns its head, otherwise returns none. -/
public def currentListHead (tv : TapeView) : Option Data :=
  match tv.current with
  | Data.list (d :: _) => some d
  | _ => none

public def updateListHead (tv : TapeView) (f : Data → Data) : TapeView :=
  match tv with
  | ⟨Data.list (d :: ds), [], _⟩ => ⟨Data.list (f d :: ds), [], rfl⟩
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
