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

/-- Head positioning. -/
public inductive HeadPos where
  /-- The head is positioned an the opening `(` -/
  | leftEnd
  /-- The head is positioned at the closing `)`. -/
  | rightEnd
  deriving DecidableEq

/-- A structured view of a tape that contains an encoding of `Data`.
- `data`: the content present on the tape, encoding using `Data.enc`.
- `path`: a navigation path into the `Data` value, pointing to the "current" value.
- `headPos`: the position of the head, either at the left or right end of the current value.
-/
@[ext]
public structure TapeView where
  /-- The `Data` value on the tape. -/
  data : Data
  /-- Navigation path into the `Data` value. -/
  path : List ℕ
  /-- The position of the head, either at the left or right end. -/
  headPos : HeadPos
  /-- The path is valid. -/
  h_path : (data.atPath path).isSome

instance : Inhabited TapeView := ⟨⟨Data.list [], [], .leftEnd, by rfl⟩⟩

namespace TapeView

/-- A tape containing a single Data value with the head at the start. -/
@[expose]
public abbrev ofData (d : Data) : TapeView := ⟨d, [], .leftEnd, by rfl⟩

/-- TODO document -/
@[expose]
public abbrev ofList (ls : List Data) : TapeView := ofData (Data.list ls)

/-- An "empty" tape (represented as an empty list), so it is actually not really empty. -/
@[expose]
public abbrev empty : TapeView := ofList []

/-- A tape containing a single typed value with the head at the start. -/
@[expose]
public abbrev ofEnc {α : Type*} [StrEnc α] (x : α) : TapeView :=
  ofData (StrEnc.toData x)

/-- The Data element currently pointed to by the head (at the path
    position). Note that this is not tagged `@[simp]` because many
    preconditions on simp lemmas use `(views i).current = ...`.
    Also note that the head can be at the left or right end of the current value. -/
@[expose]
public def current (tv : TapeView) : Data :=
  (tv.data.atPath tv.path).get tv.h_path

@[simp]
public lemma current_append {data : Data} {path : List ℕ} {pos : HeadPos}
    {h : (data.atPath path).isSome} :
  (TapeView.mk data path pos h).current =
    (data.atPath path).get h := by simp [current]

@[simp]
public lemma mk_data_path (tv : TapeView) (h : (tv.data.atPath tv.path).isSome) :
    TapeView.mk tv.data tv.path tv.headPos h = tv := by
  cases tv; rfl

-- TODO it looks weird to make that a simp. is it OK?
@[simp]
public lemma current_rev (tv : TapeView) :
  tv.data.atPath tv.path = tv.current := by simp [current]

/-- The current value as a list, if it is a `List`.
    Returns `none` if the tape is empty, the path is invalid,
    or the value at the path is not a `Data.list`. -/
@[expose]
public abbrev currentList (tv : TapeView) : List Data :=
  match tv.current with | .list ls => ls

/- Needed? -/
@[simp]
public lemma current_of_currentList (tv : TapeView) (ls : List Data)
    (h_currentList : tv.currentList = ls) :
  tv.current = Data.list ls := by grind

/-- TODO document -/
@[expose, simp]
public def parent (tv : TapeView) : TapeView :=
  match tv.path with
  | [] => tv
  | _ => ⟨tv.data, tv.path.dropLast, tv.headPos, by simp⟩

/-- TODO document -/
@[expose, simp]
public def appendPath (tv : TapeView) (idx : ℕ)
    (h : (tv.current.atPath [idx]).isSome) : TapeView :=
  ⟨tv.data, tv.path ++ [idx], tv.headPos, by simpa using h⟩

@[expose]
public abbrev toLeftEnd (tv : TapeView) : TapeView :=
  ⟨tv.data, tv.path, .leftEnd, tv.h_path⟩

@[expose]
public abbrev toRightEnd (tv : TapeView) : TapeView :=
  ⟨tv.data, tv.path, .rightEnd, tv.h_path⟩

/-- Attempt to decode the current value as a typed value of type `α`.
    Returns `none` if the tape is empty, the path is invalid,
    or the `Data` at the path does not represent a valid value of
    type `α`. -/
public def currentAs (α : Type*) [StrEnc α] (tv : TapeView) : Option α :=
  StrEnc.fromData tv.current

/-- The position of the head in the encoded version of the
    `TapeView`. -/
@[expose]
public def encodedPos : (tv : TapeView) → ℕ
  | ⟨_, [], .leftEnd, _⟩ => 0
  | ⟨d, [], .rightEnd, _⟩ => d.enc.length - 1
  | ⟨.list ds, p :: path, headPos, h_valid⟩ =>
      have h : p < ds.length := by grind [Data.atPath]
      1 +
        ((ds.take p).map fun d => d.enc.length).sum +
        encodedPos ⟨ds[p], path, headPos, by grind [Data.atPath]⟩
  termination_by tv => tv.path.length

@[simp]
public lemma encodedPos_of_path_eq_nil_left (tv : TapeView)
    (h_path : tv.path = [])
    (h_left : tv.headPos = .leftEnd) :
  tv.encodedPos = 0 := by
  unfold encodedPos
  split <;> simp_all

@[simp]
public lemma encodedPos_of_path_eq_nil_right (tv : TapeView)
    (h_path : tv.path = [])
    (h_left : tv.headPos = .rightEnd) :
  tv.encodedPos = tv.data.enc.length - 1 := by
  unfold encodedPos
  split <;> simp_all

@[simp]
public lemma encodedPos_appendPath (tv : TapeView) (idx : ℕ)
    (h : (tv.data.atPath (tv.path ++ [idx])).isSome) :
  (TapeView.mk tv.data (tv.path ++ [idx]) .leftEnd h).encodedPos =
      tv.encodedPos + 1 +
      ((tv.currentList.take idx).map fun d => d.enc.length).sum := by
  sorry

public lemma encodedPos_appendPath' (tv : TapeView) (idx : ℕ)
    (h_last : tv.path.getLast?.isSome)
    (h_left : tv.headPos = .leftEnd) :
  tv.encodedPos = tv.parent.encodedPos + 1 +
      ((tv.currentList.take (tv.path.getLast?.get h_last)).map fun d => d.enc.length).sum := by
  sorry

-- TODO clean up (ai)
/-- The encoding starting at `encodedPos` begins with `current.enc`. -/
private lemma enc_drop_prefix (tv : TapeView) (h_left : tv.headPos = .leftEnd) :
    tv.current.enc <+: tv.data.enc.drop tv.encodedPos := by
  match tv with
  | ⟨_, [], .leftEnd, h_path⟩ =>
    simp [current, Data.atPath]
  | ⟨d, [], .rightEnd, h_path⟩ =>
    simp at h_left
  | ⟨Data.list ds, p :: path, headPos, h_valid⟩ =>
    have hp : p < ds.length := by grind [Data.atPath]
    have h_path_valid : (ds[p].atPath path).isSome := by grind [Data.atPath]
    have ih := enc_drop_prefix ⟨ds[p], path, headPos, h_path_valid⟩ h_left
    have h_current : (⟨Data.list ds, p :: path, headPos, h_valid⟩ : TapeView).current =
        (⟨ds[p], path, headPos, h_path_valid⟩ : TapeView).current := by
      unfold current; simp [Data.atPath, hp]
    rw [h_current]; simp only [encodedPos, Data.enc_list]
    -- Strip the leading '('
    change _ <+: (['('] ++ (ds.map Data.enc).flatten ++ [')']).drop _
    rw [show ['('] ++ (ds.map Data.enc).flatten ++ [')'] =
        '(' :: ((ds.map Data.enc).flatten ++ [')']) from by simp,
      show 1 + ((ds.take p).map fun d => d.enc.length).sum +
        (⟨ds[p], path, headPos, h_path_valid⟩ : TapeView).encodedPos =
        (((ds.take p).map fun d => d.enc.length).sum +
        (⟨ds[p], path, headPos, h_path_valid⟩ : TapeView).encodedPos) + 1 from by omega,
      List.drop_succ_cons]
    -- Split flatten at position p
    have h_flatten_eq : (ds.map Data.enc).flatten =
        ((ds.take p).map Data.enc).flatten ++ ((ds.drop p).map Data.enc).flatten := by
      conv_lhs => rw [← List.take_append_drop p ds]
      simp only [List.map_append, List.flatten_append]
    have h_sum_eq : ((ds.take p).map fun d => d.enc.length).sum =
        ((ds.take p).map Data.enc).flatten.length := by
      rw [List.length_flatten, List.map_map]; rfl
    rw [h_flatten_eq, List.append_assoc]
    rw [show ((ds.take p).map fun d => d.enc.length).sum +
        (⟨ds[p], path, headPos, h_path_valid⟩ : TapeView).encodedPos =
        ((ds.take p).map Data.enc).flatten.length +
        (⟨ds[p], path, headPos, h_path_valid⟩ : TapeView).encodedPos from by omega]
    rw [List.drop_length_add_append,
      List.drop_eq_getElem_cons hp, List.map_cons, List.flatten_cons, List.append_assoc]
    rw [List.drop_append_of_le_length (by
        rcases ih with ⟨t, ht⟩
        have h_len := congrArg List.length ht
        simp only [List.length_drop, List.length_append] at h_len
        have := Data.enc_length_pos (⟨ds[p], path, headPos, h_path_valid⟩ : TapeView).current
        omega)]
    exact ih.trans (List.prefix_append ..)
  termination_by tv.path.length

-- TODO clean up (ai)
/-- `current.enc` is a slice of `data.enc` starting at `encodedPos`. -/
public lemma enc_current_slice (tv : TapeView) (h_left : tv.headPos = .leftEnd)
    (n : ℕ) (hn : n < tv.current.enc.length) :
    tv.data.enc[tv.encodedPos + n]? = some tv.current.enc[n] := by
  obtain ⟨suffix, h_suffix⟩ := enc_drop_prefix tv h_left
  have h1 : tv.data.enc[tv.encodedPos + n]? = (tv.current.enc ++ suffix)[n]? := by
    have := congrArg (·[n]?) h_suffix
    simp only [List.getElem?_drop] at this
    exact this.symm
  rw [h1, List.getElem?_append_left hn, List.getElem?_eq_getElem]

/-- Convert a `TapeView` to the corresponding `BiTape Char`. -/
@[expose]
public def toBiTape (tv : TapeView) : BiTape Char :=
  BiTape.move_right^[tv.encodedPos] (BiTape.mk₁ tv.data.enc)

-- TODO clean up (ai)
/-- Checking all chars of `v.enc` starting from the head of `toBiTape tv` is equivalent
    to `tv.current = v`. -/
public lemma ite_enc_condition_iff (tv : TapeView) (h_left : tv.headPos = .leftEnd) (v : Data) :
    (∀ n, (h : n < v.enc.length) →
      (BiTape.move_right^[n] tv.toBiTape).head = some v.enc[n]) ↔
    tv.current = v := by
  have key : ∀ n, (BiTape.move_right^[n] tv.toBiTape).head =
      tv.data.enc[tv.encodedPos + n]? := by
    intro n
    unfold toBiTape
    simp [← Function.iterate_add_apply, Nat.add_comm]
  simp only [key]
  constructor
  · intro h_match
    have h_eq_chars : ∀ n, (hn_c : n < tv.current.enc.length) → (hn_v : n < v.enc.length) →
        tv.current.enc[n] = v.enc[n] := by
      intro n hn_c hn_v
      have h1 := enc_current_slice tv h_left n hn_c
      have h2 := h_match n hn_v
      rw [h1] at h2; exact Option.some_injective _ h2
    suffices h : tv.current.enc <+: v.enc ∨ v.enc <+: tv.current.enc by
      rcases h with h | h
      · exact Data.enc_prefix_free h
      · exact (Data.enc_prefix_free h).symm
    have h_prefix : ∀ {a b : List Char}, a.length ≤ b.length →
        (∀ n, (hn_a : n < a.length) → (hn_b : n < b.length) → a[n] = b[n]) → a <+: b := by
      intro a b h_len h_eq
      rw [List.prefix_iff_eq_take]
      exact List.ext_getElem (by simp; omega) fun n h1 h2 => by
        simp only [List.getElem_take]; exact h_eq n (by omega) (by omega)
    by_cases h_len : tv.current.enc.length ≤ v.enc.length
    · exact Or.inl (h_prefix h_len h_eq_chars)
    · exact Or.inr (h_prefix (by omega) fun n h1 h2 => (h_eq_chars n h2 h1).symm)
  · intro h_eq; subst h_eq; exact fun n hn => enc_current_slice tv h_left n hn

@[simp]
public lemma toBiTape_ofData (d : Data) :
  (TapeView.ofData d).toBiTape = BiTape.mk₁ (Data.enc d) := by
  simp [toBiTape]

/-- TODO document -/
public def ofBiTape? (t : BiTape Char) : Option TapeView := sorry

/-- TODO document -/
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
    (h_left : tv.headPos = .leftEnd)
    (h : (tv.data.atPath (tv.path ++ [idx])).isSome) :
  (TapeView.mk tv.data (tv.path ++ [idx]) tv.headPos h).toBiTape =
    BiTape.move_right^[1 +
      ((tv.currentList.take idx).map fun d => d.enc.length).sum]
      tv.toBiTape := by
  unfold toBiTape
  simp [h_left, ←Function.iterate_add_apply]
  grind

/-- Prepend a `Data` value to the front of a list on tape.
    If the path is `[]` and `data` is `Data.list ds`,
    returns `⟨Data.list (d :: ds), [], _⟩`.
    Otherwise, returns the `TapeView` unchanged. -/
@[expose]
public def pushList (d : Data) (tv : TapeView) : TapeView :=
  match tv with
  | ⟨Data.list ds, [], headPos, _⟩ => ⟨Data.list (d :: ds), [], headPos, rfl⟩
  | other => other

@[simp]
public lemma pushList_list {d : Data} {ds : List Data} {headPos : HeadPos} :
    (TapeView.mk (Data.list ds) [] headPos rfl).pushList d =
      TapeView.mk (Data.list (d :: ds)) [] headPos rfl := by
  unfold pushList; rfl

@[simp]
public lemma pushList_nonempty_path {tv : TapeView} (h_nonempty : tv.path ≠ []) :
    tv.pushList d = tv := by  unfold pushList; split <;> grind

/-- TODO document -/
public def asWritableList (tv : TapeView) : Option (List Data) :=
  match tv with
  | ⟨Data.list l, [], _, _⟩ => some l
  | _ => none

/-- Remove the first element from a list on tape. -/
public def popList (tv : TapeView) : TapeView :=
  (tv.asWritableList.map fun ls => TapeView.ofList ls.tail).getD tv

/-- If `tv` currently points at a non-empty list, returns its head,
    otherwise returns none. -/
public def currentListHead (tv : TapeView) : Option Data :=
  match tv.current with
  | Data.list (d :: _) => some d
  | _ => none

/-- TODO document -/
public def updateListHead (tv : TapeView)
    (f : Data → Data) : TapeView :=
  match tv with
  | ⟨Data.list (d :: ds), [], headPos, _⟩ =>
    ⟨Data.list (f d :: ds), [], headPos, rfl⟩
  | other => other

/-- TODO document -/
public def updateListHeadTyped
    {α β : Type} [StrEnc α] [StrEnc β]
    (tv : TapeView) (f : α → β) : TapeView := (do
  let ls <- tv.asWritableList
  let d <- ls.head?
  let x <- StrEnc.fromData d
  return TapeView.ofList ((StrEnc.toData (f x)) :: ls.tail)).getD tv

-- /-- Checking all chars of `v.enc` starting from the head of `toBiTape tv` is equivalent
--     to `tv.current = v`. -/
-- public lemma ite_enc_condition_iff' (tv : TapeView) (v : Data) :
--   (∀ n, (h : n < v.enc.length) → (BiTape.move_right^[n] tv.toBiTape).head = some v.enc[n]) ↔
--     tv.current = v := by
--   have key : ∀ n, (BiTape.move_right^[n] tv.toBiTape).head = tv.data.enc[tv.encodedPos + n]? := by
--     intro n
--     unfold toBiTape
--     simp [← Function.iterate_add_apply, Nat.add_comm]
--   constructor
--   · intro h
--     simp [key] at h






--     sorry
--   · sorry


end TapeView

end Turing
