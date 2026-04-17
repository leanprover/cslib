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

public lemma HeadPos.eq_rightEnd_of_ne_leftEnd {hp : HeadPos}
    (h : ¬hp = .leftEnd) : hp = .rightEnd := by
  cases hp <;> simp_all

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

@[simp]
public lemma current_atPath_length_sub_one_isSome_of_non_empty (tv : TapeView)
    (h_nonempty : ¬ tv.current = .list []) :
  (tv.current.atPath [tv.current.toList.length - 1]).isSome := by
  sorry

/-- TODO document -/
@[expose, simp]
public def parent (tv : TapeView) : TapeView := ⟨tv.data, tv.path.dropLast, tv.headPos, by simp⟩

-- @[simp]
-- public lemma parent_data (tv : TapeView) : tv.parent.data = tv.data := by
--   unfold parent
--   split <;> simp

-- @[simp]
-- public lemma parent_path (tv : TapeView) : tv.parent.path = tv.path.dropLast := by
--   unfold parent
--   split <;> grind

-- @[simp]
-- public lemma parent_headPos (tv : TapeView) : tv.parent.headPos = tv.headPos := by
--   unfold parent
--   split <;> grind

/-- TODO don't use, I think it is unnatural to keep the headPos -/
@[expose, simp]
public def appendPath (tv : TapeView) (idx : ℕ)
    (h : (tv.current.atPath [idx]).isSome) : TapeView :=
  ⟨tv.data, tv.path ++ [idx], tv.headPos, by simpa using h⟩

/-- Like `appendPath` but always sets `headPos` to `.leftEnd`. -/
@[expose, simp]
public def appendPath' (tv : TapeView) (idx : ℕ)
    (h : (tv.current.atPath [idx]).isSome) : TapeView :=
  ⟨tv.data, tv.path ++ [idx], .leftEnd, by simpa using h⟩

/-- Copy the `headPos` from `tv'` into `tv`, keeping all other fields. -/
@[expose]
public abbrev setHeadPosOf (tv tv' : TapeView) : TapeView :=
  ⟨tv.data, tv.path, tv'.headPos, tv.h_path⟩

@[simp]
public lemma setHeadPosOf_of_eq (tv tv' : TapeView) (h_eq : tv'.headPos = tv.headPos) :
    tv.setHeadPosOf tv' = tv := by
  simp [setHeadPosOf, h_eq]

/-- Return a copy of the `TapeView` with the head positioned at the left end. -/
@[expose]
public abbrev toLeftEnd (tv : TapeView) : TapeView :=
  ⟨tv.data, tv.path, .leftEnd, tv.h_path⟩

@[simp]
public lemma toLeftEnd_of_leftEnd (tv : TapeView)
    (h : tv.headPos = .leftEnd) : tv.toLeftEnd = tv := by
  ext <;> simp_all

/-- Return a copy of the `TapeView` with the head positioned at the right end. -/
@[expose]
public abbrev toRightEnd (tv : TapeView) : TapeView :=
  ⟨tv.data, tv.path, .rightEnd, tv.h_path⟩

@[simp]
public lemma toRightEnd_of_rightEnd (tv : TapeView)
    (h : tv.headPos = .rightEnd) : tv.toRightEnd = tv := by
  ext <;> simp_all

@[simp]
public lemma toLeftEnd_toRightEnd (tv : TapeView) :
  tv.toLeftEnd.toRightEnd = tv.toRightEnd := by
  ext <;> simp_all

@[simp]
public lemma toRightEnd_toLeftEnd (tv : TapeView) :
  tv.toRightEnd.toLeftEnd = tv.toLeftEnd := by
  ext <;> simp_all

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
      ((match tv.current with | .list ls => ls.take idx).map fun d : Data => d.enc.length).sum := by
  sorry

public lemma encodedPos_appendPath' (tv : TapeView) (idx : ℕ)
    (h_last : tv.path.getLast?.isSome)
    (h_left : tv.headPos = .leftEnd) :
  tv.encodedPos = tv.parent.encodedPos + 1 +
      ((match tv.current with | .list ls => ls.take (tv.path.getLast?.get h_last)).map
          fun d : Data => d.enc.length).sum := by
  sorry

/-- Taking one more element adds the next element's encoding length to the sum. -/
private lemma sum_map_enc_length_take_succ (ds : List Data) (idx : ℕ) (h : idx < ds.length) :
    ((ds.take (idx + 1)).map fun d => d.enc.length).sum =
    ((ds.take idx).map fun d => d.enc.length).sum + ds[idx].enc.length := by
  induction ds generalizing idx with
  | nil => simp at h
  | cons d ds ih =>
    cases idx with
    | zero => simp
    | succ n =>
      simp only [List.take_succ_cons, List.map_cons, List.sum_cons, List.getElem_cons_succ]
      rw [ih n (by simp at h; omega)]; omega

/-- At rightEnd of the last child, moving one position right reaches the parent's rightEnd. -/
public lemma encodedPos_last_child_succ : (tv : TapeView) →
    (h_last : tv.path.getLast? = some idx) →
    (h_right : tv.headPos = .rightEnd) →
    (h_no_next : ¬((tv.parent.current.atPath [idx.succ]).isSome)) →
    tv.encodedPos + 1 = tv.parent.toRightEnd.encodedPos := by
  intro ⟨d, path, headPos, h_valid⟩
  induction path generalizing d headPos with
  | nil => intro h_last; simp at h_last
  | cons p tail ih =>
    intro h_last h_right h_no_next
    subst h_right
    let .list ds := d
    cases tail with
    | nil =>
      have h_idx : idx = p := by grind
      subst h_idx
      have h_p : idx < ds.length := by grind [Data.atPath]
      have h_idx_last : idx + 1 ≥ ds.length := by
        simp [parent, current, Data.atPath] at h_no_next; omega
      have h_sum : ((ds.take idx).map fun d => d.enc.length).sum + ds[idx].enc.length =
          (ds.map fun d => d.enc.length).sum := by
        have hsplit : ds = ds.take idx ++ ds.drop idx := by simp
        conv_rhs => rw [hsplit, List.map_append, List.sum_append]
        congr 1
        rw [List.drop_eq_getElem_cons h_p, show idx + 1 = ds.length from by omega,
          List.drop_length, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
      simp only [parent, toRightEnd, show [idx].dropLast = ([] : List ℕ) from rfl,
        encodedPos, Data.enc_list, List.length_append, List.length_singleton,
        List.length_flatten, List.map_map, List.map_take]
      conv_rhs => rw [show (List.length ∘ Data.enc) = (fun d => d.enc.length) from rfl]
      rw [← List.map_take]
      have := Data.enc_length_pos ds[idx]
      omega
    | cons r rest =>
      have h_p : p < ds.length := by grind [Data.atPath]
      have h_sub : (ds[p].atPath (r :: rest)).isSome := by grind [Data.atPath]
      have h_last' : (r :: rest).getLast? = some idx := by
        simpa [List.getLast?_cons_cons] using h_last
      have h_drop : (p :: r :: rest).dropLast = p :: (r :: rest).dropLast := by
        simp [List.dropLast_cons_of_ne_nil]
      conv_lhs => lhs; unfold encodedPos; simp [h_p]
      simp only [parent, h_drop]
      conv_rhs => rw [toRightEnd]; unfold encodedPos; simp [h_p]
      have ih := ih ds[p] .rightEnd h_sub h_last' rfl (by
          convert h_no_next using 2; simp [parent, current, h_p, h_drop])
      simp only [parent, toRightEnd] at ih; omega

/-- At rightEnd of a non-last child, moving right reaches the next sibling's leftEnd. -/
public lemma encodedPos_next_sibling_succ : (tv : TapeView) →
    (h_last : tv.path.getLast? = some idx) →
    (h_right : tv.headPos = .rightEnd) →
    (h_next : (tv.parent.current.atPath [idx.succ]).isSome) →
    tv.encodedPos + 1 = (tv.parent.appendPath' idx.succ h_next).encodedPos
  | ⟨.list ds, [p], .rightEnd, h_valid⟩, h_last, _, h_next => by
    have h_idx : idx = p := by simp [List.getLast?] at h_last; exact h_last.symm
    subst h_idx
    have h_p : idx < ds.length := by grind [Data.atPath]
    have h_p' : idx + 1 < ds.length := by
      simp [parent, current, Data.atPath] at h_next; omega
    conv_lhs => lhs; unfold encodedPos; simp [h_p]
    simp only [parent, appendPath']
    conv_rhs => unfold encodedPos; simp [h_p']; unfold encodedPos; simp
    simp only [← List.map_take]
    rw [sum_map_enc_length_take_succ ds idx h_p]
    have := Data.enc_length_pos ds[idx]; omega
  | ⟨.list ds, p :: r :: rest, .rightEnd, h_valid⟩, h_last, _, h_next => by
    have h_p : p < ds.length := by grind [Data.atPath]
    have h_sub : (ds[p].atPath (r :: rest)).isSome := by grind [Data.atPath]
    have h_last' : (r :: rest).getLast? = some idx := by
      simpa [List.getLast?_cons_cons] using h_last
    have h_drop : (p :: r :: rest).dropLast = p :: (r :: rest).dropLast := by
      simp [List.dropLast_cons_of_ne_nil]
    conv_lhs => lhs; unfold encodedPos; simp [h_p]
    simp only [parent, h_drop, appendPath']
    conv_rhs => unfold encodedPos; simp [h_p]
    exact (encodedPos_next_sibling_succ
      ⟨ds[p], r :: rest, .rightEnd, h_sub⟩ h_last' rfl (by
        convert h_next using 2; simp [parent, current, h_p, h_drop])) ▸ rfl
  termination_by tv => tv.path.length

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

/-- The rightEnd encodedPos is the leftEnd encodedPos plus current.enc.length - 1. -/
private lemma encodedPos_toRightEnd : (tv : TapeView) →
    tv.toRightEnd.encodedPos = tv.toLeftEnd.encodedPos + (tv.current.enc.length - 1)
  | ⟨.list ds, [], _, _⟩ => by
    simp [toRightEnd, toLeftEnd, current, Data.atPath]
  | ⟨.list ds, p :: path, hp, h_valid⟩ => by
    have h_p : p < ds.length := by grind [Data.atPath]
    have h_sub : (ds[p].atPath path).isSome := by grind [Data.atPath]
    have ih := encodedPos_toRightEnd ⟨ds[p], path, hp, h_sub⟩
    have h_current : (⟨Data.list ds, p :: path, hp, h_valid⟩ : TapeView).current =
        (⟨ds[p], path, hp, h_sub⟩ : TapeView).current := by
      simp [current, Data.atPath, h_p]
    rw [h_current]
    simp only [toRightEnd, toLeftEnd] at ih ⊢
    conv_lhs => unfold encodedPos; simp only [h_p, ↓reduceDIte]
    conv_rhs =>
      lhs; unfold encodedPos; simp only [h_p, ↓reduceDIte]
    omega
  termination_by tv => tv.path.length

/-- Convert a `TapeView` to the corresponding `BiTape Char`. -/
@[expose]
public def toBiTape (tv : TapeView) : BiTape Char :=
  BiTape.move_right^[tv.encodedPos] (BiTape.mk₁ tv.data.enc)

/-- Moving right on a TapeView's BiTape equals the BiTape of the target TapeView,
    given matching data and successor encodedPos. -/
public lemma toBiTape_move_right_eq (tv target : TapeView)
    (h_data : tv.data = target.data)
    (h_enc : tv.encodedPos + 1 = target.encodedPos) :
    tv.toBiTape.move_right = target.toBiTape := by
  simp only [toBiTape, h_data]
  rw [← h_enc, Nat.add_comm, Function.iterate_add_apply, Function.iterate_one]

/-- At leftEnd, the head of the BiTape reads `'('`. -/
@[simp]
public lemma toBiTape_head_leftEnd (tv : TapeView)
    (h_left : tv.headPos = .leftEnd) :
    tv.toBiTape.head = some '(' := by
  simp only [toBiTape, BiTape.head_iterate_move_right_mk₁]
  have h := enc_current_slice tv h_left 0 (Data.enc_length_pos tv.current)
  simp only [Nat.add_zero] at h
  rw [h]; simp

/-- At rightEnd, the head of the BiTape reads `')'`. -/
@[simp]
public lemma toBiTape_head_rightEnd (tv : TapeView)
    (h_right : tv.headPos = .rightEnd) :
    tv.toBiTape.head = some ')' := by
  simp only [toBiTape, BiTape.head_iterate_move_right_mk₁]
  have h_pos := encodedPos_toRightEnd tv
  have h_right_eq : tv.toRightEnd.encodedPos = tv.encodedPos := by
    congr 1; cases tv; simp_all [toRightEnd]
  rw [h_right_eq] at h_pos
  rw [h_pos]
  -- Goal: tv.data.enc[tv.toLeftEnd.encodedPos + (tv.current.enc.length - 1)]?
  --       = some ')'
  -- Use enc_current_slice with n = tv.current.enc.length - 1
  exact (enc_current_slice tv.toLeftEnd rfl
    (tv.toLeftEnd.current.enc.length - 1)
    (by have := Data.enc_length_pos tv.toLeftEnd.current; omega)).trans
    (by simp [Data.enc_getElem_last])

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

/-- At rightEnd, moving left `current.enc.length - 1` and checking `v.enc` is equivalent
    to `current = v`. -/
public lemma ite_enc_condition_right_iff (tv : TapeView) (h_right : tv.headPos = .rightEnd)
    (v : Data) :
    (∀ n, (h : n < v.enc.length) →
      (BiTape.move_right^[n]
        (BiTape.move_left^[v.enc.length - 1] tv.toBiTape)).head = some v.enc[n]) ↔
    tv.current = v := by
  -- Key: move_left/move_right cancellation
  have bi_li : Function.LeftInverse (BiTape.move_left (Symbol := Char)) BiTape.move_right :=
    fun t => BiTape.move_right_move_left t
  -- Position info
  have h_pos := encodedPos_toRightEnd tv
  have h_re : tv.toRightEnd.encodedPos = tv.encodedPos := by
    congr 1; cases tv; simp_all [toRightEnd]
  rw [h_re] at h_pos
  -- h_pos : tv.encodedPos = tv.toLeftEnd.encodedPos + (tv.current.enc.length - 1)
  have h_cenc := Data.enc_length_pos tv.current
  have h_venc := Data.enc_length_pos v
  -- Unfold toBiTape
  have h_unfold : tv.toBiTape =
      BiTape.move_right^[tv.encodedPos] (BiTape.mk₁ tv.data.enc) := by
    simp [toBiTape]
  rw [h_unfold]
  -- Cancel helper: when m ≤ ep, iterate cancellation gives getElem?
  have cancel_head (m ep : ℕ) (hle : m ≤ ep) (l : List Char) (n : ℕ) :
      (BiTape.move_right^[n] (BiTape.move_left^[m]
        (BiTape.move_right^[ep] (BiTape.mk₁ l)))).head =
      l[ep - m + n]? := by
    rw [show ep = m + (ep - m) from by omega, Function.iterate_add_apply,
      bi_li.iterate m, ← Function.iterate_add_apply,
      BiTape.head_iterate_move_right_mk₁]
    congr 1; omega
  -- move_left past tape start gives None
  have move_left_past_start : ∀ (l : List Char) (j : ℕ), 0 < j →
      (BiTape.move_left^[j] (BiTape.mk₁ l)).head = none := by
    intro l j hj
    suffices ∀ j, ∀ (t : BiTape Char), t.left = ∅ → 0 < j →
        (BiTape.move_left^[j] t).head = none ∧ (BiTape.move_left^[j] t).left = ∅ from
      (this j _ (by simp [BiTape.mk₁, StackTape.empty_eq_nil]) hj).1
    intro j
    induction j with
    | zero => intro t ht hj; omega
    | succ j ih =>
      intro t ht hj
      rw [Function.iterate_succ, Function.comp_apply]
      have h1 : t.move_left.head = none := by
        simp [BiTape.move_left, ht, StackTape.nil_head, StackTape.empty_eq_nil]
      have h2 : t.move_left.left = ∅ := by
        simp [BiTape.move_left, ht, StackTape.empty_eq_nil, StackTape.nil_tail]
      cases j with
      | zero => exact ⟨h1, h2⟩
      | succ j => exact ih t.move_left h2 (by omega)
  constructor
  · -- Forward: reads match v.enc → current = v
    intro h_match
    -- Step 1: v.enc.length - 1 ≤ tv.encodedPos
    have h_le : v.enc.length - 1 ≤ tv.encodedPos := by
      by_contra h_gt; push_neg at h_gt
      have h0 := h_match 0 h_venc
      simp only [Function.iterate_zero, Function.id_def] at h0
      rw [show v.enc.length - 1 =
          (v.enc.length - 1 - tv.encodedPos) + tv.encodedPos from by omega,
        Function.iterate_add_apply, bi_li.iterate tv.encodedPos] at h0
      rw [move_left_past_start _ _ (by omega)] at h0
      exact absurd h0 (by simp)
    -- Step 2: Simplify h_match
    have h_match' : ∀ n, (hn : n < v.enc.length) →
        tv.data.enc[tv.encodedPos - (v.enc.length - 1) + n]? = some v.enc[n] := by
      intro n hn
      have := h_match n hn
      rw [cancel_head _ _ h_le _ _] at this
      exact this
    -- Step 3: Build suffix relation
    suffices h : tv.current.enc <:+ v.enc ∨ v.enc <:+ tv.current.enc by
      rcases h with h | h
      · exact Data.enc_suffix_free h
      · exact (Data.enc_suffix_free h).symm
    by_cases h_len : v.enc.length ≤ tv.current.enc.length
    · -- v.enc <:+ current.enc
      right
      refine ⟨tv.current.enc.take (tv.current.enc.length - v.enc.length),
        List.ext_getElem (by simp; omega) fun n h1 h2 => ?_⟩
      by_cases hn : n < tv.current.enc.length - v.enc.length
      · rw [List.getElem_append_left (by simp; omega)]
        exact (List.getElem_take' h2 hn).symm
      · push_neg at hn
        rw [List.getElem_append_right (by simp; omega)]
        simp only [List.length_take_of_le (by omega : tv.current.enc.length - v.enc.length ≤
            tv.current.enc.length)]
        have r1 := enc_current_slice tv.toLeftEnd rfl n h2
        have r2 := h_match' (n - (tv.current.enc.length - v.enc.length)) (by omega)
        rw [show tv.encodedPos - (v.enc.length - 1) +
            (n - (tv.current.enc.length - v.enc.length)) =
            tv.toLeftEnd.encodedPos + n by omega] at r2
        rw [r1] at r2; exact (Option.some_injective _ r2).symm
    · -- current.enc <:+ v.enc
      push_neg at h_len
      left
      refine ⟨v.enc.take (v.enc.length - tv.current.enc.length),
        List.ext_getElem (by simp; omega) fun n h1 h2 => ?_⟩
      by_cases hn : n < v.enc.length - tv.current.enc.length
      · rw [List.getElem_append_left (by simp; omega)]
        exact (List.getElem_take' h2 hn).symm
      · push_neg at hn
        rw [List.getElem_append_right (by simp; omega)]
        simp only [List.length_take_of_le (by omega : v.enc.length - tv.current.enc.length ≤
            v.enc.length)]
        have h_idx : n - (v.enc.length - tv.current.enc.length) <
            tv.current.enc.length := by omega
        have r1 := enc_current_slice tv.toLeftEnd rfl
          (n - (v.enc.length - tv.current.enc.length)) h_idx
        have r2 := h_match' n h2
        rw [show tv.encodedPos - (v.enc.length - 1) + n =
            tv.toLeftEnd.encodedPos +
              (n - (v.enc.length - tv.current.enc.length)) by omega] at r2
        rw [r1] at r2; exact Option.some_injective _ r2
  · -- Backward: current = v → reads match
    intro h_eq; subst h_eq
    intro n hn
    rw [cancel_head _ _ (by omega) _ _,
      show tv.encodedPos - (tv.current.enc.length - 1) = tv.toLeftEnd.encodedPos by omega]
    exact enc_current_slice tv.toLeftEnd rfl n hn

@[simp]
public lemma toBiTape_ofData (d : Data) :
  (TapeView.ofData d).toBiTape = BiTape.mk₁ (Data.enc d) := by
  simp [toBiTape]

@[simp]
public lemma toBiTape_toRightEnd (tv : TapeView) :
  tv.toRightEnd.toBiTape = BiTape.move_right^[tv.current.enc.length - 1] tv.toLeftEnd.toBiTape := by
  simp only [toBiTape, toRightEnd, toLeftEnd, ← Function.iterate_add_apply]
  congr 1
  have h := encodedPos_toRightEnd tv
  simp only [toRightEnd, toLeftEnd] at h
  omega

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

/-- Combined: moving right on tape `i` and updating equals updating with the target TapeView. -/
public lemma toBiTape_comp_update_move_right {k : ℕ} {i : Fin k}
    {views : Fin k → TapeView} {target : TapeView}
    (h_data : (views i).data = target.data)
    (h_enc : (views i).encodedPos + 1 = target.encodedPos) :
    Function.update (toBiTape ∘ views) i (views i).toBiTape.move_right =
      toBiTape ∘ Function.update views i target := by
  rw [toBiTape_move_right_eq _ _ h_data h_enc, toBiTape_comp_update]

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
  (TapeView.mk tv.data (tv.path ++ [idx]) HeadPos.leftEnd h).toBiTape =
    BiTape.move_right^[1 +
      ((tv.current.toList.take idx).map fun d : Data => d.enc.length).sum]
      tv.toBiTape := by
  unfold toBiTape
  simp [←Function.iterate_add_apply, Data.toList, -List.map_take]
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


end TapeView

end Turing
