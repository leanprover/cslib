module

public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Algebra.Group.Nat.Defs

/-!
# Longest Common Sublist (Subsequence)

Two implementations, `lcsBrute` and `lcsDP`, of the longest common sublist (LCS) algorithm are
provided. Their unit tests take the form of `#guard_msgs in #eval`. There could be multiple LCS for
two given lists. We consistently yield an *opinionated* one among many.

## Main results

- `lcsBrute_correct`: The correctness proof of the slow-recursive implementation `lcsBrute`.
- `lcsDP_eq_lcsBrute`: The functional equality between `lcsDP` and `lcsBrute`.
- `lcsDP_correct`: The correctness proof of the dynamic programming implementation `lcsDP`.
- `lcsDP_time`: The number of calls to `lcsDPM.dp` is proportional to the product of the length of
  the two input lists.
-/

set_option autoImplicit false

def test_string (lcs : List Char → List Char → List Char) (s t : String) : String :=
  .ofList <| lcs s.toList t.toList

namespace List

variable {α} [DecidableEq α]

/-- `cs` is a common sublist of the lists `xs` and `ys`. -/
public structure CommonSublist (xs ys cs : List α) : Prop where
  sublist₁ : cs <+ xs
  sublist₂ : cs <+ ys

/-- `lcs` is a longest common sublist of the lists `xs` and `ys`. -/
public structure LCS (xs ys lcs : List α) : Prop extends CommonSublist xs ys lcs where
  longest : ∀ cs, CommonSublist xs ys cs → cs.length ≤ lcs.length

/-- Straightforward recursion but slow: not even the length of LCS is cached. -/
def lcsBrute : List α → List α → List α
  | [], _
  | _, [] => []
  | x :: xs, y :: ys =>
    if x = y then
      x :: lcsBrute xs ys
    else
      let xx := lcsBrute xs (y :: ys)
      let yy := lcsBrute (x :: xs) ys
      if xx.length ≥ yy.length then xx else yy

section unittest

/-- info: "" -/
#guard_msgs(info) in
#eval test_string lcsBrute "" ""

/-- info: "" -/
#guard_msgs(info) in
#eval test_string lcsBrute "ABCD" ""

/-- info: "" -/
#guard_msgs(info) in
#eval test_string lcsBrute "" "ACBAD"

/-- info: "ACD" -/
#guard_msgs(info) in
#eval test_string lcsBrute "ABCD" "ACBAD"

/-- info: "AC" -/
#guard_msgs(info) in
#eval test_string lcsBrute "GAC" "AGCAT"

/-- info: "MJAU" -/
#guard_msgs(info) in
#eval test_string lcsBrute "XMJYAUZ" "MZJAWXU"

end unittest

theorem nil_lcsBrute : {ys : List α} → lcsBrute [] ys = []
  | [] | _ :: _ => lcsBrute.eq_def ..

theorem lcsBrute_nil : {xs : List α} → lcsBrute xs [] = []
  | [] | _ :: _ => lcsBrute.eq_def ..

theorem lcsBrute_correct : {xs ys : List α} → LCS xs ys (lcsBrute xs ys)
  | [], ys =>
    suffices LCS [] ys [] from nil_lcsBrute.symm.rec this
    {
      sublist₁ := show [] <+ [] from .slnil
      sublist₂ := show [] <+ ys from ys.nil_sublist
      longest
      | cs, ⟨(h : cs <+ []), _⟩ =>
        show cs.length ≤ [].length from
        suffices cs = [] from this.rec Nat.le.refl
        eq_nil_of_sublist_nil h
    }
  | xs, [] =>
    suffices LCS xs [] [] from lcsBrute_nil.symm.rec this
    {
      sublist₁ := show [] <+ xs from xs.nil_sublist
      sublist₂ := show [] <+ [] from .slnil
      longest
      | cs, ⟨_, (h : cs <+ [])⟩ =>
        show cs.length ≤ [].length from
        suffices cs = [] from this.rec Nat.le.refl
        eq_nil_of_sublist_nil h
    }
  | x :: xs, y :: ys =>
    if h₁ : x = y then
      let xy := lcsBrute xs ys ; have hxy : LCS xs ys xy := lcsBrute_correct
      suffices LCS (x :: xs) (y :: ys) (x :: xy) by rw [lcsBrute, if_pos h₁] ; exact this
      {
        sublist₁ := show x :: xy <+ x :: xs from hxy.sublist₁.cons₂ x
        sublist₂ := show x :: xy <+ y :: ys from h₁ ▸ hxy.sublist₂.cons₂ y
        longest
        | [], _ => show [].length ≤ _ from Nat.zero_le _
        | c :: cs, ⟨(hx : c :: cs <+ x :: xs), (hy : c :: cs <+ y :: ys)⟩ =>
          show (c :: cs).length ≤ (x :: xy).length from
          suffices cs.length ≤ xy.length from Nat.succ_le_succ this
          hxy.longest cs ⟨hx.of_cons_cons, hy.of_cons_cons⟩
      }
    else
      let xx := lcsBrute xs (y :: ys) ; have hxx : LCS xs (y :: ys) xx := lcsBrute_correct
      let yy := lcsBrute (x :: xs) ys ; have hyy : LCS (x :: xs) ys yy := lcsBrute_correct
      if h₂ : xx.length ≥ yy.length then
        suffices LCS (x :: xs) (y :: ys) xx by rw [lcsBrute, if_neg h₁, if_pos h₂] ; exact this
        {
          hxx with
          sublist₁ := show xx <+ x :: xs from hxx.sublist₁.cons x
          longest
          | cs, ⟨(hx : cs <+ x :: xs), (hy : cs <+ y :: ys)⟩ =>
            match sublist_cons_iff.mp hx with
            | .inl (h : cs <+ xs) => show cs.length ≤ xx.length from hxx.longest cs ⟨h, hy⟩
            | .inr ⟨_, (h : cs = x :: _), _⟩ =>
              have : cs <+ ys :=
                match sublist_cons_iff.mp hy with
                | .inl h => h
                | .inr ⟨_, (e : cs = y :: _), _⟩ =>
                  suffices x = y from absurd this h₁
                  cons.inj (h.symm.trans e) |>.left
              calc cs.length
              _  ≤ yy.length := hyy.longest cs ⟨hx, this⟩
              _  ≤ xx.length := h₂
        }
      else
        suffices LCS (x :: xs) (y :: ys) yy by rw [lcsBrute, if_neg h₁, if_neg h₂] ; exact this
        {
          hyy with
          sublist₂ := show yy <+ y :: ys from hyy.sublist₂.cons y
          longest
          | cs, ⟨(hx : cs <+ x :: xs), (hy : cs <+ y :: ys)⟩ =>
            match sublist_cons_iff.mp hy with
            | .inl (h : cs <+ ys) => show cs.length ≤ yy.length from hyy.longest cs ⟨hx, h⟩
            | .inr ⟨_, (h : cs = y :: _), _⟩ =>
              have : cs <+ xs :=
                match sublist_cons_iff.mp hx with
                | .inl h => h
                | .inr ⟨_, (e : cs = x :: _), _⟩ =>
                  suffices x = y from absurd this h₁
                  cons.inj (e.symm.trans h) |>.left
              calc cs.length
              _  ≤ xx.length := hxx.longest cs ⟨this, hy⟩
              _  ≤ yy.length := Nat.le_of_not_ge h₂
        }

namespace lcsDP

structure DP α where
  lcs : List α
  length : Nat
  length_eq : lcs.length = length

scoped instance : Inhabited (DP α) where default := ⟨[], 0, rfl⟩
example : @Eq (DP α) default ⟨[], 0, rfl⟩ := rfl
abbrev DPS α := List (α × DP α)
example : @Eq (DPS α × DP α × DP α) default ([], ⟨[], 0, rfl⟩, ⟨[], 0, rfl⟩) := rfl
abbrev DPS.dp : DPS α → DP α | [] => default | (_, dp) :: _ => dp

end lcsDP


open scoped Cslib.Algorithms.Lean.TimeM

open Cslib.Algorithms.Lean (TimeM) in
open lcsDP in
/-- Dynamic programming taking quadratic time and quadratic space (list of list). -/
public def lcsDP (xs ys : List α) : TimeM ℕ (List α) := return (← aux0).dp.lcs
where
  aux0 : TimeM ℕ (DPS α) := xs.foldrM aux1 (ys.map (·, default))
  aux1 (x : α) (dps : DPS α) : TimeM ℕ (DPS α) := return (← aux2 x dps).1
  aux2 (x : α) (dps : DPS α) : TimeM ℕ (DPS α × DP α × DP α) := dps.foldrM (aux3 x) default
  aux3 (x : α) : α × DP α → DPS α × DP α × DP α → TimeM ℕ (DPS α × DP α × DP α)
    | (y, xx), (dps, yy, xy) => do
      ✓ let dp := dp x y xx yy xy
      return ((y, dp) :: dps, dp, xx)
  dp (x y : α) (xx yy xy : DP α) : DP α :=
    if x = y then
      ⟨x :: xy.lcs, xy.length + 1, xy.length_eq.rec rfl⟩
    else
      if xx.length ≥ yy.length then xx else yy

section unittest

/-- info: "" -/
#guard_msgs(info) in
#eval test_string (⟪lcsDP · ·⟫) "" ""

/-- info: "" -/
#guard_msgs(info) in
#eval test_string (⟪lcsDP · ·⟫) "ABCD" ""

/-- info: "" -/
#guard_msgs(info) in
#eval test_string (⟪lcsDP · ·⟫) "" "ACBAD"

/-- info: "ACD" -/
#guard_msgs(info) in
#eval test_string (⟪lcsDP · ·⟫) "ABCD" "ACBAD"

/-- info: "AC" -/
#guard_msgs(info) in
#eval test_string (⟪lcsDP · ·⟫) "GAC" "AGCAT"

/-- info: "MJAU" -/
#guard_msgs(info) in
#eval test_string (⟪lcsDP · ·⟫) "XMJYAUZ" "MZJAWXU"

end unittest

namespace lcsDP

variable {x y : α} {xs ys : List α}

theorem cons_aux0 : ⟪aux0 (x :: xs) ys⟫ = ⟪aux1 x ⟪aux0 xs ys⟫⟫ :=
  show ⟪(x :: xs).foldrM aux1 _⟫ = ⟪aux1 x ⟪xs.foldrM aux1 _⟫⟫ by simp

theorem aux0_nil : {xs : List α} → ⟪aux0 xs []⟫ = []
  | [] => rfl
  | x :: xs => by rw [cons_aux0, aux0_nil] ; rfl

theorem aux2_2 : {dps : DPS α} → ⟪aux2 x dps⟫.2.2 = dps.dp
  | [] => rfl
  | _ :: _ => by simp [aux2] ; rfl

theorem aux2_1 : {ys : List α} → ⟪aux2 x ⟪aux0 xs ys⟫⟫.2.1 = ⟪aux0 (x :: xs) ys⟫.dp
  | [] => by rw [aux0_nil, aux0_nil] ; rfl
  | y :: ys =>
    let xx := ⟪aux0 xs (y :: ys)⟫.dp
    let pp := ⟪aux2 x ⟪aux0 xs ys⟫⟫.2
    calc ⟪aux2 x ⟪aux0 xs (y :: ys)⟫⟫.2.1
    -- _  = dp x y xx pp.1 pp.2 := by rw [aux0_cons, aux2] ; simp ; rfl
    _  = ⟪aux0 (x :: xs) (y :: ys)⟫.dp := sorry -- congrArg (DPS.dp ∘ aux1 x) aux0_cons |>.symm

theorem cons_aux0_cons : ⟪aux0 (x :: xs) (y :: ys)⟫.dp =
    dp x y ⟪aux0 xs (y :: ys)⟫.dp ⟪aux0 (x :: xs) ys⟫.dp ⟪aux0 xs ys⟫.dp :=
  let xx := ⟪aux0 xs (y :: ys)⟫.dp
  let yy := ⟪aux0 (x :: xs) ys⟫.dp
  let xy := ⟪aux0 xs ys⟫.dp
  let pp := ⟪aux2 x ⟪aux0 xs ys⟫⟫.2
  let dps := ⟪aux0 xs (y :: ys)⟫
  calc ⟪aux0 (x :: xs) (y :: ys)⟫.dp
  _  = ⟪aux1 x dps⟫.dp := congrArg _ cons_aux0
  _  = ⟪aux2 x dps⟫.1.dp := rfl
  _  = ⟪aux2 x dps⟫.2.1 := sorry
  -- _  = ⟪dps.foldrM (aux3 x) default⟫.1.dp := rfl
  -- _  = ⟪dps.foldrM _ default⟫.1.dp := rfl
  _  = dp x y xx pp.1 pp.2 := sorry -- by rw [aux0_cons] ;
   -- congrArg (DPS.dp ∘ aux1 x) aux0_cons
  _  = dp x y xx yy xy := by rw [aux2_1, aux2_2]

theorem aux1_time : {dps : DPS α} → (aux1 x dps).time = dps.length
  | [] => rfl
  | z :: dps =>
    let m := dps.foldrM (aux3 x) default
    calc ((z :: dps).foldrM (aux3 x) default).time
    _  = (m >>= aux3 x z).time := congrArg _ foldrM_cons
    _  = m.time + (aux3 x z ⟪m⟫).time := rfl
    _  = m.time + 1 := rfl
    _  = dps.length + 1 := congrArg _ aux1_time

theorem aux3_length : {dps : DPS α} → ⟪dps.foldrM (aux3 x) default⟫.1.length = dps.length
  | [] => rfl
  | z :: dps =>
    let m := dps.foldrM (aux3 x) default
    calc ⟪(z :: dps).foldrM (aux3 x) default⟫.1.length
    _  = ⟪m >>= aux3 x z⟫.1.length := by rw [foldrM_cons]
    _  = ⟪aux3 x z ⟪m⟫⟫.1.length := rfl
    _  = ⟪m⟫.1.length + 1 := rfl
    _  = dps.length + 1 := congrArg _ aux3_length

theorem aux0_length : {xs : List α} → ⟪aux0 xs ys⟫.length = ys.length
  | [] => length_map _
  | x :: xs =>
    let dps := ⟪aux0 xs ys⟫
    calc ⟪aux0 (x :: xs) ys⟫.length
    _  = ⟪aux1 x dps⟫.length := congrArg _ cons_aux0
    _  = ⟪aux2 x dps⟫.1.length := rfl
    _  = ⟪dps.foldrM (aux3 x) default⟫.1.length := rfl
    _  = dps.length := aux3_length
    _  = ys.length := aux0_length

end lcsDP

open lcsDP

public theorem nil_lcsDP : {ys : List α} → ⟪lcsDP [] ys⟫ = []
  | [] | _ :: _ => rfl

public theorem lcsDP_nil {xs : List α} : ⟪lcsDP xs []⟫ = [] :=
  congrArg (DP.lcs ∘ DPS.dp) aux0_nil

theorem lcsDP_eq_lcsBrute : {xs ys : List α} → ⟪lcsDP xs ys⟫ = lcsBrute xs ys
  | [], ys => nil_lcsDP.trans nil_lcsBrute.symm
  | xs, [] => lcsDP_nil.trans lcsBrute_nil.symm
  | x :: xs, y :: ys =>
    -- lcsDP
    let xx := ⟪aux0 xs (y :: ys)⟫.dp
    let yy := ⟪aux0 (x :: xs) ys⟫.dp
    let xy := ⟪aux0 xs ys⟫.dp
    -- lcsBrute
    let xx' := lcsBrute xs (y :: ys)
    let yy' := lcsBrute (x :: xs) ys
    let xy' := lcsBrute xs ys
    -- equalities
    have hxx : xx.lcs = xx' := lcsDP_eq_lcsBrute
    have hyy : yy.lcs = yy' := lcsDP_eq_lcsBrute
    have hxy : xy.lcs = xy' := lcsDP_eq_lcsBrute
    -- main proof
    calc ⟪lcsDP (x :: xs) (y :: ys)⟫
    _  = ⟪aux0 (x :: xs) (y :: ys)⟫.dp.lcs := rfl
    _  = (dp x y xx yy xy).lcs := congrArg _ cons_aux0_cons
    _  = if x = y then x :: xy.lcs else (if xx.length ≥ yy.length then xx else yy).lcs :=
      apply_ite DP.lcs ..
    _  = if x = y then x :: xy.lcs else if xx.length ≥ yy.length then xx.lcs else yy.lcs :=
      congrArg _ (apply_ite DP.lcs ..)
    _  = if x = y then x :: xy' else if xx'.length ≥ yy'.length then xx' else yy' :=
      by rw [hxy, ←xx.length_eq, ←yy.length_eq, hxx, hyy]
    _  = lcsBrute (x :: xs) (y :: ys) := by rw [lcsBrute]

public theorem lcsDP_correct {xs ys : List α} : LCS xs ys ⟪lcsDP xs ys⟫ :=
  lcsDP_eq_lcsBrute.symm.rec lcsBrute_correct

public theorem lcsDP_time {xs ys : List α} : (lcsDP xs ys).time = xs.length * ys.length :=
  match xs with
  | [] => ys.length.zero_mul.symm
  | x :: xs =>
    calc ((x :: xs).foldrM aux1 _).time
    _  = (xs.foldrM aux1 _ >>= aux1 x).time := congrArg _ foldrM_cons
    _  = (lcsDP xs ys).time + (aux1 x ⟪aux0 xs ys⟫).time := rfl
    _  = xs.length * ys.length + ys.length := by rw [lcsDP_time, aux1_time, aux0_length]
    _  = (x :: xs).length * ys.length := Nat.succ_mul .. |>.symm

end List
