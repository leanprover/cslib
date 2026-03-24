/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.MultiTapeTuring.Dyadic

namespace Turing

/-- Universal data type for structured TM computation.
    All types processed by TM routines are first mapped to `Data`.
    Numbers are encoded with `[dyadic]` and lists with `(elem₁…elemₙ)`. -/
public inductive Data where
  /-- A natural number. -/
  | num : ℕ → Data
  /-- A list of data values. -/
  | list : List Data → Data

mutual
  public def Data.decEq : (a b : Data) → Decidable (a = b)
    | .num n₁, .num n₂ =>
      if h : n₁ = n₂ then isTrue (h ▸ rfl)
      else isFalse (fun h' => h (Data.num.inj h'))
    | .list l₁, .list l₂ =>
      match Data.decEqList l₁ l₂ with
      | isTrue h => isTrue (h ▸ rfl)
      | isFalse h => isFalse (fun h' => h (Data.list.inj h'))
    | .num _, .list _ => isFalse Data.noConfusion
    | .list _, .num _ => isFalse Data.noConfusion

  public def Data.decEqList : (l₁ l₂ : List Data) → Decidable (l₁ = l₂)
    | [], [] => isTrue rfl
    | [], _ :: _ => isFalse nofun
    | _ :: _, [] => isFalse nofun
    | a :: as, b :: bs =>
      match Data.decEq a b, Data.decEqList as bs with
      | isTrue h₁, isTrue h₂ => isTrue (by rw [h₁, h₂])
      | _, isFalse h₂ =>
        isFalse (fun h => h₂ (List.tail_eq_of_cons_eq h))
      | isFalse h₁, _ =>
        isFalse (fun h => h₁ (List.head_eq_of_cons_eq h))
end

public instance : DecidableEq Data := Data.decEq



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

-- TODO clean up (ai)
public lemma Data.enc_length_pos (d : Data) : 0 < d.enc.length := by
  cases d with
  | num n => simp [Data.enc_num]
  | list ds => simp [Data.enc_list]

-- TOOD prove by copilot
public lemma Data.enc_injective : Function.Injective Data.enc := by sorry

/-- No `Data.enc` is a proper prefix of another. Together with injectivity,
    this means the encoding is uniquely decodable. -/
public lemma Data.enc_prefix_free {d₁ d₂ : Data}
    (h : d₁.enc <+: d₂.enc) : d₁ = d₂ := by sorry

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

public instance (α : Type) [StrEnc α] : StrEnc (Option α) where
  toData o := StrEnc.toData o.toList
  fromData
    | Data.list [x] => some (StrEnc.fromData x)
    | Data.list [] => some none
    | _ => none
  fromData_toData := by
    intro o
    cases o with | some _ | none <;> simp [StrEnc.toData]

public instance : StrEnc Char where
  toData o := StrEnc.toData o.toNat
  fromData
    | Data.num n => some (Char.ofNat n)
    | _ => none
  fromData_toData := by simp

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
public lemma Data.atPath_get_atPath {d : Data} {path₁ path₂ : List ℕ}
    (h_valid : (d.atPath path₁).isSome) :
    ((d.atPath path₁).get h_valid).atPath path₂ =
      d.atPath (path₁ ++ path₂) := by
  simp [Data.atPath_append]
  sorry

@[simp]
public lemma Data.atPath_dropLast_isSome_of_isSome {d : Data} {path : List ℕ}
    (h_is_some : (d.atPath path).isSome) :
  (d.atPath path.dropLast).isSome := by
  sorry

public lemma Data.atPath_isSome_of_le_isSome {d : Data} {i₁ i₂ : ℕ}
    (h_le : i₁ ≤ i₂)
    (h_is_some : (d.atPath [i₂]).isSome) :
  (d.atPath [i₁]).isSome := by
  sorry

-- TODO redundant?
@[simp]
public lemma Data.atPath_isSome_of_succ_isSome {d : Data} {idx : ℕ}
    (h_succ_is_some : (d.atPath [idx + 1]).isSome) :
  (d.atPath [idx]).isSome := by
  sorry

end Turing
