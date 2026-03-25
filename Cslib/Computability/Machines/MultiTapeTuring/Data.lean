/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.MultiTapeTuring.Dyadic
public import Mathlib.Logic.Encodable.Basic
import Mathlib.Tactic.Linarith

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

-- ─── Balance machinery for prefix-freeness ───────────────────────────────

private def bw (c : Char) : Int :=
  if c = '[' ∨ c = '(' then 1
  else if c = ']' ∨ c = ')' then -1
  else 0

private def bal (l : List Char) : Int := (l.map bw).sum

private lemma bal_append (l₁ l₂ : List Char) :
    bal (l₁ ++ l₂) = bal l₁ + bal l₂ := by
  simp [bal, List.map_append, List.sum_append]

private lemma bal_cons (c : Char) (l : List Char) :
    bal (c :: l) = bw c + bal l := by simp [bal]

private lemma bw_dyadic {c : Char} {n : ℕ} (h : c ∈ dyadic n) : bw c = 0 := by
  rcases dyadic_mem_chars h with rfl | rfl <;> decide

private lemma bal_of_all_bw_zero {l : List Char} (h : ∀ c ∈ l, bw c = 0) :
    bal l = 0 := by
  induction l with
  | nil => rfl
  | cons c cs ih =>
    rw [bal_cons, h c List.mem_cons_self,
        ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    simp

private lemma bal_take_of_all_bw_zero {l : List Char}
    (h : ∀ c ∈ l, bw c = 0) (i : ℕ) : bal (l.take i) = 0 :=
  bal_of_all_bw_zero (fun c hc => h c (List.mem_of_mem_take hc))

private lemma bal_dyadic (n : ℕ) : bal (dyadic n) = 0 :=
  bal_of_all_bw_zero (fun _ h => bw_dyadic h)

private lemma bal_dyadic_take (n : ℕ) (i : ℕ) : bal ((dyadic n).take i) = 0 :=
  bal_take_of_all_bw_zero (fun _ h => bw_dyadic h) i

/-- Balance at interior positions of a flatten of balanced segments is non-negative. -/
private lemma bal_flatten_take_nonneg
    (segs : List (List Char))
    (h_bal : ∀ s ∈ segs, bal s = 0)
    (h_pos : ∀ s ∈ segs, ∀ i, 0 < i → i < s.length → 0 < bal (s.take i))
    (j : ℕ) (hj : j ≤ segs.flatten.length) :
    0 ≤ bal (segs.flatten.take j) := by
  induction segs generalizing j with
  | nil => simp [bal]
  | cons s ss ih =>
    simp only [List.flatten_cons] at hj ⊢
    by_cases hle : j ≤ s.length
    · rw [List.take_append_of_le_length hle]
      rcases Nat.eq_or_lt_of_le hle with rfl | hjlt
      · rw [List.take_length]; linarith [h_bal s List.mem_cons_self]
      · rcases j with _ | j
        · simp [bal]
        · linarith [h_pos s List.mem_cons_self (j + 1) (by omega) hjlt]
    · push_neg at hle
      rw [List.take_append, List.take_of_length_le (by omega), bal_append,
          h_bal s List.mem_cons_self]
      simp only [zero_add]
      exact ih (fun t ht => h_bal t (List.mem_cons_of_mem s ht))
              (fun t ht => h_pos t (List.mem_cons_of_mem s ht))
              _ (by simp only [List.length_append] at hj; omega)

/-- Balance of each encoding is 0 and positive at every interior position. -/
private lemma Data.enc_bal (d : Data) :
    bal d.enc = 0 ∧ ∀ i, 0 < i → i < d.enc.length → 0 < bal (d.enc.take i) := by
  match d with
  | .num n =>
    simp only [Data.enc_num]
    constructor
    · rw [show ['['] ++ dyadic n ++ [']'] = ['['] ++ (dyadic n ++ [']']) from by simp]
      rw [bal_append, bal_append, bal_dyadic]; decide
    · intro i hi hlt
      simp only [List.length_append, List.length_cons, List.length_nil] at hlt
      rw [show ['['] ++ dyadic n ++ [']'] = '[' :: (dyadic n ++ [']']) from rfl]
      match i, hi with
      | i + 1, _ =>
        simp only [List.take_succ_cons]
        rw [bal_cons, List.take_append_of_le_length (show i ≤ (dyadic n).length by omega),
            bal_dyadic_take]
        decide
  | .list ds =>
    simp only [Data.enc_list]
    have ih : ∀ d' ∈ ds, bal d'.enc = 0 ∧
        ∀ i, 0 < i → i < d'.enc.length → 0 < bal (d'.enc.take i) :=
      fun d' _ => Data.enc_bal d'
    have bal_flat : bal (ds.map Data.enc).flatten = 0 := by
      induction ds with
      | nil => simp [bal]
      | cons d ds' ihds =>
        simp only [List.map_cons, List.flatten_cons]
        rw [bal_append, (ih d List.mem_cons_self).1]
        simp only [zero_add]
        exact ihds (fun d' hd' => ih d' (List.mem_cons_of_mem d hd'))
    have bal_flat_nonneg : ∀ j, j ≤ (ds.map Data.enc).flatten.length →
        0 ≤ bal ((ds.map Data.enc).flatten.take j) :=
      bal_flatten_take_nonneg (ds.map Data.enc)
        (fun s hs => by
          obtain ⟨d', hd', rfl⟩ := List.mem_map.mp hs; exact (ih d' hd').1)
        (fun s hs k hk hkl => by
          obtain ⟨d', hd', rfl⟩ := List.mem_map.mp hs; exact (ih d' hd').2 k hk hkl)
    set flat := (ds.map Data.enc).flatten
    constructor
    · rw [show ['('] ++ flat ++ [')'] = ['('] ++ (flat ++ [')']) from by simp]
      rw [bal_append, bal_append, bal_flat]; decide
    · intro i hi hlt
      simp only [List.length_append, List.length_cons, List.length_nil] at hlt
      rw [show ['('] ++ flat ++ [')'] = '(' :: (flat ++ [')']) from rfl]
      match i, hi with
      | i + 1, _ =>
        simp only [List.take_succ_cons]
        rw [bal_cons, List.take_append_of_le_length (show i ≤ flat.length by omega)]
        have : 0 ≤ bal (flat.take i) := bal_flat_nonneg i (by omega)
        have : bw '(' = 1 := by decide
        linarith
  termination_by sizeOf d

/-- A proper prefix of any encoding leads to a balance contradiction. -/
private lemma Data.enc_no_proper_prefix {d₁ d₂ : Data}
    (hpfx : d₁.enc <+: d₂.enc) (hne : d₁.enc ≠ d₂.enc) : False := by
  obtain ⟨t, ht⟩ := hpfx
  -- ht : d₁.enc ++ t = d₂.enc
  have htne : t ≠ [] := fun h => hne (by rw [← ht, h, List.append_nil])
  have hlt : d₁.enc.length < d₂.enc.length := by
    rw [← ht, List.length_append]
    have : 0 < t.length := by cases t with | nil => exact absurd rfl htne | cons _ _ => simp
    omega
  have hpos := (Data.enc_bal d₂).2 d₁.enc.length (Data.enc_length_pos d₁) hlt
  have hzero : bal (d₂.enc.take d₁.enc.length) = 0 := by
    conv_lhs => rw [← ht]
    rw [List.take_append_of_le_length (Nat.le_refl _), List.take_length]
    exact (Data.enc_bal d₁).1
  linarith

-- ─── Injectivity ─────────────────────────────────────────────────────────

mutual

/-- Injectivity of `Data.enc` (internal, mutual with flatten helper). -/
private def Data.enc_injective_mut (d₁ d₂ : Data) (h : d₁.enc = d₂.enc) :
    d₁ = d₂ :=
  match d₁, d₂ with
  | .num n₁, .num n₂ => by
    simp only [Data.enc_num] at h
    have h₂ : dyadic n₁ = dyadic n₂ := by
      have := List.cons.inj h; exact List.append_cancel_right this.2
    have h₃ := congrArg dyadic_inv h₂
    simp only [dyadic_inv_dyadic] at h₃
    exact congrArg Data.num (Option.some_injective _ h₃)
  | .num _, .list _ => by simp [Data.enc_num, Data.enc_list] at h
  | .list _, .num _ => by simp [Data.enc_num, Data.enc_list] at h
  | .list ds₁, .list ds₂ => by
    simp only [Data.enc_list] at h
    have hflat : (ds₁.map Data.enc).flatten = (ds₂.map Data.enc).flatten := by
      have := List.cons.inj h; exact List.append_cancel_right this.2
    exact congrArg Data.list (enc_flatten_injective_mut ds₁ ds₂ hflat)

/-- Flatten of encodings is injective. -/
private def enc_flatten_injective_mut
    (ds₁ ds₂ : List Data)
    (h : (ds₁.map Data.enc).flatten = (ds₂.map Data.enc).flatten) :
    ds₁ = ds₂ := by
  match ds₁, ds₂ with
  | [], [] => rfl
  | [], d :: ds =>
    exfalso
    simp only [List.map_nil, List.flatten_nil, List.map_cons, List.flatten_cons] at h
    have hlen := Data.enc_length_pos d
    have : 0 = (d.enc ++ (ds.map Data.enc).flatten).length := congrArg List.length h
    simp only [List.length_append] at this
    omega
  | d :: ds, [] =>
    exfalso
    simp only [List.map_cons, List.flatten_cons, List.map_nil, List.flatten_nil] at h
    have hlen := Data.enc_length_pos d
    have : (d.enc ++ (ds.map Data.enc).flatten).length = 0 := congrArg List.length h
    simp only [List.length_append] at this
    omega
  | d₁ :: ds₁, d₂ :: ds₂ =>
    simp only [List.map_cons, List.flatten_cons] at h
    -- h : d₁.enc ++ flat₁ = d₂.enc ++ flat₂
    -- Show d₁.enc = d₂.enc using enc_no_proper_prefix
    have heq_enc : d₁.enc = d₂.enc := by
      by_contra hne
      by_cases hle : d₁.enc.length ≤ d₂.enc.length
      · have hpfx : d₁.enc <+: d₂.enc := by
          have h1 := congrArg (List.take d₁.enc.length) h
          rw [List.take_append_of_le_length (Nat.le_refl _),
              List.take_length] at h1
          rw [List.take_append_of_le_length hle] at h1
          -- h1 : d₁.enc = d₂.enc.take d₁.enc.length
          have := List.take_prefix d₁.enc.length d₂.enc
          rwa [← h1] at this
        exact Data.enc_no_proper_prefix hpfx hne
      · push_neg at hle
        have hpfx : d₂.enc <+: d₁.enc := by
          have h1 := congrArg (List.take d₂.enc.length) h
          rw [List.take_append_of_le_length (by omega)] at h1
          rw [List.take_append_of_le_length (Nat.le_refl _),
              List.take_length] at h1
          -- h1 : d₁.enc.take d₂.enc.length = d₂.enc
          have := List.take_prefix d₂.enc.length d₁.enc
          rwa [h1] at this
        exact Data.enc_no_proper_prefix hpfx (Ne.symm hne)
    have hd := Data.enc_injective_mut d₁ d₂ heq_enc
    subst hd
    exact congrArg (d₁ :: ·) (enc_flatten_injective_mut ds₁ ds₂
      (List.append_cancel_left h))

end

public lemma Data.enc_injective : Function.Injective Data.enc :=
  fun d₁ d₂ h => Data.enc_injective_mut d₁ d₂ h

/-- No `Data.enc` is a proper prefix of another. Together with injectivity,
    this means the encoding is uniquely decodable. -/
public lemma Data.enc_prefix_free {d₁ d₂ : Data}
    (h : d₁.enc <+: d₂.enc) : d₁ = d₂ := by
  by_cases heq : d₁.enc = d₂.enc
  · exact Data.enc_injective_mut d₁ d₂ heq
  · exact False.elim (Data.enc_no_proper_prefix h heq)

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

-- TODO clean up (ai)
public instance (k : ℕ) : StrEnc (Fin k) where
  toData i := StrEnc.toData i.val
  fromData d := do
    let n ← StrEnc.fromData (α := ℕ) d
    if h : n < k then some ⟨n, h⟩ else none
  fromData_toData i := by simp [i.isLt]

-- TODO clean up (ai)
public instance (k : ℕ) (α : Type*) [StrEnc α] : StrEnc (Fin k → α) where
  toData f := StrEnc.toData (List.ofFn f)
  fromData d := do
    let l ← StrEnc.fromData (α := List α) d
    if h : l.length = k then
      some (fun i => l[i.val]'(h ▸ i.isLt))
    else
      none
  fromData_toData f := by
    simp only [StrEnc.fromData_toData_apply]
    ext i
    simp [List.getElem_ofFn]

-- TODO clean up (ai)
public instance (α : Type*) (β : Type*) [StrEnc α] [StrEnc β] : StrEnc (α × β) where
  toData p := Data.list [StrEnc.toData p.1, StrEnc.toData p.2]
  fromData
    | Data.list [a, b] =>
      match StrEnc.fromData a, StrEnc.fromData b with
      | some a', some b' => some (a', b')
      | _, _ => none
    | _ => none
  fromData_toData p := by simp

/-- `StrEnc` for functions `α → β` where `α` is finite, encoded as the function's
    graph: a list of `(a, f a)` pairs.
    Not registered as an instance to avoid overlap with `Fin k → α`.
    Activate with `letI := StrEnc.ofFunction α β`. -/
-- TODO clean up (ai)
@[reducible]
public noncomputable def StrEnc.ofFunction (α : Type) (β : Type*)
    [Fintype α] [DecidableEq α] [StrEnc α] [StrEnc β] : StrEnc (α → β) where
  toData f := StrEnc.toData (Finset.univ.val.toList.map fun a => (a, f a))
  fromData d :=
    match StrEnc.fromData (α := List (α × β)) d with
    | none => none
    | some pairs =>
      let f := fun a => pairs.lookup a
      if h : ∀ a, (f a).isSome then
        some (fun a => (f a).get (h a))
      else
        none
  fromData_toData f := by
    simp only [StrEnc.fromData_toData_apply]
    have h_mem : ∀ a : α, a ∈ Finset.univ.val.toList := fun a =>
      Multiset.mem_toList.mpr (Finset.mem_univ a)
    have h_lookup : ∀ a, (Finset.univ.val.toList.map (fun a => (a, f a))).lookup a
        = some (f a) :=
      fun a => List.lookup_graph f (h_mem a)
    have h_forall : ∀ a,
        ((Finset.univ.val.toList.map (fun a => (a, f a))).lookup a).isSome := by
      intro a; simp [h_lookup a]
    rw [dif_pos h_forall]
    congr 1; ext a
    have := h_lookup a
    simp_all

/-- `StrEnc` instance for any `Encodable` type via its encoding to `ℕ`.
    Not registered as an instance to avoid overlap with specific encodings
    (e.g., `Bool`). Use `attribute [local instance] StrEnc.ofEncodable` or
    `letI := StrEnc.ofEncodable α` to activate. -/
-- TODO clean up (ai)
@[reducible]
public def StrEnc.ofEncodable (α : Type) [Encodable α] : StrEnc α where
  toData a := StrEnc.toData (Encodable.encode a)
  fromData d := do
    let n ← StrEnc.fromData (α := ℕ) d
    Encodable.decode n
  fromData_toData a := by simp [Encodable.encodek]

/-- Example: encoding the addition function on `Fin 4 × Fin 4 → ℕ`. -/
-- TODO clean up (ai)
noncomputable example : Data :=
  letI := StrEnc.ofFunction (Fin 4 × Fin 4) ℕ
  StrEnc.toData (fun (p : Fin 4 × Fin 4) => p.1.val + p.2.val)

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
