

import Mathlib.Computability.Encoding
import Mathlib.Data.List.SplitOn

open Computability

section Encodings
/-
These encodings are used in the formalization of complexity classes such as P and NP.
Note that in a Zulip discussion thread, Daniel Weber contributed some more general encodings.
We might eventually want to replace these with his more general versions.
see: https://leanprover.zulipchat.com/#narrow/channel/116395-maths/topic/Formalise.20the.20proposition.20P.20.E2.89.A0NP/with/453031558
-/

def finEncodingListBool : Computability.FinEncoding (List Bool) where
  Γ := Bool
  encode := id
  decode := Option.some
  decode_encode _ := rfl
  ΓFin := Bool.fintype

@[simp]
lemma splitOnP_isNone_map_some {α : Type} (l : List α) :
    List.splitOnP Option.isNone (l.map some) = [l.map some] := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    simp [ih]

@[simp]
lemma splitOnP_append_cons {α : Type} (l1 l2 : List α)
    (a : α) (P : α → Bool) (hPa : P a = true) :
    List.splitOnP P (l1 ++ a :: l2)
    = List.splitOnP P l1 ++ List.splitOnP P l2 := by
  induction l1 with
  | nil => simp [hPa]
  | cons hd tl ih =>
    obtain ⟨hd1, tl1, h1'⟩ := List.exists_cons_of_ne_nil (List.splitOnP_ne_nil P tl)
    by_cases hPh : P hd <;> simp [*]

@[simp]
lemma getLeft?_comp_inl {α β : Type*} :
    Sum.getLeft? ∘ @Sum.inl α β = Option.some := by
  ext
  simp

@[simp]
lemma getLeft?_comp_inr {α β : Type*} :
    Sum.getLeft? ∘ @Sum.inr α β = fun x ↦ Option.none := by
  ext
  simp

@[simp]
lemma getRight?_comp_inl {α β : Type*} :
    Sum.getRight? ∘ @Sum.inl α β = fun x ↦ Option.none := by
  ext
  simp

@[simp]
lemma getRight?_comp_inr {α β : Type*} :
    Sum.getRight? ∘ @Sum.inr α β = Option.some := by
  ext
  simp

@[simp]
lemma List.filterMap_none {α β : Type*} (l : List α) :
    l.filterMap (fun _ ↦ @Option.none β) = [] := by
  induction l <;> simp [*]

def finEncodingPair {α β : Type*} (ea : FinEncoding α) (eb : FinEncoding β) :
    Computability.FinEncoding (α × β) where
  Γ := ea.Γ ⊕ eb.Γ
  encode x := (ea.encode x.1).map .inl ++ (eb.encode x.2).map .inr
  decode x := Option.map₂ Prod.mk (ea.decode (x.filterMap Sum.getLeft?))
      (eb.decode (x.filterMap Sum.getRight?))
  decode_encode x := by
    simp [List.filterMap_append, ea.decode_encode, eb.decode_encode]
  ΓFin := inferInstance

def encode_list_bool_prod_list_bool :
    (List Bool × List Bool) → List (Bool) :=
  fun ⟨l1, l2⟩ ↦ ((l1.map some) ++ [none] ++ (l2.map some)).flatMap (fun
    | some b => [true, b]
    | none   => [false, false])

def finEncodingListBoolProdListBool : Computability.FinEncoding (List Bool × List Bool) where
  Γ := Option Bool
  encode := fun ⟨l1, l2⟩ ↦ (l1.map some) ++ [none] ++ (l2.map some)
  decode := fun l ↦
    match l.splitOnP Option.isNone with
    | [l1, l2] => some (l1.map (Option.getD · false), l2.map (Option.getD · false))
    | _ => none
  decode_encode := by
    intro (l1, l2)
    simp
  ΓFin := instFintypeOption



end Encodings
