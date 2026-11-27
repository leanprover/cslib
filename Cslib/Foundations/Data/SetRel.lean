/-
Copyright (c) 2026 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/

module

public import Cslib.Init
public import Mathlib.Basic.Rel

/-! # Set-based relations -/

@[expose] public section

namespace SetRel

section Map

variable {α β γ α' β' γ' : Type*} {f : α → α'} {g : β → β'} {h : γ → γ'} {s r : SetRel α β}

/-- Map set-based relations along a pair of functions. -/
protected def map (f : α → α') (g : β → β') (r : SetRel α β) : SetRel α' β' := Prod.map f g '' r

@[simp, grind =] lemma mem_map : c ~[r.map f g] d ↔ ∃ a b, a ~[r] b ∧ f a = c ∧ g b = d := by
  simp [SetRel.map]

lemma map_mem_map (h : a ~[r] b) : f a ~[r.map f g] g b := mem_map.mpr ⟨a, b, h, rfl, rfl⟩

@[simp] lemma map_inv : (s.map f g).inv = s.inv.map g f := by grind

lemma map_subset_map (h : s ⊆ r) : s.map f g ⊆ r.map f g := Set.image_mono h

lemma map_subset_map_iff (hf : f.Injective) (hg : g.Injective) :
    s.map f g ⊆ r.map f g ↔ s ⊆ r := Set.image_subset_image_iff (hf.prodMap hg)

@[simp] lemma map_union : (s ∪ r).map f g = s.map f g ∪ r.map f g := Set.image_union ..

lemma map_inter_of_injective_prodMap (h : (Prod.map f g).Injective) :
    (s ∩ r).map f g = s.map f g ∩ r.map f g :=
  Set.image_inter h

lemma map_inter_of_injective (hf : f.Injective) (hg : g.Injective) :
    (s ∩ r).map f g = s.map f g ∩ r.map f g :=
  map_inter_of_injective_prodMap (hf.prodMap hg)

@[simp] lemma map_bot : (∅ : SetRel α β).map f g = ⊥ := by
  ext ⟨a, b⟩
  simp

lemma map_top_of_surjective_prodMap (h : (Prod.map f g).Surjective) :
    (⊤ : SetRel α β).map f g = ⊤ := Set.image_univ_of_surjective h

lemma map_top_of_surjective (hf : f.Surjective) (hg : g.Surjective) :
    (⊤ : SetRel α β).map f g = ⊤ := map_top_of_surjective_prodMap (hf.prodMap hg)

lemma map_id_of_surjective (hf : f.Surjective) :
    (.id : SetRel α α).map f f = SetRel.id := by
  ext ⟨a, b⟩
  grind [hf a]

lemma map_comp_of_injective (hg : g.Injective) {s : SetRel α β} {r : SetRel β γ} :
    (s ○ r).map f h = s.map f g ○ r.map g h := by
  ext ⟨a, c⟩
  simp [hg.eq_iff]
  grind

@[simp] lemma map_id_fun : s.map id id = s := Set.image_id _

@[simp] lemma map_comp_fun {α₁ α₂ α₃ β₁ β₂ β₃ : Type*} {f₁ : α₁ → α₂} {f₂ : α₂ → α₃} {g₁ : β₁ → β₂}
    {g₂ : β₂ → β₃} {s : SetRel α₁ β₁} : (s.map f₁ g₁).map f₂ g₂ = s.map (f₂ ∘ f₁) (g₂ ∘ g₁) :=
  Set.image_comp (Prod.map f₂ g₂) (Prod.map f₁ g₁) s |>.symm

/-- Equivalences between types lift the their types of set-based relations. -/
@[simps]
def mapEquiv (eα : α ≃ α') (eβ : β ≃ β') : SetRel α β ≃ SetRel α' β' where
  toFun s := s.map eα eβ
  invFun s := s.map eα.symm eβ.symm
  left_inv _ := by simp
  right_inv _ := by simp

end Map

variable {α : Type*} {s : Set α} {r : SetRel α α} {x y : α}

/-- Encode a `s` set as a relation, by relating each element of `s` to itself. -/
def ofSet (s : Set α) : SetRel α α := {(a, b) | a = b ∧ a ∈ s}

@[simp, grind =] lemma mem_ofSet : x ~[ofSet s] y ↔ x = y ∧ x ∈ s := .rfl

lemma mem_ofSet' : x ~[ofSet s] y ↔ x = y ∧ y ∈ s := by simp +contextual

lemma mem_ofSet_self_iff : x ~[ofSet s] x ↔ x ∈ s := by simp

@[simp] lemma dom_ofSet : (ofSet s).dom = s := by ext; simp

@[simp] lemma cod_ofSet : (ofSet s).cod = s := by ext; simp

lemma ofSet_injective : Function.Injective (α := Set α) ofSet := by
  intro s t h
  simpa using congr(SetRel.dom $h)

lemma ofSet_inj {s t : Set α} : ofSet s = ofSet t ↔ s = t := ofSet_injective.eq_iff

lemma ofSet_le_ofSet_iff {s t : Set α} : ofSet s ≤ ofSet t ↔ s ⊆ t := by
  simp [Set.subset_def]

lemma eq_of_mem_ofSet (h : x ~[ofSet s] y) : x = y := by grind

lemma left_mem_of_mem_ofSet (h : x ~[ofSet s] y) : x ∈ s := by grind

lemma right_mem_of_mem_ofSet (h : x ~[ofSet s] y) : y ∈ s := by grind

lemma ofSet_dom_comp_self (r : SetRel α α) : ofSet r.dom ○ r = r := by
  grind

lemma self_comp_ofSet_cod (r : SetRel α α) : r ○ ofSet r.cod = r := by
  grind

lemma mem_ofSet_comp_iff : x ~[ofSet s ○ r] y ↔ x ∈ s ∧ x ~[r] y := by simp

lemma mem_comp_ofSet_iff : x ~[r ○ ofSet s] y ↔ y ∈ s ∧ x ~[r] y := by simp [and_comm]

lemma comp_ofSet_eq_self_iff : ofSet s ○ r = r ↔ r.dom ⊆ s := by
  grind

lemma ofSet_comp_eq_self_iff : r ○ ofSet s = r ↔ r.cod ⊆ s := by
  grind

end SetRel
