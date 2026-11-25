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

@[simp] lemma map_inv : (s.map f g).inv = s.inv.map g f := by ext ⟨c, d⟩; grind

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

/-- Equivalences between types lift to the their types of set-based relations. -/
@[simps]
def mapEquiv (eα : α ≃ α') (eβ : β ≃ β') : SetRel α β ≃ SetRel α' β' where
  toFun s := s.map eα eβ
  invFun s := s.map eα.symm eβ.symm
  left_inv _ := by simp
  right_inv _ := by simp

protected def comap (f : α → α') (g : β → β') (r : SetRel α' β') : SetRel α β :=
  (Prod.map f g) ⁻¹' r

variable {s r : SetRel α' β'}

@[simp, grind =] lemma mem_comap : a ~[r.comap f g] b ↔ f a ~[r] g b := .rfl

@[simp] lemma comap_inv : r.inv.comap g f = (r.comap f g).inv := by ext ⟨x, y⟩; simp

@[simp] lemma comap_union : (s ∪ r).comap f g = s.comap f g ∪ r.comap f g := Set.preimage_union

@[simp] lemma comap_inter : (s ∩ r).comap f g = s.comap f g ∩ r.comap f g := Set.preimage_inter

lemma comap_subset_comap (h : s ⊆ r) : s.comap f g ⊆ r.comap f g := Set.preimage_mono h

lemma comap_subset_comap_iff (hf : f.Surjective) (hg : g.Surjective) :
    s.comap f g ⊆ r.comap f g ↔ s ⊆ r := (hf.prodMap hg).preimage_subset_preimage_iff

@[simp] lemma comap_bot : SetRel.comap f g ⊥ = ⊥ := Set.preimage_empty

@[simp] lemma comap_top : SetRel.comap f g ⊤ = ⊤ := Set.preimage_univ

lemma map_id_of_injective (hf : f.Injective) : SetRel.comap f f .id = .id := by
  ext ⟨x, y⟩
  exact hf.eq_iff

lemma map_comp_of_surjective (hg : g.Surjective) {r : SetRel β' γ'} :
    (s ○ r).comap f h = s.comap f g ○ r.comap g h := by
  ext ⟨x, z⟩
  simpa using hg.exists

@[simp] lemma comap_id_fun : r.map id id = r := by ext ⟨x, y⟩; simp

@[simp] lemma comap_comp_fun {α₁ α₂ α₃ β₁ β₂ β₃ : Type*} {f₁ : α₁ → α₂} {f₂ : α₂ → α₃}
    {g₁ : β₁ → β₂} {g₂ : β₂ → β₃} {s : SetRel α₃ β₃} :
    (s.comap f₂ g₂).comap f₁ g₁ =  s.comap (f₂ ∘ f₁) (g₂ ∘ g₁) :=
  Set.preimage_comp.symm

def mapBijective (hf : f.Bijective) (hg : g.Bijective) : SetRel α β ≃ SetRel α' β' where
  toFun := .map f g
  invFun := .comap f g
  left_inv r := by ext ⟨x, y⟩; simp [hf.injective.eq_iff, hg.injective.eq_iff]
  right_inv r := by
    ext ⟨x, y⟩
    constructor
    · rintro ⟨⟨a, b⟩, h, rfl, rfl⟩
      exact h
    · intro h
      obtain ⟨x', rfl⟩ := hf.surjective x
      obtain ⟨y', rfl⟩ := hg.surjective y
      exact map_mem_map h

end Map

section Sigma

variable {α β ι : Type*}

def toPartition (s : ι → Set α) (t : ι → Set β) : SetRel α β → Π i, SetRel (s i) (t i) :=
    fun r _ ↦ r.comap (↑) (↑)

end Sigma

end SetRel
