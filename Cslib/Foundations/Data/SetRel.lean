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

section Sets

variable {α : Type*} {s : Set α} {r : SetRel α α} {x y : α}

/-- Encode a `s` set as a relation, by relating each element of `s` to itself. -/
@[simps]
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

variable {α β : Type*} {A : Set α} {B : Set β} {a : α} {b : β}

def rectangle (A : Set α) (B : Set β) : SetRel α β := {(a, b) : α × β | a ∈ A ∧ b ∈ B}

@[simp, grind =] lemma mem_rectangle : a ~[rectangle A B] b ↔ a ∈ A ∧ b ∈ B := .rfl

end Sets

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

lemma comap_id_of_injective (hf : f.Injective) : SetRel.comap f f .id = .id := by
  ext ⟨x, y⟩
  exact hf.eq_iff

lemma comap_comp_of_surjective (hg : g.Surjective) {r : SetRel β' γ'} :
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

open Sigma Set

variable {α β γ ι : Type*} {A : ι → Set α} {B : ι → Set β} {C : ι → Set γ} {s r : SetRel α β}

def comapPartition (A : ι → Set α) (B : ι → Set β) : SetRel α β → Π i, SetRel (A i) (B i) :=
    fun r _ ↦ r.comap (↑) (↑)

@[simp] lemma mem_comapPartition {i : ι} {a : A i} {b : B i} :
    a ~[comapPartition A B r i] b ↔ (a : α) ~[r] (b : β) := .rfl

lemma comapPartition_inv : s.inv.comapPartition B A = fun i ↦ (s.comapPartition A B i).inv :=
  funext fun _ ↦ comap_inv

lemma comapPartition_le (h : s ⊆ r) : s.comapPartition A B ≤ r.comapPartition A B := by
  intro i ⟨⟨a, _⟩, ⟨b, _⟩⟩
  simpa using @h (a, b)

lemma comapPartition_union :
    (s ∪ r).comapPartition A B = s.comapPartition A B ⊔ r.comapPartition A B :=
  funext fun _ ↦ comap_union

lemma comapPartition_inter :
    (s ∩ r).comapPartition A B = s.comapPartition A B ⊓ r.comapPartition A B :=
  funext fun _ ↦ comap_inter

lemma comapPartition_id : SetRel.id.comapPartition A A = fun _ ↦ .id :=
  funext fun _ ↦ comap_id_of_injective Subtype.val_injective

lemma comapPartition_bot : (⊥ : SetRel α β).comapPartition A B = ⊥ :=
  funext fun _ ↦ comap_bot

lemma comapPartition_top : (⊤ : SetRel α β).comapPartition A B = ⊤ :=
  funext fun _ ↦ comap_top

def ofPartition (A : ι → Set α) (B : ι → Set β) : SetRel α β := ⋃ i, rectangle (A i) (B i)

@[simp, grind =] lemma mem_ofPartition : a ~[ofPartition A B] b ↔ ∃ i, a ∈ A i ∧ b ∈ B i := by
  simp [ofPartition]

instance : (ofPartition A A).IsSymm where
  symm a b h := by simpa [and_comm] using h

theorem isTrans_ofPartition (h : Set.univ.PairwiseDisjoint A) : (ofPartition A A).IsTrans where
  trans := by
    rintro a b c ⟨_, ⟨i, rfl⟩, ha, hb⟩ ⟨_, ⟨j, rfl⟩, hb', hc⟩
    obtain rfl : i = j :=
      (h.eq_or_disjoint trivial trivial).resolve_right <| Set.not_disjoint_iff.mpr ⟨b, hb, hb'⟩
    exact ⟨rectangle (A i) (A i), ⟨i, rfl⟩, ha, hc⟩

instance (α : ι → Type*) :
    (ofPartition (α := Σ i, α i) (range <| mk ·) (range <| mk ·)).IsTrans :=
  isTrans_ofPartition <| by intro; grind

lemma comapPartition_ofPartition : (ofPartition A B).comapPartition A B = ⊤ := by
  ext i ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  simpa using ⟨i, ha, hb⟩

lemma comapPartition_le_iff_of_subset (hs : s ⊆ ofPartition A B) :
    s.comapPartition A B ≤ r.comapPartition A B ↔ s ⊆ r := by
  refine ⟨fun h ⟨a, b⟩ hmem ↦ ?_, comapPartition_le⟩
  have ⟨i, ha, hb⟩ : ∃ i, a ∈ A i ∧ b ∈ B i := by simpa using hs hmem
  exact @h i ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ hmem

lemma comapPartition_injOn_Iic : (Set.Iic <| ofPartition A B).InjOn (comapPartition A B) := by
  intro s (hs : s ⊆ _) r (hr : r ⊆ _) h
  exact (comapPartition_le_iff_of_subset hs |>.mp h.le).antisymm
    (comapPartition_le_iff_of_subset hr |>.mp h.ge)

lemma comapPartition_comp_of_le {r : SetRel β γ} (hA : Set.univ.PairwiseDisjoint A)
    (hs : s ⊆ ofPartition A B) :
    (s ○ r).comapPartition A C = fun i ↦ s.comapPartition A B i ○ r.comapPartition B C i := by
  ext i ⟨⟨a, ha⟩, ⟨c, hc⟩⟩
  simp only [mem_comapPartition, mem_comp, Subtype.exists, exists_and_left, exists_prop]
  refine ⟨fun ⟨b, hab, hbc⟩ ↦ ⟨b, hab, ?_, hbc⟩, fun ⟨b, hab, hb, hbc⟩ ↦ ⟨b, hab, hbc⟩⟩
  obtain ⟨j, ha', hb⟩ : ∃ j, a ∈ A j ∧ b ∈ B j := by simpa using hs hab
  rwa [(hA.eq_or_disjoint trivial trivial).resolve_right <| Set.not_disjoint_iff.mpr ⟨a, ha, ha'⟩]

variable {ι : Type*} {α β γ : ι → Type*} {s r : ∀ i : ι, SetRel (α i) (β i)}

def piToSigma (r : ∀ i : ι, SetRel (α i) (β i)) : SetRel (Σ i, α i) (Σ i, β i) :=
    ⋃ i, (r i).map (.mk i) (.mk i)

@[simp, grind =]
lemma mem_piToSigma : a ~[piToSigma r] b ↔ ∃ h : a.fst = b.fst, a.snd ~[r a.fst] h ▸ b.snd := by
  simp [piToSigma]; grind

lemma mem_piToSigma' :
    a ~[piToSigma r] b ↔ ∃ i a' b', a' ~[r i] b' ∧ ⟨i, a'⟩ = a ∧ ⟨i, b'⟩ = b := by
  grind

lemma piToSigma_subset_iff : piToSigma s ⊆ piToSigma r ↔ s ≤ r := by
  simp only [Set.subset_def, Prod.forall, mem_piToSigma, forall_exists_index]
  constructor
  · intro h i (a, b) hab
    simpa using h ⟨i, a⟩ ⟨i, b⟩ rfl hab
  · rintro h ⟨i, a⟩ ⟨j, b⟩ (rfl : i = j) (hab : a ~[s i] b)
    exact ⟨rfl, h i hab⟩

lemma piToSigma_inv : piToSigma (fun i ↦ (r i).inv) = (piToSigma r).inv := by
  grind

lemma piToSigma_comp {r : ∀ i : ι, SetRel (β i) (γ i)} :
    piToSigma (fun i ↦ (s i).comp (r i)) = (piToSigma s).comp (piToSigma r) := by
  ext ⟨⟨i, a⟩, ⟨j, c⟩⟩
  simp
  grind

lemma piToSigma_id : piToSigma (fun i ↦ (SetRel.id : SetRel (α i) (α i))) = SetRel.id := by
  grind

lemma piToSigma_union : piToSigma (s ⊔ r) = piToSigma s ∪ piToSigma r := by
  grind [Pi.sup_apply]

lemma piToSigma_inter : piToSigma (s ⊓ r) = piToSigma s ∩ piToSigma r := by
  grind [Pi.inf_apply]

lemma piToSigma_sdiff : piToSigma (s \ r) = piToSigma s \ piToSigma r := by
  grind [Pi.sdiff_apply]

lemma piToSigma_bot : piToSigma (⊥ : Π i, SetRel (α i) (β i)) = ⊥ := by
  ext ⟨⟨i, a⟩, ⟨j, b⟩⟩
  simp

lemma piToSigma_inj : (@piToSigma ι α β).Injective := by
  intro s r h
  ext i ⟨a, b⟩
  simp only [Set.ext_iff, Prod.forall, mem_piToSigma] at h
  simpa using h ⟨i, a⟩ ⟨i, b⟩

-- def sigmaSetoid {ι : Type*} (α β : ι → Type*) : SetRel (Σ i, α i) (Σ i, β i) :=
--   {p | p.1.fst = p.2.fst}

-- @[simp, grind =] lemma mem_sigmaSetoid : a ~[sigmaSetoid α β] b ↔ a.fst = b.fst := .rfl

-- instance : SetRel.IsRefl (sigmaSetoid α α) where
--   refl := by simp

-- instance : SetRel.IsSymm (sigmaSetoid α α) where
--   symm := by simp +contextual

-- instance : SetRel.IsTrans (sigmaSetoid α α) where
--   trans := by simp +contextual

lemma piToSigma_top_eq_sigmaSetoid : piToSigma (⊤ : Π i, SetRel (α i) (β i)) =
  ofPartition (mk · '' ⊤) (mk · '' ⊤) := by
  ext ⟨⟨i, a⟩, ⟨j, b⟩⟩
  simp only [mem_piToSigma, Pi.top_apply, Set.top_eq_univ, Set.mem_univ, exists_prop, and_true,
    Set.image_univ, mem_ofPartition, Set.mem_range, mk.injEq, exists_and_left, ↓existsAndEq,
    heq_eq_eq, exists_eq, and_self, true_and, iff_self_and]
  rintro rfl
  use b

lemma mem_range_piToSigma_iff (r : SetRel (Σ i, α i) (Σ i, β i)) :
    r ∈ Set.range piToSigma ↔ ∀ {x y}, x ~[r] y → x.fst = y.fst := by
  constructor
  · grind
  · intro h
    use fun i ↦ {p | ⟨i, p.1⟩ ~[r] ⟨i, p.2⟩}
    grind

lemma mem_range_piToSigma_iff' (r : SetRel (Σ i, α i) (Σ i, β i)) :
    r ∈ Set.range piToSigma ↔ r ⊆ ofPartition (mk · '' ⊤) (mk · '' ⊤) := by
  constructor
  · simp
    grind
  · intro h
    use fun i ↦ {p | ⟨i, p.1⟩ ~[r] ⟨i, p.2⟩}
    grind

variable {α β γ ι : Type*} {A : ι → Set α} {B : ι → Set β} (C : ι → Set γ)
    {s r : Π i, SetRel (A i) (B i)}

variable (r) in
def mapPartition : SetRel α β := ⋃ i, (r i).map (↑) (↑)

@[simp, grind =] lemma mem_mapPartition_iff :
    a ~[mapPartition r] b ↔ ∃ (i : ι) (ha : a ∈ A i) (hb : b ∈ B i), ⟨a, ha⟩ ~[r i] ⟨b, hb⟩ := by
  simp [mapPartition]

lemma mapPartition_mono (h : s ≤ r) : mapPartition s ⊆ mapPartition r := by
  intro ⟨a, b⟩
  simp_rw [mem_mapPartition_iff, forall_exists_index]
  intro i
  grind [h i]

lemma _root_.Set.PairwiseDisjoint.eq_of_mem {s : Set ι} {f : ι → Set α} (hf : s.PairwiseDisjoint f)
    {i j : ι} (hi : i ∈ s) (hj : j ∈ s) {a : α} (hai : a ∈ f i) (haj : a ∈ f j) : i = j := by
  apply (hf.eq_or_disjoint hi hj).resolve_right
  grind [Set.not_disjoint_iff]

-- lemma pairwiseDisjoint_of_isTrans_ofPartition

lemma mapPartition_comapPartition (hA : Set.univ.PairwiseDisjoint A) (r) :
    (mapPartition r).comapPartition A B = r := by
  ext i ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  rw [mem_comapPartition, mem_mapPartition_iff]
  exact ⟨fun ⟨_, ha', _, h⟩ ↦ hA.eq_of_mem trivial trivial ha ha' ▸ h, (⟨_, _, _, ·⟩)⟩

lemma comapPartition_mapPartition {r} (hr : r ⊆ ofPartition A B) :
    mapPartition (r.comapPartition A B) = r := by
  ext ⟨a, b⟩
  simp
  grind

lemma mapPartition_top : mapPartition (⊤ : Π i, SetRel (A i) (B i)) = ofPartition A B := by
  ext ⟨a, b⟩
  simp

variable (r) in
lemma mapPartition_subset_ofPartition : mapPartition r ⊆ ofPartition A B :=
    mapPartition_top ▸ mapPartition_mono le_top

end Sigma

end SetRel
