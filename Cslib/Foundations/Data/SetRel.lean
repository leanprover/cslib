/-
Copyright (c) 2026 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/

module

public import Mathlib.Basic.Rel
public import Mathlib.Data.Set.Sigma

/-!-/

@[expose] public section

namespace SetRel

section Map

variable {α β γ α' β' γ' : Type*} {f : α → α'} {g : β → β'} {h : γ → γ'} {s r : SetRel α β}

protected def map (f : α → α') (g : β → β') (r : SetRel α β) : SetRel α' β' := Prod.map f g '' r

@[simp, grind =] lemma mem_map : c ~[r.map f g] d ↔ ∃ a b, a ~[r] b ∧ f a = c ∧ g b = d := by
  simp [SetRel.map]

lemma map_mem_map (h : a ~[r] b) : f a ~[r.map f g] g b := mem_map.mpr ⟨a, b, h, rfl, rfl⟩

@[simp] lemma inv_map : (s.map f g).inv = s.inv.map g f := by ext ⟨c, d⟩; grind

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

@[simp] lemma map_bot : (⊥ : SetRel α β).map f g = ⊥ := by
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
    {g₂ : β₂ → β₃} {s : SetRel α₁ β₁} : s.map (f₂ ∘ f₁) (g₂ ∘ g₁) = (s.map f₁ g₁).map f₂ g₂ :=
  Set.image_comp (Prod.map f₂ g₂) (Prod.map f₁ g₁) s

@[simps]
def mapEquiv (eα : α ≃ α') (eβ : β ≃ β') : SetRel α β ≃ SetRel α' β' where
  toFun s := s.map eα eβ
  invFun s := s.map eα.symm eβ.symm
  left_inv _ := by simp [← map_comp_fun]
  right_inv _ := by simp [← map_comp_fun]

def ofRel (r : α → β → Prop) : SetRel α β := {p | r p.1 p.2}

@[simp, grind =] lemma mk_mem_ofRel {r : α → β → Prop} : x ~[ofRel r] y ↔ r x y := .rfl

end Map

section Sigma

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

def sigmaSetoid {ι : Type*} (α β : ι → Type*) : SetRel (Σ i, α i) (Σ i, β i) :=
  {p | p.1.fst = p.2.fst}

@[simp, grind =] lemma mem_sigmaSetoid : a ~[sigmaSetoid α β] b ↔ a.fst = b.fst := .rfl

instance : SetRel.IsRefl (sigmaSetoid α α) where
  refl := by simp

instance : SetRel.IsSymm (sigmaSetoid α α) where
  symm := by simp +contextual

instance : SetRel.IsTrans (sigmaSetoid α α) where
  trans := by simp +contextual

lemma piToSigma_top_eq_sigmaSetoid :
    piToSigma (⊤ : Π i, SetRel (α i) (β i)) = sigmaSetoid α β := by
  ext ⟨⟨i, a⟩, ⟨j, b⟩⟩
  simp

lemma mem_range_piToSigma_iff (r : SetRel (Σ i, α i) (Σ i, β i)) :
    r ∈ Set.range piToSigma ↔ ∀ {x y}, x ~[r] y → x.fst = y.fst := by
  constructor
  · grind
  · intro h
    use fun i ↦ {p | ⟨i, p.1⟩ ~[r] ⟨i, p.2⟩}
    grind

lemma mem_range_piToSigma_iff' (r : SetRel (Σ i, α i) (Σ i, β i)) :
    r ∈ Set.range piToSigma ↔ r ⊆ sigmaSetoid α β := by
  constructor
  · grind
  · intro h
    use fun i ↦ {p | ⟨i, p.1⟩ ~[r] ⟨i, p.2⟩}
    grind

end Sigma

end SetRel
