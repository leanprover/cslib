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

variable {α β γ δ : Type*} {f : α → γ} {g : β → δ} {s r : SetRel α β}

protected def map (f : α → γ) (g : β → δ) (r : SetRel α β) : SetRel γ δ := Prod.map f g '' r

@[simp, grind =] lemma mem_map : c ~[r.map f g] d ↔ ∃ a b, a ~[r] b ∧ f a = c ∧ g b = d := by
  simp [SetRel.map]

lemma map_mem_map (h : a ~[r] b) : f a ~[r.map f g] g b := mem_map.mpr ⟨a, b, h, rfl, rfl⟩

lemma inv_map : (s.map f g).inv = s.inv.map g f := by ext ⟨c, d⟩; grind

lemma map_subset_map (h : s ⊆ r) : s.map f g ⊆ r.map f g := Set.image_mono h

@[simp] lemma map_union : (s ∪ r).map f g = s.map f g ∪ r.map f g := Set.image_union ..

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

lemma piToSigma_inj : (@piToSigma ι α β).Injective := by
  intro s r h
  ext i ⟨a, b⟩
  simp only [Set.ext_iff, Prod.forall, mem_piToSigma] at h
  simpa using h ⟨i, a⟩ ⟨i, b⟩

lemma mem_range_piToSigma_iff (r : SetRel (Σ i, α i) (Σ i, β i)) :
    r ∈ Set.range piToSigma ↔ ∀ {x y}, x ~[r] y → x.fst = y.fst := by
  constructor
  · grind
  · intro h
    use fun i ↦ {p | ⟨i, p.1⟩ ~[r] ⟨i, p.2⟩}
    grind

end Sigma

end SetRel
