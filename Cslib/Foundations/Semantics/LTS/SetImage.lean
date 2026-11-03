/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Yusuf Demir
-/

module

public import Cslib.Foundations.Semantics.LTS.Basic

/-!
# Images of sets of states

The image of a set of states of an `LTS` along a label and along a list of labels, with lemmas on
membership, singletons, the empty set and the empty list, unions, monotonicity and concatenation.

## Main definitions

- `LTS.setImage`: the `μ`-image of a set of states.
- `LTS.setImageMultistep`: the `μs`-image of a set of states, for a list of labels `μs`.

## Main statements

- `LTS.mem_setImage`, `LTS.mem_setImageMultistep`: membership through `Tr` and `MTr`.
- `LTS.setImageMultistep_foldl_setImage`: the multistep image is a left fold of `setImage`.
- `LTS.setImage_union`, `LTS.setImageMultistep_union`: images distribute over unions.
- `LTS.setImageMultistep_append`: the image along `μs₁ ++ μs₂` is the image along `μs₂` of the
  image along `μs₁`.
-/

@[expose] public section

namespace Cslib

universe u v

namespace LTS

variable {State : Type u} {Label : Type v} (lts : LTS State Label)

/-- The `μ`-image of a set of states `S` is the union of all `μ`-images of the states in `S`. -/
@[scoped grind =]
def setImage (S : Set State) (μ : Label) : Set State :=
  ⋃ s ∈ S, lts.image s μ

/-- The `μs`-image of a set of states `S`, where `μs` is a list of labels, is the union of all
`μs`-images of the states in `S`. -/
@[scoped grind =]
def setImageMultistep (S : Set State) (μs : List Label) : Set State :=
  ⋃ s ∈ S, lts.imageMultistep s μs

/-- Characterisation of `setImage` wrt `Tr`. -/
@[scoped grind =]
theorem mem_setImage {lts : LTS State Label} :
  s' ∈ lts.setImage S μ ↔ ∃ s ∈ S, lts.Tr s μ s' := by
  simp only [setImage, Set.mem_iUnion, exists_prop]
  grind

theorem tr_setImage {lts : LTS State Label} (hs : s ∈ S) (htr : lts.Tr s μ s') :
  s' ∈ lts.setImage S μ := by grind

/-- Characterisation of `setImageMultistep` with `MTr`. -/
@[scoped grind =]
theorem mem_setImageMultistep {lts : LTS State Label} :
  s' ∈ lts.setImageMultistep S μs ↔ ∃ s ∈ S, lts.MTr s μs s' := by
  simp only [setImageMultistep, Set.mem_iUnion, exists_prop]
  grind

@[scoped grind <=]
theorem mTr_setImage {lts : LTS State Label} (hs : s ∈ S) (htr : lts.MTr s μs s') :
  s' ∈ lts.setImageMultistep S μs := by grind

/-- The image of the empty set is always the empty set. -/
@[scoped grind =]
theorem setImage_empty (lts : LTS State Label) : lts.setImage ∅ μ = ∅ := by grind

@[scoped grind =]
lemma setImageMultistep_setImage_head (lts : LTS State Label) :
  lts.setImageMultistep S (μ :: μs) = lts.setImageMultistep (lts.setImage S μ ) μs := by grind

/-- Characterisation of `setImageMultistep` as `List.foldl` on `setImage`. -/
@[scoped grind _=_]
theorem setImageMultistep_foldl_setImage (lts : LTS State Label) :
  lts.setImageMultistep = List.foldl lts.setImage := by
  ext S μs s'
  induction μs generalizing S <;> grind

/-- Characterisation of membership in `List.foldl lts.setImage` with `MTr`. -/
@[scoped grind =]
theorem mem_foldl_setImage (lts : LTS State Label) :
  s' ∈ List.foldl lts.setImage S μs ↔ ∃ s ∈ S, lts.MTr s μs s' := by
  rw [← setImageMultistep_foldl_setImage]
  exact mem_setImageMultistep

/-- The image of a singleton is the image of its element. -/
@[simp]
theorem setImage_singleton (s : State) (μ : Label) : lts.setImage {s} μ = lts.image s μ := by
  ext s'
  simp [mem_setImage, image]

/-- Images of sets distribute over binary unions. -/
@[simp, scoped grind =]
theorem setImage_union (S T : Set State) (μ : Label) :
    lts.setImage (S ∪ T) μ = lts.setImage S μ ∪ lts.setImage T μ := by
  ext s'
  simp [mem_setImage, or_and_right, exists_or]

/-- Images of sets distribute over indexed unions. -/
@[simp]
theorem setImage_iUnion {ι : Sort*} (S : ι → Set State) (μ : Label) :
    lts.setImage (⋃ i, S i) μ = ⋃ i, lts.setImage (S i) μ := by
  ext s'
  simp only [mem_setImage, Set.mem_iUnion]
  exact ⟨fun ⟨s, ⟨i, hs⟩, htr⟩ => ⟨i, s, hs, htr⟩, fun ⟨i, s, hs, htr⟩ => ⟨s, ⟨i, hs⟩, htr⟩⟩

/-- Taking the image of a set is monotone. -/
@[gcongr]
theorem setImage_mono {S T : Set State} (h : S ⊆ T) (μ : Label) :
    lts.setImage S μ ⊆ lts.setImage T μ := by
  intro s' hs'
  obtain ⟨s, hs, htr⟩ := mem_setImage.mp hs'
  exact tr_setImage (h hs) htr

/-- The multistep image of a set along the empty list is the set itself. -/
@[simp, scoped grind =]
theorem setImageMultistep_nil (S : Set State) : lts.setImageMultistep S [] = S := by
  ext s'
  simp [mem_setImageMultistep]

/-- The multistep image of the empty set is empty. -/
@[simp, scoped grind =]
theorem setImageMultistep_empty (μs : List Label) : lts.setImageMultistep ∅ μs = ∅ := by
  ext s'
  simp [mem_setImageMultistep]

/-- The multistep image of a singleton is the multistep image of its element. -/
@[simp]
theorem setImageMultistep_singleton (s : State) (μs : List Label) :
    lts.setImageMultistep {s} μs = lts.imageMultistep s μs := by
  ext s'
  simp [mem_setImageMultistep, imageMultistep]

/-- Multistep images of sets distribute over binary unions. -/
@[simp, scoped grind =]
theorem setImageMultistep_union (S T : Set State) (μs : List Label) :
    lts.setImageMultistep (S ∪ T) μs =
      lts.setImageMultistep S μs ∪ lts.setImageMultistep T μs := by
  ext s'
  simp [mem_setImageMultistep, or_and_right, exists_or]

/-- Multistep images of sets distribute over indexed unions. -/
@[simp]
theorem setImageMultistep_iUnion {ι : Sort*} (S : ι → Set State) (μs : List Label) :
    lts.setImageMultistep (⋃ i, S i) μs = ⋃ i, lts.setImageMultistep (S i) μs := by
  ext s'
  simp only [mem_setImageMultistep, Set.mem_iUnion]
  exact ⟨fun ⟨s, ⟨i, hs⟩, hmtr⟩ => ⟨i, s, hs, hmtr⟩, fun ⟨i, s, hs, hmtr⟩ => ⟨s, ⟨i, hs⟩, hmtr⟩⟩

/-- Taking the multistep image of a set is monotone. -/
@[gcongr]
theorem setImageMultistep_mono {S T : Set State} (h : S ⊆ T) (μs : List Label) :
    lts.setImageMultistep S μs ⊆ lts.setImageMultistep T μs := by
  intro s' hs'
  obtain ⟨s, hs, hmtr⟩ := mem_setImageMultistep.mp hs'
  exact mTr_setImage (h hs) hmtr

/-- The multistep image along `μs₁ ++ μs₂` is the multistep image along `μs₂` of the multistep
image along `μs₁`. -/
@[simp]
theorem setImageMultistep_append (S : Set State) (μs₁ μs₂ : List Label) :
    lts.setImageMultistep S (μs₁ ++ μs₂) =
      lts.setImageMultistep (lts.setImageMultistep S μs₁) μs₂ := by
  rw [setImageMultistep_foldl_setImage, List.foldl_append]

end LTS

end Cslib
