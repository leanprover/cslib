/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Init
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Order.SetNotation

/-!
# Labelled Transition System (LTS)

A Labelled Transition System (`LTS`) models the observable behaviour of the possible states of a
system. They are particularly popular in the fields of concurrency theory, logic, and programming
languages.

## Main definitions

- `LTS` is a structure for labelled transition systems, consisting of a labelled transition
relation `Tr` between states. We follow the style and conventions in [Sangiorgi2011].

- `LTS.MTr` extends the transition relation of any LTS to a multistep transition relation,
formalising the inference system and admissible rules for such relations in [Montesi2023].

- Definitions for all the common classes of LTSs: image-finite, finitely branching, finite-state,
finite, and deterministic.

## Main statements

- A series of results on `LTS.MTr` that allow for obtaining and composing multistep transitions in
different ways.

- `LTS.deterministic_imageFinite`: every deterministic LTS is also image-finite.

- `LTS.finiteState_imageFinite`: every finite-state LTS is also image-finite.

- `LTS.finiteState_finitelyBranching`: every finite-state LTS is also finitely-branching, if the
type of labels is finite.

## References

* [F. Montesi, *Introduction to Choreographies*][Montesi2023]
* [D. Sangiorgi, *Introduction to Bisimulation and Coinduction*][Sangiorgi2011]
-/

@[expose] public section

namespace Cslib

universe u v

/--
A Labelled Transition System (LTS) for a type of states (`State`) and a type of transition
labels (`Label`) consists of a labelled transition relation (`Tr`).
-/
structure LTS (State : Type u) (Label : Type v) where
  /-- The transition relation. -/
  Tr : State → Label → State → Prop

namespace LTS

section MultiStep

/-! ## Multistep transitions and executions with finite traces

This section treats executions with a finite number of steps.
-/

variable {State : Type u} {Label : Type v} (lts : LTS State Label)

/--
Definition of a multistep transition.

(Implementation note: compared to [Montesi2023], we choose stepL instead of stepR as fundamental
rule. This makes working with lists of labels more convenient, because we follow the same
construction. It is also similar to what is done in the `SimpleGraph` library in mathlib.)
-/
@[scoped grind, mk_iff]
inductive MTr (lts : LTS State Label) : State → List Label → State → Prop where
  | refl {s : State} : lts.MTr s [] s
  | stepL {s1 : State} {μ : Label} {s2 : State} {μs : List Label} {s3 : State} :
    lts.Tr s1 μ s2 → lts.MTr s2 μs s3 →
    lts.MTr s1 (μ :: μs) s3

/-- In any zero-steps multistep transition, the origin and the derivative are the same. -/
@[scoped grind .]
theorem MTr.nil_eq (h : lts.MTr s1 [] s2) : s1 = s2 := by
  cases h
  rfl

@[simp] theorem MTr.nil_iff (s1 s2 : State) : lts.MTr s1 [] s2 ↔ s1 = s2 :=
  ⟨nil_eq lts, fun h => h ▸ MTr.refl⟩

/-- Any transition is also a multistep transition. -/
@[scoped grind →]
theorem MTr.single {s1 : State} {μ : Label} {s2 : State} :
  lts.Tr s1 μ s2 → lts.MTr s1 [μ] s2 := by
  intro h
  apply MTr.stepL
  · exact h
  · apply MTr.refl

/-- A multistep transition along `μ :: μs` is a transition labelled by `μ` plus a multistep
transition labelled by `μs`. -/
theorem MTr.cons_iff {lts : LTS State Label} :
    lts.MTr s1 (μ :: μs) s2 ↔ ∃ s, lts.Tr s1 μ s ∧ lts.MTr s μs s2 := by
  constructor
  · rintro (_ | ⟨htr, hmtr⟩)
    exact ⟨_, htr, hmtr⟩
  · intro ⟨s, htr, hmtr⟩
    exact .stepL htr hmtr

/-- Any multistep transition can be extended by adding a transition. -/
theorem MTr.stepR {s1 : State} {μs : List Label} {s2 : State} {μ : Label} {s3 : State} :
  lts.MTr s1 μs s2 → lts.Tr s2 μ s3 → lts.MTr s1 (μs ++ [μ]) s3 := by
  intro h1 h2
  induction h1
  case refl s1' => exact MTr.single lts h2
  case stepL s1' μ' s2' μs' s3' h1' h3 ih =>
    apply MTr.stepL
    · exact h1'
    · apply ih h2

/-- Multistep transitions can be composed. -/
@[scoped grind <=]
theorem MTr.comp {s1 : State} {μs1 : List Label} {s2 : State} {μs2 : List Label} {s3 : State} :
  lts.MTr s1 μs1 s2 → lts.MTr s2 μs2 s3 →
  lts.MTr s1 (μs1 ++ μs2) s3 := by
  intro h1 h2
  induction h1
  case refl => assumption
  case stepL s1 μ s' μs1' s'' h1' h3 ih  =>
    apply MTr.stepL
    · exact h1'
    · apply ih h2

/-- Any 1-sized multistep transition implies a transition with the same states and label. -/
@[scoped grind .]
theorem MTr.single_invert (s1 : State) (μ : Label) (s2 : State) :
  lts.MTr s1 [μ] s2 → lts.Tr s1 μ s2 := by
  intro h
  cases h
  case stepL s1' htr hmtr =>
    cases hmtr
    exact htr

/-- A 1-sized multistep transition is exactly a single transision with the given label. -/
@[simp] theorem MTr.singleton_iff (s1 : State) (μ : Label) (s2 : State) :
  lts.MTr s1 [μ] s2 ↔ lts.Tr s1 μ s2 := ⟨MTr.single_invert lts s1 μ s2, MTr.single lts⟩

/-- A multistep transition over a concatenation can be split into two multistep transitions. -/
theorem MTr.split {lts : LTS State Label} (h : lts.MTr s1 (μs ++ μs') s2) :
    ∃ s, lts.MTr s1 μs s ∧ lts.MTr s μs' s2 := by
  induction μs generalizing s1 s2 with
  | nil => use s1, .refl, h
  | cons μ μs ih =>
    rw [List.cons_append] at h
    cases h
    case stepL s htr hmtr =>
      obtain ⟨s', hmtr', hmtr''⟩ := ih hmtr
      use s', .stepL htr hmtr', hmtr''

/-- Multistep-transitions over `μs ++ μs'` are exactly multistep transitions over `μs` and `μs'`
with a common end & start state (respectively). -/
theorem MTr.append_iff : lts.MTr s1 (μs ++ μs') s2 ↔ ∃ s, lts.MTr s1 μs s ∧ lts.MTr s μs' s2 := by
  refine ⟨MTr.split, ?_⟩
  intro ⟨_, h, h'⟩
  exact h.comp lts h'

/-- A state `s1` can reach a state `s2` if there exists a multistep transition from
`s1` to `s2`. -/
@[scoped grind =]
def CanReach (s1 s2 : State) : Prop :=
  ∃ μs, lts.MTr s1 μs s2

/-- Any state can reach itself. -/
@[scoped grind .]
theorem CanReach.refl (s : State) : lts.CanReach s s := by
  exists []
  apply MTr.refl

/-- The LTS generated by a state `s` is the LTS given by all the states reachable from `s`. -/
@[scoped grind =]
def generatedBy (s : State) : LTS {s' : State // lts.CanReach s s'} Label where
  Tr := fun s1 μ s2 => lts.CanReach s s1 ∧ lts.CanReach s s2 ∧ lts.Tr s1 μ s2

end MultiStep

section Classes
/-!
### Classes of LTSs
-/

variable {State : Type u} {Label : Type v} (lts : LTS State Label)

/-- An lts is deterministic if a state cannot reach different states with the same transition
label. -/
@[scoped grind]
class Deterministic (lts : LTS State Label) where
  deterministic (s1 : State) (μ : Label) (s2 s3 : State) :
    lts.Tr s1 μ s2 → lts.Tr s1 μ s3 → s2 = s3

theorem Deterministic.eq_of_tr {lts : LTS State Label} [lts.Deterministic]
    (htr : lts.Tr s1 μ s2) (htr' : lts.Tr s1 μ s2') : s2 = s2' :=
  Deterministic.deterministic s1 μ s2 s2' htr htr'

/-- In a deterministic lts, multistep transitions with a given start state and trace reach a unique
end state. -/
theorem Deterministic.eq_of_mTr {lts : LTS State Label} [lts.Deterministic]
    (hmtr : lts.MTr s1 μs s2) (hmtr' : lts.MTr s1 μs s2') : s2 = s2' := by
  induction μs generalizing s1 s2 s2' with
  | nil => grind
  | cons μ μs ih =>
    rcases hmtr with (_ | ⟨htr, hmtr⟩); rcases hmtr' with (_ | ⟨htr', hmtr'⟩)
    rw [eq_of_tr htr htr'] at hmtr
    exact ih hmtr hmtr'

/-- The `μ`-image of a state `s` is the set of all `μ`-derivatives of `s`. -/
@[scoped grind =]
def image (s : State) (μ : Label) : Set State := { s' : State | lts.Tr s μ s' }

/-- The `μs`-image of a state `s`, where `μs` is a list of labels, is the set of all
`μs`-derivatives of `s`. -/
@[scoped grind =]
def imageMultistep (s : State) (μs : List Label) : Set State :=
  { s' : State | lts.MTr s μs s' }

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

/-- An lts is image-finite if all images of its states are finite. -/
abbrev ImageFinite := ∀ s μ, Finite (lts.image s μ)

/-- In a deterministic LTS, if a state has a `μ`-derivative, then it can have no other
`μ`-derivative. -/
@[scoped grind .]
theorem deterministic_not_lto [h : lts.Deterministic] :
  ∀ s μ s' s'', s' ≠ s'' → lts.Tr s μ s' → ¬lts.Tr s μ s'' := by grind

@[scoped grind _=_]
theorem deterministic_tr_image_singleton [lts.Deterministic] :
    lts.image s μ = {s'} ↔ lts.Tr s μ s' := by
  have := (lts.image s μ).eq_singleton_iff_unique_mem (a := s')
  grind

/-- In a deterministic LTS, any image is either a singleton or the empty set. -/
@[scoped grind .]
theorem deterministic_image_char [lts.Deterministic] (s : State) (μ : Label) :
    (∃ s', lts.image s μ = { s' }) ∨ (lts.image s μ = ∅) := by grind

/-- In a deterministic LTS, the image of any state-label combination is finite. -/
instance [lts.Deterministic] (s : State) (μ : Label) : Finite (lts.image s μ) := by
  have hDet := deterministic_image_char lts s μ
  cases hDet
  case inl hDet =>
    obtain ⟨s', hDet'⟩ := hDet
    simp only [hDet']
    apply Set.finite_singleton
  case inr hDet =>
    simp only [hDet]
    apply Set.finite_empty

/-- Every deterministic LTS is also image-finite. -/
instance deterministic_imageFinite [lts.Deterministic] : lts.ImageFinite := inferInstance

/-- Every finite-state LTS is also image-finite. -/
@[scoped grind .]
instance finiteState_imageFinite [Finite State] : lts.ImageFinite := inferInstance

/-- A state has an outgoing label `μ` if it has a `μ`-derivative. -/
def HasOutLabel (s : State) (μ : Label) : Prop :=
  ∃ s', lts.Tr s μ s'

/-- The set of outgoing labels of a state. -/
def outgoingLabels (s : State) := { μ | lts.HasOutLabel s μ }

/-- An LTS is finitely branching if it is image-finite and all states have finite sets of
outgoing labels. -/
class FinitelyBranching where
  [image_finite : lts.ImageFinite]
  [finite_state : ∀ s, Finite (lts.outgoingLabels s)]

attribute [instance] FinitelyBranching.image_finite FinitelyBranching.finite_state

/-- Every LTS with finite types for states and labels is also finitely branching. -/
instance FinitelyBranching.of_finite [Finite State] [Finite Label] : lts.FinitelyBranching where

/-- An LTS is acyclic if there are no infinite multistep transitions. -/
class Acyclic (lts : LTS State Label) where
  acyclic : ∃ n, ∀ s1 μs s2, lts.MTr s1 μs s2 → μs.length < n

/-- An LTS is finite if it is finite-state and acyclic.

We call this `FiniteLTS` instead of just `Finite` to avoid confusion with the standard `Finite`
class. -/
class FiniteLTS [Finite State] (lts : LTS State Label) extends lts.Acyclic

end Classes

end LTS

end Cslib
