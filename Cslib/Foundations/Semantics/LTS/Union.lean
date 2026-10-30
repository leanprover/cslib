/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Foundations.Semantics.LTS.Basic

/-!
# Union of LTSs

Note: there is a nontrivial balance between ergonomics and generality here. These definitions might
change in the future.
-/

@[expose] public section

namespace Cslib.LTS

universe u v

variable {State : Type u} {Label : Type v}

/-- The union of two LTSs defined on the same types. -/
def union (lts1 lts2 : LTS State Label) : LTS State Label where
  Tr := lts1.Tr ⊔ lts2.Tr

/-- The union of two LTSs that have common supertypes for states and labels. -/
def unionSubtype
{S1 : State → Prop} {L1 : Label → Prop} {S2 : State → Prop} {L2 : Label → Prop}
(lts1 : LTS (@Subtype State S1) (@Subtype Label L1))
(lts2 : LTS (@Subtype State S2) (@Subtype Label L2)) :
  LTS State Label where
  Tr := fun s μ s' =>
    (∃ h : S1 s ∧ L1 μ ∧ S1 s', lts1.Tr ⟨s, h.1⟩ ⟨μ, h.2.1⟩ ⟨s', h.2.2⟩) ∨
    (∃ h : S2 s ∧ L2 μ ∧ S2 s', lts2.Tr ⟨s, h.1⟩ ⟨μ, h.2.1⟩ ⟨s', h.2.2⟩)

/-- Lifting of an `LTS State Label` to `LTS (State ⊕ State') Label`. -/
def inl (lts : LTS State Label) :
    LTS { x : State ⊕ State' // x.isLeft } { _label : Label // True } where
  Tr s μ s' :=
    match s, s' with
    | ⟨.inl s1, _⟩, ⟨.inl s2, _⟩ => lts.Tr s1 μ s2
    | _, _ => False

/-- Lifting of an `LTS State Label` to `LTS (State' ⊕ State) Label`. -/
def inr (lts : LTS State Label) :
    LTS { x : State' ⊕ State // x.isRight } { _label : Label // True } where
  Tr s μ s' :=
    match s, s' with
    | ⟨.inr s1, _⟩, ⟨.inr s2, _⟩ => lts.Tr s1 μ s2
    | _, _ => False

/-- Union of two LTSs with the same `Label` type. The result combines the original respective
state types `State1` and `State2` into `(State1 ⊕ State2)`. -/
def unionSum (lts1 : LTS State1 Label) (lts2 : LTS State2 Label) :
    LTS (State1 ⊕ State2) Label :=
  unionSubtype lts1.inl lts2.inr

section unionSum

variable {State1 State2 : Type*} {lts1 : LTS State1 Label} {lts2 : LTS State2 Label}

@[simp]
theorem unionSum_tr_inl_inl {s s' : State1} {μ : Label} :
    (unionSum lts1 lts2).Tr (.inl s) μ (.inl s') ↔ lts1.Tr s μ s' := by
  simp [unionSum, unionSubtype, LTS.inl]

@[simp]
theorem unionSum_tr_inr_inr {s s' : State2} {μ : Label} :
    (unionSum lts1 lts2).Tr (.inr s) μ (.inr s') ↔ lts2.Tr s μ s' := by
  simp [unionSum, unionSubtype, LTS.inr]

@[simp]
theorem unionSum_not_tr_inl_inr {s : State1} {s' : State2} {μ : Label} :
    ¬(unionSum lts1 lts2).Tr (.inl s) μ (.inr s') := by
  simp [unionSum, unionSubtype]

@[simp]
theorem unionSum_not_tr_inr_inl {s : State2} {s' : State1} {μ : Label} :
    ¬(unionSum lts1 lts2).Tr (.inr s) μ (.inl s') := by
  simp [unionSum, unionSubtype]

/-- A run of `unionSum lts1 lts2` from a state of `lts1` stays among the states of `lts1`, where it
is a run of `lts1`. -/
theorem unionSum_mTr_inl {s : State1} {μs : List Label} {y : State1 ⊕ State2}
    (h : (unionSum lts1 lts2).MTr (.inl s) μs y) : ∃ t, y = .inl t ∧ lts1.MTr s μs t := by
  induction μs generalizing s with
  | nil =>
    cases h
    exact ⟨s, rfl, .refl⟩
  | cons μ μs ih =>
    obtain ⟨z, htr, h'⟩ := MTr.cons_iff.mp h
    rcases z with z | z
    · obtain ⟨t, rfl, hrun⟩ := ih h'
      exact ⟨t, rfl, .stepL (unionSum_tr_inl_inl.mp htr) hrun⟩
    · exact absurd htr unionSum_not_tr_inl_inr

/-- A run of `unionSum lts1 lts2` from a state of `lts2` stays among the states of `lts2`, where it
is a run of `lts2`. -/
theorem unionSum_mTr_inr {s : State2} {μs : List Label} {y : State1 ⊕ State2}
    (h : (unionSum lts1 lts2).MTr (.inr s) μs y) : ∃ t, y = .inr t ∧ lts2.MTr s μs t := by
  induction μs generalizing s with
  | nil =>
    cases h
    exact ⟨s, rfl, .refl⟩
  | cons μ μs ih =>
    obtain ⟨z, htr, h'⟩ := MTr.cons_iff.mp h
    rcases z with z | z
    · exact absurd htr unionSum_not_tr_inr_inl
    · obtain ⟨t, rfl, hrun⟩ := ih h'
      exact ⟨t, rfl, .stepL (unionSum_tr_inr_inr.mp htr) hrun⟩

/-- The runs of `unionSum lts1 lts2` between states of `lts1` are the runs of `lts1`. -/
theorem unionSum_mTr_inl_iff {s t : State1} {μs : List Label} :
    (unionSum lts1 lts2).MTr (.inl s) μs (.inl t) ↔ lts1.MTr s μs t := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨t', ht', hrun⟩ := unionSum_mTr_inl h
    obtain rfl := Sum.inl.inj ht'
    exact hrun
  · induction h with
    | refl => exact .refl
    | stepL htr _ ih => exact .stepL (unionSum_tr_inl_inl.mpr htr) ih

/-- The runs of `unionSum lts1 lts2` between states of `lts2` are the runs of `lts2`. -/
theorem unionSum_mTr_inr_iff {s t : State2} {μs : List Label} :
    (unionSum lts1 lts2).MTr (.inr s) μs (.inr t) ↔ lts2.MTr s μs t := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨t', ht', hrun⟩ := unionSum_mTr_inr h
    obtain rfl := Sum.inr.inj ht'
    exact hrun
  · induction h with
    | refl => exact .refl
    | stepL htr _ ih => exact .stepL (unionSum_tr_inr_inr.mpr htr) ih

end unionSum

end Cslib.LTS
