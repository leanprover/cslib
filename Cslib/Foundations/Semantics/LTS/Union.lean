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
[DecidablePred S1] [DecidablePred L1] [DecidablePred S2] [DecidablePred L2]
(lts1 : LTS (@Subtype State S1) (@Subtype Label L1))
(lts2 : LTS (@Subtype State S2) (@Subtype Label L2)) :
  LTS State Label where
  Tr := fun s μ s' =>
    if h : S1 s ∧ L1 μ ∧ S1 s' then
      lts1.Tr ⟨s, h.1⟩ ⟨μ, h.2.1⟩ ⟨s', h.2.2⟩
    else if h : S2 s ∧ L2 μ ∧ S2 s' then
      lts2.Tr ⟨s, h.1⟩ ⟨μ, h.2.1⟩ ⟨s', h.2.2⟩
    else
      False

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

end Cslib.LTS
