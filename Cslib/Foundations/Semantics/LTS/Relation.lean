/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Foundations.Semantics.LTS.Basic

/-!
# Conversions between `LTS` and `Relation`.
-/

@[expose] public section

namespace Cslib.LTS

variable {State Label : Type*}

/-- Returns the relation that relates all states `s1` and `s2` via a fixed transition label `μ`. -/
def Tr.toRelation (lts : LTS State Label) (μ : Label) : State → State → Prop :=
  fun s1 s2 => lts.Tr s1 μ s2

/-- Any homogeneous relation can be seen as an LTS where all transitions have the same label. -/
def Relation.toLTS [DecidableEq Label] (r : State → State → Prop) (μ : Label) :
  LTS State Label where
  Tr := fun s1 μ' s2 => if μ' = μ then r s1 s2 else False

/-- Returns the relation that relates all states `s1` and `s2` via a fixed list of transition
labels `μs`. -/
def MTr.toRelation (lts : LTS State Label) (μs : List Label) : State → State → Prop :=
  fun s1 s2 => lts.MTr s1 μs s2

/-! ### Calc tactic support for MTr -/

/-- Transitions can be chained. -/
instance (lts : LTS State Label) :
  Trans
    (Tr.toRelation lts μ1)
    (Tr.toRelation lts μ2)
    (MTr.toRelation lts [μ1, μ2]) where
  trans := by
    intro s1 s2 s3 htr1 htr2
    apply MTr.single at htr1
    apply MTr.single at htr2
    apply MTr.comp lts htr1 htr2

/-- Transitions can be chained with multi-step transitions. -/
instance (lts : LTS State Label) :
  Trans
    (Tr.toRelation lts μ)
    (MTr.toRelation lts μs)
    (MTr.toRelation lts (μ :: μs)) where
  trans := by
    intro s1 s2 s3 htr1 hmtr2
    apply MTr.single at htr1
    apply MTr.comp lts htr1 hmtr2

/-- Multi-step transitions can be chained with transitions. -/
instance (lts : LTS State Label) :
  Trans
    (MTr.toRelation lts μs)
    (Tr.toRelation lts μ)
    (MTr.toRelation lts (μs ++ [μ])) where
  trans := by
    intro s1 s2 s3 hmtr1 htr2
    apply MTr.single at htr2
    apply MTr.comp lts hmtr1 htr2

/-- Multi-step transitions can be chained. -/
instance (lts : LTS State Label) :
  Trans
    (MTr.toRelation lts μs1)
    (MTr.toRelation lts μs2)
    (MTr.toRelation lts (μs1 ++ μs2)) where
  trans := by
    intro s1 s2 s3 hmtr1 hmtr2
    apply MTr.comp lts hmtr1 hmtr2

end Cslib.LTS
