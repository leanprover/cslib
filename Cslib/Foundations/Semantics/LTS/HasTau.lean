/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Foundations.Semantics.LTS.Basic

@[expose] public section

/-!
# LTS with a special "internal" transition `τ`.
-/

namespace Cslib

universe u v

/-! ## Weak transitions (single- and multistep) -/
section Weak

/-- A type of transition labels that includes a special 'internal' transition `τ`. -/
class HasTau (Label : Type v) where
  /-- The internal transition label, also known as τ. -/
  τ : Label

/-- Saturated τ-transition relation. -/
def LTS.τSTr [HasTau Label] (lts : LTS State Label) : State → State → Prop :=
  Relation.ReflTransGen (Tr.toRelation lts HasTau.τ)

/-- Saturated transition relation. -/
inductive LTS.STr [HasTau Label] (lts : LTS State Label) : State → Label → State → Prop where
| refl : lts.STr s HasTau.τ s
| tr : lts.τSTr s1 s2 → lts.Tr s2 μ s3 → lts.τSTr s3 s4 → lts.STr s1 μ s4

/-- The `LTS` obtained by saturating the transition relation in `lts`. -/
@[scoped grind =]
def LTS.saturate [HasTau Label] (lts : LTS State Label) : LTS State Label where
  Tr := lts.STr

@[scoped grind _=_]
theorem LTS.saturate_tr_sTr [HasTau Label] {lts : LTS State Label} :
  lts.saturate.Tr = lts.STr := by rfl

/-- Any transition is also a saturated transition. -/
theorem LTS.STr.single [HasTau Label] (lts : LTS State Label) :
    lts.Tr s μ s' → lts.STr s μ s' := by
  intro h
  apply LTS.STr.tr .refl h .refl

/-- STr transitions labeled by HasTau.τ are exactly the τSTr transitions. -/
theorem LTS.sTr_τSTr [HasTau Label] (lts : LTS State Label) :
  lts.STr s HasTau.τ s' ↔ lts.τSTr s s' := by
  apply Iff.intro <;> intro h
  case mp =>
    cases h
    case refl => exact .refl
    case tr _ _ h1 h2 h3 =>
      exact (.trans h1 (.head h2 h3))
  case mpr =>
    cases h
    case refl => exact LTS.STr.refl
    case tail _ h1 h2 => exact LTS.STr.tr h1 h2 .refl

/-- In a saturated LTS, the transition and saturated transition relations are the same. -/
theorem LTS.saturate_τSTr_τSTr [hHasTau : HasTau Label] (lts : LTS State Label)
  : lts.saturate.τSTr s = lts.τSTr s := by
  ext s''
  apply Iff.intro <;> intro h
  case mp =>
    induction h
    case refl => constructor
    case tail _ _ _ h2 h3 => exact Relation.ReflTransGen.trans h3 ((LTS.sTr_τSTr _).mp h2)
  case mpr =>
    cases h
    case refl => constructor
    case tail s' h2 h3 =>
      have h4 := LTS.STr.tr h2 h3 Relation.ReflTransGen.refl
      exact Relation.ReflTransGen.single h4

/-- Saturated transitions labelled by τ can be composed. -/
@[scoped grind .]
theorem LTS.STr.trans_τ
  [HasTau Label] (lts : LTS State Label)
  (h1 : lts.STr s1 HasTau.τ s2) (h2 : lts.STr s2 HasTau.τ s3) :
  lts.STr s1 HasTau.τ s3 := by
  rw [LTS.sTr_τSTr _] at h1 h2
  rw [LTS.sTr_τSTr _]
  apply Relation.ReflTransGen.trans h1 h2

/-- Saturated transitions can be composed. -/
theorem LTS.STr.comp
  [HasTau Label] (lts : LTS State Label)
  (h1 : lts.STr s1 HasTau.τ s2)
  (h2 : lts.STr s2 μ s3)
  (h3 : lts.STr s3 HasTau.τ s4) :
  lts.STr s1 μ s4 := by
  rw [LTS.sTr_τSTr _] at h1 h3
  cases h2
  case refl =>
    rw [LTS.sTr_τSTr _]
    apply Relation.ReflTransGen.trans h1 h3
  case tr _ _ hτ1 htr hτ2 =>
    exact LTS.STr.tr (Relation.ReflTransGen.trans h1 hτ1) htr (Relation.ReflTransGen.trans hτ2 h3)

/-- In a saturated LTS, the transition and saturated transition relations are the same. -/
theorem LTS.saturate_tr_saturate_sTr [hHasTau : HasTau Label] (lts : LTS State Label)
  (hμ : μ = hHasTau.τ) : lts.saturate.Tr s μ = lts.saturate.STr s μ := by
  ext s'
  apply Iff.intro <;> intro h
  case mp =>
    cases h
    case refl => constructor
    case tr hstr1 htr hstr2 =>
      apply LTS.STr.single
      exact LTS.STr.tr hstr1 htr hstr2
  case mpr =>
    cases h
    case refl => constructor
    case tr hstr1 htr hstr2 =>
      rw [LTS.saturate_τSTr_τSTr lts] at hstr1 hstr2
      rw [←LTS.sTr_τSTr lts] at hstr1 hstr2
      exact LTS.STr.comp lts hstr1 htr hstr2

/-- In a saturated LTS, every state is in its τ-image. -/
@[scoped grind .]
theorem LTS.mem_saturate_image_τ [HasTau Label] (lts : LTS State Label) :
  s ∈ lts.saturate.image s HasTau.τ := LTS.STr.refl

/-- The `τ`-closure of a set of states `S` is the set of states reachable by any state in `S`
by performing only `τ`-transitions. -/
def LTS.τClosure [HasTau Label] (lts : LTS State Label) (S : Set State) : Set State :=
  lts.saturate.setImage S HasTau.τ

end Weak

end Cslib
