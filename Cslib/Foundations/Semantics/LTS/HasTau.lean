/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Foundations.Semantics.LTS.Relation

/-!
# LTS with a special "internal" transition `τ`.
-/

@[expose] public section

namespace Cslib

universe u v

/-- A type of transition labels that includes a special 'internal' transition `τ`. -/
class HasTau (Label : Type v) where
  /-- The internal transition label, also known as τ. -/
  τ : Label

namespace LTS

/-- Saturated τ-transition relation. -/
def τSTr [HasTau Label] (lts : LTS State Label) : State → State → Prop :=
  Relation.ReflTransGen (Tr.toRelation lts HasTau.τ)

@[scoped grind .]
theorem τSTr.refl [HasTau Label] {lts : LTS State Label} : lts.τSTr s s :=
  Relation.ReflTransGen.refl

/-- Saturated transition relation. -/
inductive STr [HasTau Label] (lts : LTS State Label) : State → Label → State → Prop where
  | refl : lts.STr s HasTau.τ s
  | tr : lts.τSTr s1 s2 → lts.Tr s2 μ s3 → lts.τSTr s3 s4 → lts.STr s1 μ s4

/-- The `LTS` obtained by saturating the transition relation in `lts`. -/
@[scoped grind =]
def saturate [HasTau Label] (lts : LTS State Label) : LTS State Label where
  Tr := lts.STr

@[scoped grind _=_]
theorem saturate_tr_sTr [HasTau Label] {lts : LTS State Label} :
  lts.saturate.Tr = lts.STr := by rfl

/-- Any transition is also a saturated transition. -/
theorem STr.single [HasTau Label] {lts : LTS State Label} :
    lts.Tr s μ s' → lts.STr s μ s' := by
  intro h
  apply STr.tr .refl h .refl

lemma tr_le_tr_saturate [HasTau Label] (lts : LTS State Label) : lts.Tr ≤ lts.saturate.Tr :=
  fun _ _ _ => STr.single

/-- STr transitions labeled by HasTau.τ are exactly the τSTr transitions. -/
theorem sTr_τSTr_iff [HasTau Label] (lts : LTS State Label) :
    lts.STr s HasTau.τ s' ↔ lts.τSTr s s' := by
  apply Iff.intro <;> intro h
  case mp =>
    cases h
    case refl => exact .refl
    case tr _ _ h1 h2 h3 =>
      exact (.trans h1 (.head h2 h3))
  case mpr =>
    cases h
    case refl => exact STr.refl
    case tail _ h1 h2 => exact STr.tr h1 h2 .refl

/-- In a saturated LTS, the transition and saturated transition relations are the same. -/
theorem saturate_τsTr_τSTr_iff [hHasTau : HasTau Label] (lts : LTS State Label) :
    lts.saturate.τSTr = lts.τSTr := by
  ext s s'
  apply Iff.intro <;> intro h
  case mp =>
    induction h
    case refl => constructor
    case tail _ _ _ h2 h3 => exact Relation.ReflTransGen.trans h3 ((sTr_τSTr_iff _).mp h2)
  case mpr =>
    cases h
    case refl => constructor
    case tail s' h2 h3 =>
      have h4 := STr.tr h2 h3 Relation.ReflTransGen.refl
      exact Relation.ReflTransGen.single h4

/-- Saturated transitions labelled by τ can be composed. -/
@[scoped grind .]
theorem STr.trans_τ
    [HasTau Label] {lts : LTS State Label}
    (h1 : lts.STr s1 HasTau.τ s2) (h2 : lts.STr s2 HasTau.τ s3) :
    lts.STr s1 HasTau.τ s3 := by
  rw [sTr_τSTr_iff _] at h1 h2
  rw [sTr_τSTr_iff _]
  apply Relation.ReflTransGen.trans h1 h2

/-- Saturated transitions can be composed. -/
theorem STr.comp
    [HasTau Label] {lts : LTS State Label}
    (h1 : lts.STr s1 HasTau.τ s2)
    (h2 : lts.STr s2 μ s3)
    (h3 : lts.STr s3 HasTau.τ s4) :
  lts.STr s1 μ s4 := by
  rw [sTr_τSTr_iff _] at h1 h3
  cases h2
  case refl =>
    rw [sTr_τSTr_iff _]
    apply Relation.ReflTransGen.trans h1 h3
  case tr _ _ hτ1 htr hτ2 =>
    exact STr.tr (Relation.ReflTransGen.trans h1 hτ1) htr (Relation.ReflTransGen.trans hτ2 h3)

/-- In a saturated LTS, the transition and saturated transition relations are the same. -/
theorem saturate_tr_saturate_sTr [hHasTau : HasTau Label] (lts : LTS State Label)
    (hμ : μ = hHasTau.τ) : lts.saturate.Tr s μ = lts.saturate.STr s μ := by
  ext s'
  apply Iff.intro <;> intro h
  case mp =>
    cases h
    case refl => constructor
    case tr hstr1 htr hstr2 =>
      apply STr.single
      exact STr.tr hstr1 htr hstr2
  case mpr =>
    cases h
    case refl => constructor
    case tr hstr1 htr hstr2 =>
      rw [saturate_τsTr_τSTr_iff lts] at hstr1 hstr2
      rw [←sTr_τSTr_iff lts] at hstr1 hstr2
      exact STr.comp hstr1 htr hstr2

/-- In a saturated LTS, every state is in its τ-image. -/
@[scoped grind .]
lemma mem_saturate_image_τ [HasTau Label] (lts : LTS State Label) :
  s ∈ lts.saturate.image s HasTau.τ := STr.refl

/-- Monotonicity of `setImage` on `HasTau.τ`. -/
@[scoped grind .]
lemma subset_saturate_setImage_τ [HasTau Label] (lts : LTS State Label) :
    S ⊆ lts.saturate.setImage S HasTau.τ := by
  grind [setImage, Set.mem_iUnion]

/-- `setImage` preserves (non-)emptyness. -/
@[scoped grind =]
lemma empty_saturate_setImage_τ [HasTau Label] (lts : LTS State Label) :
    lts.saturate.setImage S HasTau.τ = ∅ ↔ S = ∅:= by grind [Set.mem_of_mem_of_subset]

/-- The `τ`-closure of a set of states `S` is the set of states reachable by any state in `S`
by performing only `τ`-transitions. -/
def τClosure [HasTau Label] (lts : LTS State Label) (S : Set State) : Set State :=
  lts.saturate.setImage S HasTau.τ

/-- Monotonicity of `setImage` on `HasTau.τ`. -/
@[scoped grind .]
lemma τClosure_subset [HasTau Label] (lts : LTS State Label) :
    S ⊆ lts.τClosure S := by grind [Set.mem_of_mem_of_subset, = τClosure]

/-- Saturated multistep transition relation. -/
inductive SMTr [HasTau Label] (lts : LTS State Label) : State → List Label → State → Prop where
  | τ : lts.STr s HasTau.τ s' → lts.SMTr s [] s'
  | stepL : lts.STr s1 μ s2 → lts.SMTr s2 μs s3 → lts.SMTr s1 (μ :: μs) s3

/-- The saturated multistep transition relation is reflexive. -/
@[scoped grind .]
theorem SMTr.refl [HasTau Label] (lts : LTS State Label) (s : State) :
    lts.SMTr s [] s := by grind [LTS.STr, LTS.SMTr]

open scoped LTS.STr

/-- The saturated multistep transition relation is transitive. -/
@[scoped grind .]
theorem SMTr.comp [HasTau Label] {lts : LTS State Label}
    (h₁ : lts.SMTr s₁ μs₁ s₂) (h₂ : lts.SMTr s₂ μs₂ s₃) : lts.SMTr s₁ (μs₁ ++ μs₂) s₃ := by
  induction h₁
  case τ s₁ s₂ htr =>
    cases h₂
    case τ htr' => grind [SMTr]
    case stepL _ _ _ μ s₂' μs hstr hmstr =>
      have hstr' : lts.STr s₁ μ s₂' := by
        apply STr.comp htr hstr STr.refl
      simp only [List.nil_append]
      apply stepL hstr' hmstr
  case stepL s₁ μ s₁' μs s₂ hstr hmstr ih =>
    apply stepL hstr (ih h₂)

/-- A multistep transition implies a saturated multistep transition. -/
@[scoped grind .]
theorem SMTr.fromMTr [HasTau Label] {lts : LTS State Label}
    (h : lts.MTr s μs s') : lts.SMTr s μs s' := by
  induction μs generalizing s s'
  case nil => grind [LTS.STr, LTS.SMTr]
  case cons x xs ih =>
    cases h
    case stepL sb htr hmtr => exact SMTr.stepL (STr.single htr) (ih hmtr)

@[scoped grind =]
theorem sMTr_τSTr_iff [HasTau Label] {lts : LTS State Label} :
    lts.τSTr s s' ↔ lts.SMTr s [] s' := by grind only [=_ sTr_τSTr_iff, SMTr]

/-- A saturated multistep transition with a nonempty label list implies a multistep transition. -/
@[scoped grind =]
theorem saturate_mTr_sMTr_not_nil_iff [HasTau Label] {lts : LTS State Label}
    (hμs : μs ≠ []) : lts.saturate.MTr s μs s' ↔ lts.SMTr s μs s' := by
  induction μs generalizing s
  case nil => contradiction
  case cons x xs ih =>
    apply Iff.intro <;> intro h
    case mp =>
      cases h
      case stepL sb htr hmtr =>
        cases xs with
        | nil =>
          cases hmtr
          apply LTS.SMTr.stepL htr (by grind only [SMTr.fromMTr, MTr.refl])
        | cons x' xs' =>
          exact LTS.SMTr.stepL htr ((ih (by simp)).mp hmtr)
    case mpr =>
      cases h
      case stepL sb htr hmtr =>
        cases xs with
        | nil =>
          cases hmtr
          case τ h_τ =>
            exact LTS.MTr.stepL
              (LTS.STr.comp LTS.STr.refl htr h_τ)
              LTS.MTr.refl
        | cons x' xs' =>
          exact LTS.MTr.stepL htr ((ih (by simp)).mpr hmtr)

end LTS

end Cslib
