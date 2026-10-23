/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Foundations.Semantics.LTS.Relation
public import Cslib.Foundations.Semantics.LTS.SetImage

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

/-- Checking whether an element is `τ` is decidable. -/
abbrev DecidableEqTau (α : Type*) [HasTau α] := ∀ a : α, Decidable (a = HasTau.τ)

namespace LTS

/-- Saturated τ-transition relation. -/
def τSTr [HasTau Label] (lts : LTS State Label) : State → State → Prop :=
  Relation.ReflTransGen (Tr.toRelation lts HasTau.τ)

@[scoped grind .]
theorem τSTr.refl [HasTau Label] {lts : LTS State Label} : lts.τSTr s s :=
  Relation.ReflTransGen.refl

/-- Saturated transition relation. -/
@[mk_iff]
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

/-- Saturating an LTS does not change its saturated τ-transition relation. -/
theorem saturate_τsTr_τSTr_iff [hHasTau : HasTau Label] (lts : LTS State Label) :
    lts.saturate.τSTr = lts.τSTr := by
  change Relation.ReflTransGen (fun s s' => lts.STr s HasTau.τ s') = _
  simp only [sTr_τSTr_iff]
  exact Relation.reflTransGen_eq_self (r := Relation.ReflTransGen _)

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

/-- In a saturated LTS, transitions and saturated transitions agree for every label. -/
theorem saturate_tr_saturate_sTr [hHasTau : HasTau Label] (lts : LTS State Label) :
    lts.saturate.Tr s μ = lts.saturate.STr s μ := by
  ext s'
  constructor
  · exact STr.single
  · intro h
    cases h with
    | refl => exact STr.refl
    | tr h₁ h₂ h₃ =>
      rw [saturate_τsTr_τSTr_iff] at h₁ h₃
      exact STr.comp ((sTr_τSTr_iff _).mpr h₁) h₂ ((sTr_τSTr_iff _).mpr h₃)

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

/-- The `τ`-closure of `S` consists of the states reachable from `S` by `τ`-transitions. -/
@[scoped grind =]
theorem mem_τClosure_iff [HasTau Label] {lts : LTS State Label} {S : Set State} {s' : State} :
    s' ∈ lts.τClosure S ↔ ∃ s ∈ S, lts.τSTr s s' := by
  simp_rw [τClosure, mem_setImage, ← sTr_τSTr_iff, saturate_tr_sTr]

/-- The `τ`-closure of the empty set is empty. -/
@[simp, scoped grind =]
theorem τClosure_empty [HasTau Label] (lts : LTS State Label) : lts.τClosure ∅ = ∅ :=
  lts.saturate.setImage_empty

/-- The `τ`-closure distributes over binary unions. -/
@[simp, scoped grind =]
theorem τClosure_union [HasTau Label] (lts : LTS State Label) (S T : Set State) :
    lts.τClosure (S ∪ T) = lts.τClosure S ∪ lts.τClosure T :=
  lts.saturate.setImage_union S T HasTau.τ

/-- Taking the `τ`-closure is monotone. -/
@[gcongr]
theorem τClosure_mono [HasTau Label] (lts : LTS State Label) {S T : Set State} (h : S ⊆ T) :
    lts.τClosure S ⊆ lts.τClosure T :=
  lts.saturate.setImage_mono h HasTau.τ

/-- The `τ`-closure is idempotent. -/
@[simp]
theorem τClosure_τClosure [HasTau Label] (lts : LTS State Label) (S : Set State) :
    lts.τClosure (lts.τClosure S) = lts.τClosure S := by
  refine Set.Subset.antisymm (fun s'' h => ?_) (τClosure_subset lts)
  obtain ⟨s', hs', h₂⟩ := mem_τClosure_iff.mp h
  obtain ⟨s, hs, h₁⟩ := mem_τClosure_iff.mp hs'
  exact mem_τClosure_iff.mpr ⟨s, hs, Relation.ReflTransGen.trans h₁ h₂⟩

/-- For a label other than `τ`, the saturated image of `S` is the `τ`-closure of the image of the
`τ`-closure of `S`. -/
theorem saturate_setImage_of_ne_τ [HasTau Label] (lts : LTS State Label) {S : Set State}
    {μ : Label} (hμ : μ ≠ HasTau.τ) :
    lts.saturate.setImage S μ = lts.τClosure (lts.setImage (lts.τClosure S) μ) := by
  ext s'
  simp [mem_setImage, saturate_tr_sTr, sTr_iff, hμ, mem_τClosure_iff]
  grind

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
    case stepL _ _ _ μ s₂' μs hstr hmstr => exact stepL (htr.comp hstr STr.refl) hmstr
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

/-- A saturated `τ`-transition is a run along a list of `τ`s. -/
theorem τSTr_iff_exists_mTr_replicate [HasTau Label] {lts : LTS State Label} {s t : State} :
    lts.τSTr s t ↔ ∃ n, lts.MTr s (List.replicate n HasTau.τ) t := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨0, .refl⟩
    | tail _ htr ih =>
      obtain ⟨n, hmtr⟩ := ih
      refine ⟨n + 1, ?_⟩
      rw [List.replicate_succ']
      exact hmtr.stepR _ htr
  · rintro ⟨n, hmtr⟩
    induction n generalizing s with
    | zero =>
      obtain rfl := hmtr.nil_eq _
      exact .refl
    | succ n ih =>
      obtain ⟨s', htr, hmtr'⟩ := MTr.cons_iff.mp hmtr
      exact .head htr (ih hmtr')

/-- A saturated run along a list of visible labels is a run whose labels, once the `τ`s are
dropped, are that list. -/
theorem sMTr_iff_exists_mTr_filter [HasTau Label] [DecidableEqTau Label]
    {lts : LTS State Label} {s t : State} {μs : List Label} (hμs : ∀ μ ∈ μs, μ ≠ HasTau.τ) :
    lts.SMTr s μs t ↔ ∃ νs : List Label, νs.filter (· ≠ HasTau.τ) = μs ∧ lts.MTr s νs t := by
  constructor
  · intro h
    induction h with
    | τ hstr =>
      obtain ⟨n, hmtr⟩ := τSTr_iff_exists_mTr_replicate.mp ((sTr_τSTr_iff lts).mp hstr)
      exact ⟨_, by simp, hmtr⟩
    | @stepL s₁ μ s₂ μs s₃ hstr _ ih =>
      have hμ : μ ≠ HasTau.τ := hμs μ (by simp)
      obtain ⟨νs, hνs, hmtr⟩ := ih fun ν hν => hμs ν (by simp [hν])
      cases hstr with
      | refl => exact absurd rfl hμ
      | tr h₁ htr h₂ =>
        obtain ⟨n₁, hmtr₁⟩ := τSTr_iff_exists_mTr_replicate.mp h₁
        obtain ⟨n₂, hmtr₂⟩ := τSTr_iff_exists_mTr_replicate.mp h₂
        refine ⟨List.replicate n₁ HasTau.τ ++ μ :: (List.replicate n₂ HasTau.τ ++ νs), ?_,
          hmtr₁.comp _ (.stepL htr (hmtr₂.comp _ hmtr))⟩
        simpa [List.filter_append, hμ] using hνs
  · rintro ⟨νs, rfl, hmtr⟩
    clear hμs
    induction hmtr with
    | refl => exact SMTr.refl lts _
    | @stepL s₁ ν s₂ νs s₃ htr _ ih =>
      by_cases hν : ν = HasTau.τ
      · subst hν
        have hfilter : (HasTau.τ :: νs).filter (· ≠ HasTau.τ) = νs.filter (· ≠ HasTau.τ) := by
          simp
        rw [hfilter]
        exact SMTr.comp (.τ (.single htr)) ih
      · have hfilter : (ν :: νs).filter (· ≠ HasTau.τ) = ν :: νs.filter (· ≠ HasTau.τ) := by
          simp [hν]
        rw [hfilter]
        exact .stepL (.single htr) ih

end LTS

end Cslib
