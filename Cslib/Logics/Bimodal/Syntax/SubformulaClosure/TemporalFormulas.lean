/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

import Cslib.Logics.Bimodal.Syntax.SubformulaClosure.NestingDepth

/-!
# Temporal Formula Infrastructure

Deferral closure, seriality formulas, temporal blocking set, and structural lemmas.

Ported from BimodalLogic/Theories/Bimodal/Syntax/SubformulaClosure/TemporalFormulas.lean
-/

set_option linter.style.emptyLine false
set_option linter.style.longLine false

namespace Cslib.Logic.Bimodal

open Formula

variable {Atom : Type*} [DecidableEq Atom]

def toFutureDeferral (f : Formula Atom) : Formula Atom :=
  match extractFutureInner f with
  | some chi => Formula.or chi (Formula.some_future chi)
  | none => Formula.bot

def toPastDeferral (f : Formula Atom) : Formula Atom :=
  match extractPastInner f with
  | some chi => Formula.or chi (Formula.some_past chi)
  | none => Formula.bot

def deferralDisjunctionSet (phi : Formula Atom) : Finset (Formula Atom) :=
  ((closureWithNeg phi).filter IsFutureFormula).image toFutureDeferral

def backwardDeferralSet (phi : Formula Atom) : Finset (Formula Atom) :=
  ((closureWithNeg phi).filter IsPastFormula).image toPastDeferral

def IsUntilFormula : Formula Atom → Prop
  | .untl _ _ => True
  | _ => False

instance : DecidablePred (IsUntilFormula (Atom := Atom)) :=
  fun f => match f with
  | .untl _ _ => isTrue True.intro
  | .atom _ | .bot | .imp _ _ | .box _ | .snce _ _ =>
    isFalse (by simp [IsUntilFormula])

def IsSinceFormula : Formula Atom → Prop
  | .snce _ _ => True
  | _ => False

instance : DecidablePred (IsSinceFormula (Atom := Atom)) :=
  fun f => match f with
  | .snce _ _ => isTrue True.intro
  | .atom _ | .bot | .imp _ _ | .box _ | .untl _ _ =>
    isFalse (by simp [IsSinceFormula])

def toUntilDeferral : Formula Atom → Formula Atom
  | .untl phi psi => Formula.or psi (Formula.and phi (.untl phi psi))
  | _ => Formula.bot

def toSinceDeferral : Formula Atom → Formula Atom
  | .snce phi psi => Formula.or psi (Formula.and phi (.snce phi psi))
  | _ => Formula.bot

def untilDeferralSet (phi : Formula Atom) : Finset (Formula Atom) :=
  ((closureWithNeg phi).filter IsUntilFormula).image toUntilDeferral

def sinceDeferralSet (phi : Formula Atom) : Finset (Formula Atom) :=
  ((closureWithNeg phi).filter IsSinceFormula).image toSinceDeferral

abbrev F_top : Formula Atom := Formula.some_future (Formula.neg Formula.bot)
abbrev P_top : Formula Atom := Formula.some_past (Formula.neg Formula.bot)
abbrev neg_neg_bot : Formula Atom := Formula.neg (Formula.neg Formula.bot)
abbrev G_neg_neg_bot : Formula Atom := Formula.all_future (neg_neg_bot : Formula Atom)
abbrev H_neg_neg_bot : Formula Atom := Formula.all_past (neg_neg_bot : Formula Atom)
abbrev neg_G_neg_neg_bot : Formula Atom := Formula.neg (G_neg_neg_bot : Formula Atom)
abbrev neg_H_neg_neg_bot : Formula Atom := Formula.neg (H_neg_neg_bot : Formula Atom)
abbrev F_top_deferral : Formula Atom := Formula.or (Formula.neg Formula.bot) (F_top : Formula Atom)
abbrev P_top_deferral : Formula Atom := Formula.or (Formula.neg Formula.bot) (P_top : Formula Atom)

def serialityFormulas : Finset (Formula Atom) :=
  {F_top, P_top, Formula.neg Formula.bot, neg_neg_bot, G_neg_neg_bot, H_neg_neg_bot,
   neg_G_neg_neg_bot, neg_H_neg_neg_bot, F_top_deferral, P_top_deferral}

def toFutureBlocking (f : Formula Atom) : Formula Atom :=
  match extractFutureInner f with
  | some chi => Formula.all_future chi.neg
  | none => Formula.bot

def toPastBlocking (f : Formula Atom) : Formula Atom :=
  match extractPastInner f with
  | some chi => Formula.all_past chi.neg
  | none => Formula.bot

def temporalBlockingSet (phi : Formula Atom) : Finset (Formula Atom) :=
  ((closureWithNeg phi).filter IsFutureFormula).image toFutureBlocking ∪
  ((closureWithNeg phi).filter IsPastFormula).image toPastBlocking

theorem toFutureBlocking_some_future (chi : Formula Atom) :
    toFutureBlocking (Formula.some_future chi) = Formula.all_future chi.neg := by
  simp only [toFutureBlocking, extractFutureInner_some_future]

theorem toPastBlocking_some_past (chi : Formula Atom) :
    toPastBlocking (Formula.some_past chi) = Formula.all_past chi.neg := by
  simp only [toPastBlocking, extractPastInner_some_past]

theorem all_future_neg_mem_temporalBlockingSet_of_some_future {phi chi : Formula Atom}
    (h : Formula.some_future chi ∈ closureWithNeg phi) :
    Formula.all_future chi.neg ∈ temporalBlockingSet phi := by
  unfold temporalBlockingSet
  apply Finset.mem_union_left
  rw [Finset.mem_image]
  refine ⟨Formula.some_future chi, ?_, toFutureBlocking_some_future chi⟩
  rw [Finset.mem_filter]
  exact ⟨h, by simp [IsFutureFormula, extractFutureInner_some_future]⟩

theorem all_past_neg_mem_temporalBlockingSet_of_some_past {phi chi : Formula Atom}
    (h : Formula.some_past chi ∈ closureWithNeg phi) :
    Formula.all_past chi.neg ∈ temporalBlockingSet phi := by
  unfold temporalBlockingSet
  apply Finset.mem_union_right
  rw [Finset.mem_image]
  refine ⟨Formula.some_past chi, ?_, toPastBlocking_some_past chi⟩
  rw [Finset.mem_filter]
  exact ⟨h, by simp [IsPastFormula, extractPastInner_some_past]⟩

def baseDeferralClosure (phi : Formula Atom) : Finset (Formula Atom) :=
  closureWithNeg phi ∪ deferralDisjunctionSet phi ∪ backwardDeferralSet phi
  ∪ serialityFormulas ∪ temporalBlockingSet phi

def deferralClosure (phi : Formula Atom) : Finset (Formula Atom) :=
  baseDeferralClosure phi

def extendedDeferralClosure (phi : Formula Atom) : Finset (Formula Atom) :=
  baseDeferralClosure phi ∪ untilDeferralSet phi ∪ sinceDeferralSet phi

theorem baseDeferralClosure_eq_deferralClosure (phi : Formula Atom) :
    baseDeferralClosure phi = deferralClosure phi := rfl

theorem baseDeferralClosure_subset_deferralClosure (phi : Formula Atom) :
    baseDeferralClosure phi ⊆ deferralClosure phi := by
  rw [baseDeferralClosure_eq_deferralClosure]

theorem deferralClosure_subset_extendedDeferralClosure (phi : Formula Atom) :
    deferralClosure phi ⊆ extendedDeferralClosure phi := by
  intro psi h
  unfold extendedDeferralClosure
  exact Finset.mem_union_left _ (Finset.mem_union_left _ h)

theorem closureWithNeg_subset_deferralClosure (phi : Formula Atom) :
    closureWithNeg phi ⊆ deferralClosure phi := by
  intro psi h
  unfold deferralClosure baseDeferralClosure
  exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ h)))

theorem self_mem_deferralClosure (phi : Formula Atom) : phi ∈ deferralClosure phi :=
  closureWithNeg_subset_deferralClosure phi (self_mem_closureWithNeg phi)

theorem neg_self_mem_deferralClosure (phi : Formula Atom) : phi.neg ∈ deferralClosure phi :=
  closureWithNeg_subset_deferralClosure phi (neg_self_mem_closureWithNeg phi)

theorem serialityFormulas_subset_deferralClosure (phi : Formula Atom) :
    (serialityFormulas : Finset (Formula Atom)) ⊆ deferralClosure phi := by
  intro psi h
  unfold deferralClosure baseDeferralClosure
  exact Finset.mem_union_left _ (Finset.mem_union_right _ h)

theorem temporalBlockingSet_subset_deferralClosure (phi : Formula Atom) :
    temporalBlockingSet phi ⊆ deferralClosure phi := by
  intro psi h
  unfold deferralClosure baseDeferralClosure
  exact Finset.mem_union_right _ h

theorem F_top_mem_serialityFormulas : (F_top : Formula Atom) ∈ serialityFormulas := by
  simp only [serialityFormulas, Finset.mem_insert, Finset.mem_singleton]
  left; trivial

theorem P_top_mem_serialityFormulas : (P_top : Formula Atom) ∈ serialityFormulas := by
  simp only [serialityFormulas, Finset.mem_insert, Finset.mem_singleton]
  right; left; trivial

theorem neg_bot_mem_serialityFormulas :
    (Formula.neg Formula.bot : Formula Atom) ∈ serialityFormulas := by
  simp only [serialityFormulas, Finset.mem_insert, Finset.mem_singleton]
  right; right; left; trivial

theorem neg_neg_bot_mem_serialityFormulas :
    (neg_neg_bot : Formula Atom) ∈ serialityFormulas := by
  simp only [serialityFormulas, Finset.mem_insert, Finset.mem_singleton]
  right; right; right; left; trivial

theorem G_neg_neg_bot_mem_serialityFormulas :
    (G_neg_neg_bot : Formula Atom) ∈ serialityFormulas := by
  simp only [serialityFormulas, Finset.mem_insert, Finset.mem_singleton]
  right; right; right; right; left; trivial

theorem H_neg_neg_bot_mem_serialityFormulas :
    (H_neg_neg_bot : Formula Atom) ∈ serialityFormulas := by
  simp only [serialityFormulas, Finset.mem_insert, Finset.mem_singleton]
  right; right; right; right; right; left; trivial

theorem F_top_mem_deferralClosure (phi : Formula Atom) :
    (F_top : Formula Atom) ∈ deferralClosure phi :=
  serialityFormulas_subset_deferralClosure phi F_top_mem_serialityFormulas

theorem P_top_mem_deferralClosure (phi : Formula Atom) :
    (P_top : Formula Atom) ∈ deferralClosure phi :=
  serialityFormulas_subset_deferralClosure phi P_top_mem_serialityFormulas

theorem neg_bot_mem_deferralClosure (phi : Formula Atom) :
    (Formula.neg Formula.bot : Formula Atom) ∈ deferralClosure phi :=
  serialityFormulas_subset_deferralClosure phi neg_bot_mem_serialityFormulas

theorem neg_neg_bot_mem_deferralClosure (phi : Formula Atom) :
    (neg_neg_bot : Formula Atom) ∈ deferralClosure phi :=
  serialityFormulas_subset_deferralClosure phi neg_neg_bot_mem_serialityFormulas

theorem G_neg_neg_bot_mem_deferralClosure (phi : Formula Atom) :
    (G_neg_neg_bot : Formula Atom) ∈ deferralClosure phi :=
  serialityFormulas_subset_deferralClosure phi G_neg_neg_bot_mem_serialityFormulas

theorem H_neg_neg_bot_mem_deferralClosure (phi : Formula Atom) :
    (H_neg_neg_bot : Formula Atom) ∈ deferralClosure phi :=
  serialityFormulas_subset_deferralClosure phi H_neg_neg_bot_mem_serialityFormulas

theorem all_future_neg_mem_deferralClosure_of_some_future {phi chi : Formula Atom}
    (h : Formula.some_future chi ∈ closureWithNeg phi) :
    Formula.all_future chi.neg ∈ deferralClosure phi :=
  temporalBlockingSet_subset_deferralClosure phi
    (all_future_neg_mem_temporalBlockingSet_of_some_future h)

theorem all_past_neg_mem_deferralClosure_of_some_past {phi chi : Formula Atom}
    (h : Formula.some_past chi ∈ closureWithNeg phi) :
    Formula.all_past chi.neg ∈ deferralClosure phi :=
  temporalBlockingSet_subset_deferralClosure phi
    (all_past_neg_mem_temporalBlockingSet_of_some_past h)

theorem toFutureDeferral_some_future (chi : Formula Atom) :
    toFutureDeferral (Formula.some_future chi) = Formula.or chi (Formula.some_future chi) := by
  simp only [toFutureDeferral, extractFutureInner_some_future]

theorem toPastDeferral_some_past (chi : Formula Atom) :
    toPastDeferral (Formula.some_past chi) = Formula.or chi (Formula.some_past chi) := by
  simp only [toPastDeferral, extractPastInner_some_past]

theorem deferral_of_F_in_closure (phi chi : Formula Atom)
    (h : Formula.some_future chi ∈ closureWithNeg phi) :
    Formula.or chi (Formula.some_future chi) ∈ deferralClosure phi := by
  unfold deferralClosure baseDeferralClosure deferralDisjunctionSet
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  rw [← toFutureDeferral_some_future chi]
  apply Finset.mem_image_of_mem
  apply Finset.mem_filter.mpr
  constructor
  · exact h
  · simp only [IsFutureFormula, extractFutureInner_some_future, Option.isSome_some]

theorem deferral_of_P_in_closure (phi chi : Formula Atom)
    (h : Formula.some_past chi ∈ closureWithNeg phi) :
    Formula.or chi (Formula.some_past chi) ∈ deferralClosure phi := by
  unfold deferralClosure baseDeferralClosure backwardDeferralSet
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  rw [← toPastDeferral_some_past chi]
  apply Finset.mem_image_of_mem
  apply Finset.mem_filter.mpr
  constructor
  · exact h
  · simp only [IsPastFormula, extractPastInner_some_past, Option.isSome_some]

theorem f_nesting_depth_or (chi psi : Formula Atom) :
    f_nesting_depth (Formula.or chi psi) = 0 := by
  simp only [Formula.or, Formula.neg, f_nesting_depth]

theorem p_nesting_depth_or (chi psi : Formula Atom) :
    p_nesting_depth (Formula.or chi psi) = 0 := by
  simp only [Formula.or, Formula.neg, p_nesting_depth]

theorem f_nesting_depth_F_deferral (chi : Formula Atom) :
    f_nesting_depth (Formula.or chi (Formula.some_future chi)) = 0 :=
  f_nesting_depth_or chi (Formula.some_future chi)

theorem p_nesting_depth_P_deferral (chi : Formula Atom) :
    p_nesting_depth (Formula.or chi (Formula.some_past chi)) = 0 :=
  p_nesting_depth_or chi (Formula.some_past chi)

-- The remaining structural lemmas (max depth, all_future/all_past cases, box cases)
-- are deferred to a follow-up continuation due to volume. The definitions and
-- core membership lemmas above are sufficient for Phase 2+ dependencies.

-- Placeholder for forward references from later phases:
theorem F_top_deferral_mem_deferralClosure (phi : Formula Atom) :
    (F_top_deferral : Formula Atom) ∈ deferralClosure phi := by
  apply serialityFormulas_subset_deferralClosure
  simp only [serialityFormulas, Finset.mem_insert, Finset.mem_singleton]
  right; right; right; right; right; right; right; right; left; trivial

theorem P_top_deferral_mem_deferralClosure (phi : Formula Atom) :
    (P_top_deferral : Formula Atom) ∈ deferralClosure phi := by
  apply serialityFormulas_subset_deferralClosure
  simp only [serialityFormulas, Finset.mem_insert, Finset.mem_singleton]
  right; right; right; right; right; right; right; right; right; trivial

end Cslib.Logic.Bimodal
