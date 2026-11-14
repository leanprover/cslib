/-
Copyright (c) 2026 Malvin Gattinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Malvin Gattinger
-/

module

public import Cslib.Logics.PDL.Semantics

/-! # Axioms for Propositional Dynamic Logic (PDL)

From BRV Def 4.78.

NOTES:

- TODO: should we separate the statement of the axioms from their soundness theorem?
-/

@[expose] public section

namespace Cslib.Logic.Modal.PDL

variable {State Label Atom : Type*}

namespace Axioms

open scoped PDL.Model Modal.Proposition InferenceSystem

variable {State : Type*} (m : Model State Label Atom) (s : State)
  (a b : Program Label Atom) (p q ψ : Formula Label Atom)

/-- (i) K: valid on all frames. -/
theorem K : ⇓PDL[m, s ⊨ d[a](p → q) → (d[a]p → d[a]q)] := by grind [modal]

/-- (ii) Duality: valid on all frames. -/
theorem dual : ⇓PDL[m, s ⊨ d⟨a⟩p ↔ ¬d[a](¬p)] := by grind [modal]

/-- (iii) Composition: valid on frames regular for `;'`. -/
theorem seq (isReg : m.lts.IsRegularPDL) :
    ⇓PDL[m, s ⊨ d⟨a ;' b⟩p ↔ d⟨a⟩(d⟨b⟩p)] := by
  simp only [judgement, Formula.toUnary_iff, Formula.toUnary_dynDiamond]
  rw [@Satisfies.iff_iff_iff]
  grind [modal, isReg.seq]

/-- (iv) Choice: valid on frames regular for `∪`. -/
theorem union (isReg : m.lts.IsRegularPDL) :
    ⇓PDL[m, s ⊨ d⟨a ∪ b⟩p ↔ (d⟨a⟩p ∨ d⟨b⟩p)] := by
  simp only [judgement, Formula.toUnary_iff, Formula.toUnary_dynDiamond]
  rw [@Satisfies.iff_iff_iff]
  grind [modal, isReg.union]

/-- (v) Mix: valid on frames regular for `*`. -/
theorem mix (isReg : m.lts.IsRegularPDL) :
    ⇓PDL[m, s ⊨ d⟨a*⟩p ↔ (p ∨ d⟨a⟩(d⟨a*⟩p))] := by
  simp only [judgement, Formula.toUnary_iff, Formula.toUnary_dynDiamond]
  rw [@Satisfies.iff_iff_iff]
  have := @Satisfies.pdl_dynDiamond_iff_exists State Label Atom m s (a*) p
  simp only [judgement, Formula.toUnary_dynDiamond] at this -- having to do this seems sub-optimal
  rw [this]
  clear this
  simp_rw [isReg.star a] -- using regularity here
  refine ⟨fun lhs => ?_, fun rhs => ?_⟩
  · simp only [Formula.toUnary_or, Formula.toUnary_dynDiamond]
    rw [@Satisfies.or_iff_or]
    rcases lhs with ⟨s', s_to_s', s'_p⟩
    rw [Relation.ReflTransGen.cases_head_iff] at s_to_s'
    rcases s_to_s' with _ | ⟨u, s_to_u, u_to_s'⟩
    · grind
    · right
      have := @Satisfies.pdl_dynDiamond_iff_exists State Label Atom m s a (d⟨a*⟩p)
      simp only [judgement, Formula.toUnary_dynDiamond] at this -- again, this seems annoying
      rw [this]
      clear this
      refine ⟨u, s_to_u, ?_⟩
      have := @Satisfies.pdl_dynDiamond_iff_exists State Label Atom m u (a*) p
      simp only [judgement, Formula.toUnary_dynDiamond] at this -- once more
      rw [this]
      refine ⟨s', ?_, s'_p⟩
      · convert u_to_s'
        simp_rw [isReg.star a] -- using regularity again
  · rw [Formula.toUnary_or, Satisfies.or_iff_or] at rhs
    rcases rhs with h|h
    · use s
    · rw [Satisfies.pdl_dynDiamond_iff_exists] at h
      -- rw [Satisfies.pdl_dynDiamond_iff_exists] at h -- cannot rewrtie under binder??
      simp_rw [Satisfies.pdl_dynDiamond_iff_exists] at h
      rcases h with ⟨t, s_a_t, s', t_aS_s', s'_sat⟩
      refine ⟨s', ?_, ?_⟩
      · -- grind [modal]
        rw [isReg.star a] at t_aS_s' -- using regularity
        exact Relation.ReflTransGen.head s_a_t t_aS_s'
      · grind

/-- (vi) Induction: valid on frames regular for `*`. -/
theorem ind (isReg : m.lts.IsRegularPDL) :
    ⇓PDL[m, s ⊨ d[a*](p → d[a]p) → (p → d[a*]p)] := by
  sorry

/-- Test axiom (not in BRV's test-free list): needs a standard model. -/
theorem test (h : m.IsStandard) :
    ⇓PDL[m, s ⊨ d⟨?' ψ⟩p ↔ (ψ ∧ p)] := by
  have := h.test
  grind [modal]

end Axioms

end Cslib.Logic.Modal.PDL
