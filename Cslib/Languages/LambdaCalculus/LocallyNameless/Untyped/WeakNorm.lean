/-
Copyright (c) 2025 David Wegmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Leng
-/

module

public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.EtaPostpone

/-! Weak normalization for full beta-reduction of untyped lambda calculus. -/

@[expose] public section

set_option linter.unusedDecidableInType false

namespace Cslib

universe u

namespace LambdaCalculus.LocallyNameless.Untyped.Term

variable {Var : Type u} [DecidableEq Var] [HasFresh Var] {t t' : Term Var}

open FullBeta Relation

/-- [Takahashi1995] 3.7: If `P ↠ηᶠ Q` and `P` is a β-normal form,
  then `Q` is a β-normal form. -/
theorem etastar_preserves_normal_beta :
  Preserves ((· ↠ηᶠ ·) : Term Var → Term Var → Prop) (Normal FullBeta) := by
  rintro _ _ steps hP ⟨_, hR⟩
  rw [reflTransGen_swap] at steps
  obtain ⟨y, hy, _⟩ := diamondcommute_etaplus_betastar steps (.single hR)
  rw [TransGen.head'_iff] at hy
  exact hP (by grind)

theorem etastar_hasBetaNF (steps : t ↠ηᶠ t') (hQ : Normalizable FullBeta t') :
  Normalizable FullBeta t := by
  induction steps with
  | refl => grind
  | tail _ step ih => exact ih (parEta_hasBetaNF (FullEta.le_parallel _ _ step) hQ)

/-- A term has a βη-normal form ⇔ it has a β-normal form. -/
theorem hasBetaNF_iff_hasBetaEtaNF : Normalizable FullBeta t ↔ Normalizable FullBetaEta t := by
  refine ⟨fun ⟨y, hy, hβ⟩ => ?_, fun ⟨y, hy, hβηnormal⟩ => ?_⟩
  · obtain ⟨z, hz, hnormal⟩ := SN.normalizable (FullEta.terminating.apply y)
    refine ⟨z, .trans (.mono le_sup_left _ _ hy) (.mono le_sup_right _ _ hz), fun ⟨_, h⟩ => ?_⟩
    have := etastar_preserves_normal_beta hz hβ
    cases h <;> grind
  · obtain ⟨L, hβ, hη⟩ := eta_postpone hy
    rw [Normal.sup_iff] at hβηnormal
    obtain ⟨_, _⟩ := hβηnormal
    have h : Normalizable FullBeta y := by exists y
    obtain ⟨W, hw, hnormal⟩ := etastar_hasBetaNF hη h
    exact ⟨W, .trans hβ hw, hnormal⟩

theorem etastar_iff_hasBetaNF (steps : t ↠ηᶠ t') :
  Normalizable FullBeta t ↔ Normalizable FullBeta t' := by
  refine ⟨fun hP => ?_, fun hQ => etastar_hasBetaNF steps hQ⟩
  rw [hasBetaNF_iff_hasBetaEtaNF] at *
  obtain ⟨Z, βηsteps, hZ⟩ := hP
  obtain ⟨_, refl_steps, _⟩ := confluent_beta_eta βηsteps (.mono le_sup_right _ _ steps)
  grind [Normal.reflTransGen_eq hZ refl_steps]

theorem etastar_iff_hasBetaEtaNF (steps : t ↠ηᶠ t') :
  Normalizable FullBetaEta t ↔ Normalizable FullBetaEta t' := by
  repeat rw [← hasBetaNF_iff_hasBetaEtaNF]
  exact etastar_iff_hasBetaNF steps

end LambdaCalculus.LocallyNameless.Untyped.Term

end Cslib
