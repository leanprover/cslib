/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Temporal.Metalogic.Chronicle.ChronicleToCountermodel

/-!
# Chronicle Truth Lemma

The truth lemma for the chronicle countermodel: satisfaction in the chronicle
model corresponds to membership in the limit point function.

## Main Results

- `chronicle_truth_lemma`: For all formulas `φ` and points `t` in the chronicle
  subtype, `Satisfies (chronicleModel A h_mcs) t φ ↔ φ ∈ limitF A h_mcs t.val`.

The proof proceeds by structural induction on `φ` with five cases:
- `atom`: By definition of `chronicleModel.valuation`
- `bot`: `False ↔ bot ∉ MCS` by `mcs_bot_not_mem`
- `imp`: By MCS implication property and negation completeness
- `untl`: Forward by `limit_satisfies_c5_strong`, backward by contradiction
  using `limit_satisfies_c4`
- `snce`: Mirror of `untl` using `limit_satisfies_c5'_strong` and
  `limit_satisfies_c4'`

## References

- Burgess 1982: Section 2, Claim 2.11
-/

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.flexible false
set_option maxHeartbeats 3200000

@[expose] public section

namespace Cslib.Logic.Temporal.Metalogic.Chronicle

open Cslib.Logic.Temporal
open Cslib.Logic.Temporal.Metalogic

attribute [local instance] Classical.propDecidable

variable {Atom : Type*}
variable [Denumerable (Formula Atom)]

/-! ## Helper: MCS membership implies limitF membership -/

/-! ## Truth Lemma: Individual Cases -/

/-- Atom case: by definition of chronicleModel valuation. -/
theorem truth_lemma_atom (A : Set (Formula Atom)) (h_mcs : Temporal.SetMaximalConsistent A)
    (t : ChronicleSubtype A h_mcs) (p : Atom) :
    Satisfies (chronicleModel A h_mcs) t (Formula.atom p) ↔
      Formula.atom p ∈ limitF A h_mcs t.val := by
  simp only [Satisfies, chronicleModel]

/-- Bot case: bot is never satisfied and never in an MCS. -/
theorem truth_lemma_bot (A : Set (Formula Atom)) (h_mcs : Temporal.SetMaximalConsistent A)
    (t : ChronicleSubtype A h_mcs) :
    Satisfies (chronicleModel A h_mcs) t ⊥ ↔
      (⊥ : Formula Atom) ∈ limitF A h_mcs t.val := by
  constructor
  · intro h; exact absurd h id
  · intro h; exact absurd h (mcs_bot_not_mem (limit_c0 A h_mcs t.val t.property))

/-- Imp case: by MCS implication property and induction hypotheses. -/
theorem truth_lemma_imp (A : Set (Formula Atom)) (h_mcs : Temporal.SetMaximalConsistent A)
    (t : ChronicleSubtype A h_mcs) (φ ψ : Formula Atom)
    (ih_φ : Satisfies (chronicleModel A h_mcs) t φ ↔ φ ∈ limitF A h_mcs t.val)
    (ih_ψ : Satisfies (chronicleModel A h_mcs) t ψ ↔ ψ ∈ limitF A h_mcs t.val) :
    Satisfies (chronicleModel A h_mcs) t (φ → ψ) ↔
      (φ → ψ) ∈ limitF A h_mcs t.val := by
  have h_mcs_t := limit_c0 A h_mcs t.val t.property
  simp only [Satisfies]
  constructor
  · -- Forward: if (Sat φ → Sat ψ) then (φ → ψ) ∈ f(t)
    intro h_imp
    by_cases h_phi : φ ∈ limitF A h_mcs t.val
    · -- φ ∈ f(t): then Sat φ by IH, so Sat ψ, so ψ ∈ f(t) by IH
      have h_psi := ih_ψ.mp (h_imp (ih_φ.mpr h_phi))
      -- ψ ∈ f(t) implies (φ → ψ) ∈ f(t) in MCS
      have h_ax : DerivationTree FrameClass.Base [] (ψ.imp (φ.imp ψ)) :=
        .axiom [] _ (.imp_s ψ φ) trivial
      exact temporal_implication_property h_mcs_t
        (theoremInMcs h_mcs_t h_ax) h_psi
    · -- φ ∉ f(t): then ¬φ ∈ f(t), so (φ → ψ) ∈ f(t) by classical logic in MCS
      have h_neg_phi := mcs_neg_of_not_mem h_mcs_t h_phi
      -- ¬φ ∈ f(t) means (φ → ⊥) ∈ f(t)
      -- We need (φ → ψ) ∈ f(t). From ¬φ derive φ → ψ:
      -- In MCS: ¬φ ∈ Ω implies (φ → ψ) ∈ Ω
      -- Proof: ⊢ (φ → ⊥) → (φ → ψ) using efq
      have h_deriv : DerivationTree FrameClass.Base [] (φ.neg.imp (φ.imp ψ)) := by
        let ctx := [φ, φ.neg]
        have d_bot : DerivationTree FrameClass.Base ctx ⊥ :=
          .modus_ponens ctx φ ⊥
            (.assumption ctx φ.neg (by simp [List.mem_cons, ctx]))
            (.assumption ctx φ (by simp [List.mem_cons, ctx]))
        have d_efq : DerivationTree FrameClass.Base ctx ψ :=
          .modus_ponens ctx ⊥ ψ
            (.weakening [] ctx _ (.axiom [] _ (.efq ψ) trivial) (fun _ h => nomatch h))
            d_bot
        exact deductionTheorem [] φ.neg (φ.imp ψ)
          (deductionTheorem [φ.neg] φ ψ d_efq)
      exact temporal_implication_property h_mcs_t
        (theoremInMcs h_mcs_t h_deriv) h_neg_phi
  · -- Backward: if (φ → ψ) ∈ f(t) then (Sat φ → Sat ψ)
    intro h_imp_mem h_sat_phi
    have h_phi_mem := ih_φ.mp h_sat_phi
    exact ih_ψ.mpr (temporal_implication_property h_mcs_t h_imp_mem h_phi_mem)

/-- Until forward case: untl φ ψ ∈ f(t) implies Satisfies model t (untl φ ψ). -/
theorem truth_lemma_untl_forward (A : Set (Formula Atom)) (h_mcs : Temporal.SetMaximalConsistent A)
    (t : ChronicleSubtype A h_mcs) (φ ψ : Formula Atom)
    (ih_φ : ∀ s : ChronicleSubtype A h_mcs,
      Satisfies (chronicleModel A h_mcs) s φ ↔ φ ∈ limitF A h_mcs s.val)
    (ih_ψ : ∀ s : ChronicleSubtype A h_mcs,
      Satisfies (chronicleModel A h_mcs) s ψ ↔ ψ ∈ limitF A h_mcs s.val)
    (h_mem : (φ U ψ) ∈ limitF A h_mcs t.val) :
    Satisfies (chronicleModel A h_mcs) t (φ U ψ) := by
  -- untl φ ψ ∈ f(t.val). By limit_satisfies_c5_strong, get witness y > t.val
  -- with φ ∈ f(y) and ψ ∈ limitG(t.val, y) (i.e., ψ ∈ f(w) for all w between t and y).
  obtain ⟨y, hy_dom, hty, hy_phi, hy_guard⟩ :=
    limit_satisfies_c5_strong A h_mcs t.val t.property ψ φ h_mem
  -- Build the subtype witness
  let s : ChronicleSubtype A h_mcs := ⟨y, hy_dom⟩
  simp only [Satisfies]
  refine ⟨s, hty, (ih_φ s).mpr hy_phi, ?_⟩
  -- Guard: for all r with t < r < s, Sat r ψ
  intro ⟨r, hr_dom⟩ htr hrs
  exact (ih_ψ ⟨r, hr_dom⟩).mpr (hy_guard r hr_dom htr hrs)

/-- Until backward case: Satisfies model t (untl φ ψ) implies untl φ ψ ∈ f(t). -/
theorem truth_lemma_untl_backward (A : Set (Formula Atom)) (h_mcs : Temporal.SetMaximalConsistent A)
    (t : ChronicleSubtype A h_mcs) (φ ψ : Formula Atom)
    (ih_φ : ∀ s : ChronicleSubtype A h_mcs,
      Satisfies (chronicleModel A h_mcs) s φ ↔ φ ∈ limitF A h_mcs s.val)
    (ih_ψ : ∀ s : ChronicleSubtype A h_mcs,
      Satisfies (chronicleModel A h_mcs) s ψ ↔ ψ ∈ limitF A h_mcs s.val)
    (h_sat : Satisfies (chronicleModel A h_mcs) t (φ U ψ)) :
    (φ U ψ) ∈ limitF A h_mcs t.val := by
  -- By contradiction: assume (φ U ψ) ∉ f(t).
  by_contra h_not_mem
  have h_mcs_t := limit_c0 A h_mcs t.val t.property
  -- Then neg(φ U ψ) ∈ f(t)
  have h_neg := mcs_neg_of_not_mem h_mcs_t h_not_mem
  -- From h_sat: ∃ s > t, Sat s φ ∧ ∀ r ∈ (t, s), Sat r ψ
  simp only [Satisfies] at h_sat
  obtain ⟨⟨s, hs_dom⟩, hts, h_sat_phi, h_sat_guard⟩ := h_sat
  -- By IH: φ ∈ f(s)
  have h_phi_s := (ih_φ ⟨s, hs_dom⟩).mp h_sat_phi
  -- We have: neg(untl φ ψ) ∈ f(t.val), φ ∈ f(s), t.val < s.
  -- By limit_satisfies_c4: ∃ z ∈ limitDom, t < z < s, ψ.neg ∈ f(z).
  obtain ⟨z, hz_dom, htz, hzs, h_psi_neg⟩ :=
    limit_satisfies_c4 A h_mcs t.val s t.property hs_dom hts ψ φ h_neg h_phi_s
  -- z is in limitDom, so ⟨z, hz_dom⟩ is a valid subtype element.
  -- By the guard condition from h_sat: Sat ⟨z, hz_dom⟩ ψ (since t < z < s).
  have h_sat_z := h_sat_guard ⟨z, hz_dom⟩ htz hzs
  -- By IH: ψ ∈ f(z).
  have h_psi_z := (ih_ψ ⟨z, hz_dom⟩).mp h_sat_z
  -- But ψ.neg ∈ f(z), contradicting MCS consistency.
  exact mcs_not_mem_of_neg (limit_c0 A h_mcs z hz_dom) h_psi_neg h_psi_z

/-- Since forward case: snce φ ψ ∈ f(t) implies Satisfies model t (snce φ ψ). -/
theorem truth_lemma_snce_forward (A : Set (Formula Atom)) (h_mcs : Temporal.SetMaximalConsistent A)
    (t : ChronicleSubtype A h_mcs) (φ ψ : Formula Atom)
    (ih_φ : ∀ s : ChronicleSubtype A h_mcs,
      Satisfies (chronicleModel A h_mcs) s φ ↔ φ ∈ limitF A h_mcs s.val)
    (ih_ψ : ∀ s : ChronicleSubtype A h_mcs,
      Satisfies (chronicleModel A h_mcs) s ψ ↔ ψ ∈ limitF A h_mcs s.val)
    (h_mem : (φ S ψ) ∈ limitF A h_mcs t.val) :
    Satisfies (chronicleModel A h_mcs) t (φ S ψ) := by
  obtain ⟨y, hy_dom, hyt, hy_phi, hy_guard⟩ :=
    limit_satisfies_c5'_strong A h_mcs t.val t.property ψ φ h_mem
  let s : ChronicleSubtype A h_mcs := ⟨y, hy_dom⟩
  simp only [Satisfies]
  refine ⟨s, hyt, (ih_φ s).mpr hy_phi, ?_⟩
  intro ⟨r, hr_dom⟩ hsr hrt
  exact (ih_ψ ⟨r, hr_dom⟩).mpr (hy_guard r hr_dom hsr hrt)

/-- Since backward case: Satisfies model t (snce φ ψ) implies snce φ ψ ∈ f(t). -/
theorem truth_lemma_snce_backward (A : Set (Formula Atom)) (h_mcs : Temporal.SetMaximalConsistent A)
    (t : ChronicleSubtype A h_mcs) (φ ψ : Formula Atom)
    (ih_φ : ∀ s : ChronicleSubtype A h_mcs,
      Satisfies (chronicleModel A h_mcs) s φ ↔ φ ∈ limitF A h_mcs s.val)
    (ih_ψ : ∀ s : ChronicleSubtype A h_mcs,
      Satisfies (chronicleModel A h_mcs) s ψ ↔ ψ ∈ limitF A h_mcs s.val)
    (h_sat : Satisfies (chronicleModel A h_mcs) t (φ S ψ)) :
    (φ S ψ) ∈ limitF A h_mcs t.val := by
  by_contra h_not_mem
  have h_mcs_t := limit_c0 A h_mcs t.val t.property
  have h_neg := mcs_neg_of_not_mem h_mcs_t h_not_mem
  simp only [Satisfies] at h_sat
  obtain ⟨⟨s, hs_dom⟩, hst, h_sat_phi, h_sat_guard⟩ := h_sat
  have h_phi_s := (ih_φ ⟨s, hs_dom⟩).mp h_sat_phi
  obtain ⟨z, hz_dom, hsz, hzt, h_psi_neg⟩ :=
    limit_satisfies_c4' A h_mcs t.val s t.property hs_dom hst ψ φ h_neg h_phi_s
  have h_sat_z := h_sat_guard ⟨z, hz_dom⟩ hsz hzt
  have h_psi_z := (ih_ψ ⟨z, hz_dom⟩).mp h_sat_z
  exact mcs_not_mem_of_neg (limit_c0 A h_mcs z hz_dom) h_psi_neg h_psi_z

/-! ## Main Truth Lemma -/

/-- **Chronicle Truth Lemma**: For all formulas `φ` and points `t` in the
chronicle subtype, satisfaction in the chronicle model corresponds exactly
to membership in the limit point function.

This is Claim 2.11 of Burgess 1982, adapted to the temporal logic setting. -/
theorem chronicle_truth_lemma (A : Set (Formula Atom)) (h_mcs : Temporal.SetMaximalConsistent A)
    (t : ChronicleSubtype A h_mcs) (φ : Formula Atom) :
    Satisfies (chronicleModel A h_mcs) t φ ↔ φ ∈ limitF A h_mcs t.val := by
  induction φ generalizing t with
  | atom p => exact truth_lemma_atom A h_mcs t p
  | bot => exact truth_lemma_bot A h_mcs t
  | imp φ ψ ih_φ ih_ψ =>
    exact truth_lemma_imp A h_mcs t φ ψ (ih_φ t) (ih_ψ t)
  | untl φ ψ ih_φ ih_ψ =>
    constructor
    · exact truth_lemma_untl_backward A h_mcs t φ ψ ih_φ ih_ψ
    · exact truth_lemma_untl_forward A h_mcs t φ ψ ih_φ ih_ψ
  | snce φ ψ ih_φ ih_ψ =>
    constructor
    · exact truth_lemma_snce_backward A h_mcs t φ ψ ih_φ ih_ψ
    · exact truth_lemma_snce_forward A h_mcs t φ ψ ih_φ ih_ψ

end Cslib.Logic.Temporal.Metalogic.Chronicle
