/-
Copyright (c) 2026 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/
module

public import Cslib.Logics.Propositional.NaturalDeduction.Theory
public import Mathlib.Order.Heyting.Basic

/-!-/

@[expose] public section

namespace Cslib.Logic.PL

open Proposition Theory InferenceSystem DerivableIn Derivation IsIntuitionistic IsClassical

universe u

variable {Atom : Type u} [DecidableEq Atom] {T : Theory Atom}

abbrev Valuation (Atom H : Type*) := Atom → H

variable {H : Type*} [HeytingAlgebra H] {v : Valuation Atom H}

namespace Valuation

omit [DecidableEq Atom]

/-- Extend the valuation `v: Atom → H` to all propositions using the Heyting algebra operations on
`H`. -/
def interp (v : Valuation Atom H) : Proposition Atom → H
  | atom x => v x
  | bot => ⊥
  | .and A B => v.interp A ⊓ v.interp B
  | .or A B => v.interp A ⊔ v.interp B
  | .imp A B => v.interp A ⇨ v.interp B

@[simp] lemma interp_atom {x} : v.interp (atom x) = v x := rfl
@[simp] lemma interp_bot : v.interp ⊥ = ⊥ := rfl
@[simp] lemma interp_and {A B} : v.interp (A ∧ B) = v.interp A ⊓ v.interp B := rfl
@[simp] lemma interp_or {A B} : v.interp (A ∨ B) = v.interp A ⊔ v.interp B := rfl
@[simp] lemma interp_imp {A B} : v.interp (A → B) = v.interp A ⇨ v.interp B := rfl
@[simp] lemma interp_not {A} : v.interp (¬A) = (v.interp A)ᶜ := himp_bot (v.interp A)

end Valuation

/-- The **soundness theorem** for natural deduction: for any derivable sequent `A₁, ..., Aₙ ⊢ B`,
and any valuation `v` into a Heyting algebra `H`, `v.interp A₁ ⊓ ... ⊓ v.interp Aₙ ≤ v.interp B`. -/
theorem _root_.Cslib.Logic.InferenceSystem.DerivableIn.soundness (hv : ∀ A ∈ T, v.interp A = ⊤)
    {Γ : Ctx Atom} {A : Proposition Atom} (h : DerivableIn T (Γ ⊢ A)) :
    Γ.inf v.interp ≤ v.interp A := by
  obtain ⟨D : T.Derivation Γ A⟩ := h
  induction D with
  | ax hA => simp [hv _ hA]
  | ass hA => exact Finset.inf_le hA
  | efq _ _ ih => exact ih.trans bot_le
  | andI _ _ ihA ihB => exact le_inf ihA ihB
  | andE₁ _ ih => exact ih.trans inf_le_left
  | andE₂ _ ih => exact ih.trans inf_le_right
  | orI₁ _ ih => exact ih.trans le_sup_left
  | orI₂ _ ih => exact ih.trans le_sup_right
  | orE _ _ _ ih ihA ihB =>
    rw [← inf_of_le_right ih]
    simpa [inf_sup_right] using (⟨ihA, ihB⟩ : _ ∧ _)
  | implI _ _ ih => simpa [inf_comm] using ih
  | implE _ _ ih ih' => exact (le_inf ih ih').trans himp_inf_le

theorem _root_.Cslib.Logic.InferenceSystem.DerivableIn.soundness₁ (hv : ∀ A ∈ T, v.interp A = ⊤)
    {A : Proposition Atom} (h : DerivableIn T A) : v.interp A = ⊤ :=
  eq_top_iff.mpr (h.soundness hv)

theorem _root_.Cslib.Logic.InferenceSystem.DerivableIn.ipl_soundness {Γ : Ctx Atom}
    {A : Proposition Atom} (h : DerivableIn (IPL Atom) (Γ ⊢ A)) : Γ.inf v.interp ≤ v.interp A :=
  h.soundness (by simp)

theorem isConsistent_ipl : IsConsistent Atom (IPL Atom) := by
  rw [IsIntuitionistic.isConsistent_iff_not_derivableIn_bot]
  intro h
  simpa using h.ipl_soundness (v := fun _ ↦ True)

theorem _root_.Cslib.Logic.InferenceSystem.DerivableIn.cpl_soundness {H : Type*} [BooleanAlgebra H]
    {v : Valuation Atom H} {Γ : Ctx Atom} {A : Proposition Atom}
    (h : DerivableIn (CPL Atom) (Γ ⊢ A)) : Γ.inf v.interp ≤ v.interp A :=
  h.soundness (by simp)

theorem isConsistent_cpl : IsConsistent Atom (CPL Atom) := by
  rw [IsIntuitionistic.isConsistent_iff_not_derivableIn_bot]
  intro h
  simpa using h.cpl_soundness (v := fun _ ↦ True)

namespace Theory

def Lindenbaum (T : Theory Atom) := Quotient T.propositionSetoid

instance Lindenbaum.heytingAlgebra : HeytingAlgebra T.Lindenbaum where
  le := Quotient.lift₂ (fun A B ↦ DerivableIn T ({A} ⊢ B)) <| by
    intro A B A' B' (eA : A ≡[T] A') (eB : B ≡[T] B')
    rw [← Finset.insert_empty, ← Finset.insert_empty, equiv_iff_equiv_derivableIn.mp eB.symm,
      equiv_iff_equiv_derivableIn_hypothesis.mp eA ∅ B]
  le_refl := Quotient.ind fun A ↦ ⟨refl A⟩
  le_trans := Quotient.ind₂ fun _ _ ↦ Quotient.ind fun _ ↦ DerivableIn.trans
  le_antisymm := Quotient.ind₂ fun _ _ h h' ↦ Quotient.sound ⟨h.some, h'.some⟩
  inf := Quotient.map₂ (· ∧ ·) fun _ _ hA _ _ hB ↦ hA.and hB
  inf_le_left := Quotient.ind₂ fun A B ↦ ⟨leftOfAnd A B⟩
  inf_le_right := Quotient.ind₂ fun A B ↦ ⟨rightOfAnd A B⟩
  le_inf := Quotient.ind₂ fun _ _ ↦ Quotient.ind fun _ ⟨D⟩ ⟨D'⟩ ↦ ⟨D.andI D'⟩
  sup := Quotient.map₂ (· ∨ ·) fun _ _ hA _ _ hB ↦ hA.or hB
  le_sup_left := Quotient.ind₂ fun A B ↦ ⟨orOfLeft A B⟩
  le_sup_right := Quotient.ind₂ fun A B ↦ ⟨orOfRight A B⟩
  sup_le := Quotient.ind₂ fun A B ↦ Quotient.ind fun _ ⟨D⟩ ⟨D'⟩ ↦
    ⟨(Derivation.refl <| A ∨ B).orE (D.weakCtx (by grind)) (D'.weakCtx (by grind))⟩
  bot := ⟦⊥⟧
  bot_le := Quotient.ind fun A ↦ ⟨efqRule {⊥} A <| .refl ⊥⟩
  top := ⟦⊤⟧
  le_top := Quotient.ind fun _ ↦ ⟨derivationTop.weakCtx <| by simp⟩
  himp := Quotient.map₂ (· → ·) fun _ _ hA _ _ hB ↦ hA.imp hB
  le_himp_iff := Quotient.ind₂ fun _ _ ↦ Quotient.ind fun _ ↦
    DerivableIn.imp_iff_insert_and (Γ := ∅)
  compl := Quotient.map (¬·) fun _ _ hA ↦ hA.not
  himp_bot := Quotient.ind fun _ ↦ rfl

instance Lidenbaum.booleanAlgebra [hT : IsClassical Atom T] : BooleanAlgebra T.Lindenbaum where
  le_top _ := le_top
  bot_le _ := bot_le
  inf_compl_le_bot _ := inf_compl_eq_bot.le
  top_le_sup_compl := Quotient.ind fun A ↦ ⟨(hT.lem A).weakCtx (by simp)⟩
  himp_eq := Quotient.ind₂ fun A B ↦ Quotient.sound ⟨imp_equiv_or_not A B⟩

def val : Valuation Atom T.Lindenbaum := fun x ↦ ⟦atom x⟧

theorem val_spec (A : Proposition Atom) : T.val.interp A = ⟦A⟧ := by
  induction A with
  | atom => rfl
  | bot => rfl
  | and A B ihA ihB => simp [ihA, ihB]; rfl
  | or A B ihA ihB => simp [ihA, ihB]; rfl
  | imp A B ihA ihB => simp [ihA, ihB]; rfl

theorem val_interp_of_mem (A : Proposition Atom) (hA : A ∈ T) : T.val.interp A = ⊤ := by
  rw [eq_top_iff, val_spec]
  exact ⟨ax hA⟩

theorem Lindenbaum.completeness₁ {A : Proposition Atom} (h : T.val.interp A = ⊤) :
    DerivableIn T A := by
  rw [val_spec] at h
  exact (derivable_iff_equiv_top A).mpr <| Quotient.exact h

theorem Lindenbaum.completeness {Γ : Ctx Atom} {A : Proposition Atom}
    (h : Γ.inf T.val.interp ≤ T.val.interp A) : DerivableIn T (Γ ⊢ A) := by
  obtain ⟨Γ, -, rfl⟩ := Γ.exists_list_nodup_eq
  suffices DerivableIn T (Γ.foldl (fun B C ↦ C → B) A : Proposition Atom) by
    simpa using toFinset_union_iff.mpr this
  apply Lindenbaum.completeness₁
  induction Γ generalizing A with
  | nil => simpa using eq_top_iff.mpr h
  | cons B Γ ih =>
    apply ih
    simpa [inf_comm] using h

theorem_wanted cpl_completeness_bool {Γ : Ctx Atom} {A : Proposition Atom}
    (h : ∀ (v : Valuation Atom Bool), Γ.inf v.interp ≤ v.interp A) :
    DerivableIn (CPL Atom) (Γ ⊢ A)

end Theory

theorem adequacy₁ {A : Proposition Atom} :
    DerivableIn T A ↔ ∀ {H : Type u} [HeytingAlgebra H] {v : Valuation Atom H},
      (∀ B ∈ T, v.interp B = ⊤) → v.interp A = ⊤ :=
  ⟨fun h _ _ _ hv ↦ h.soundness₁ hv, fun h ↦ Lindenbaum.completeness₁ <| h val_interp_of_mem⟩

theorem adequacy {Γ : Ctx Atom} {A : Proposition Atom} :
    DerivableIn T (Γ ⊢ A) ↔ ∀ {H : Type u} [HeytingAlgebra H] {v : Valuation Atom H},
      (∀ B ∈ T, v.interp B = ⊤) → Γ.inf v.interp ≤ v.interp A :=
  ⟨fun h _ _ _ hv ↦ h.soundness hv, fun h ↦ Lindenbaum.completeness <| h val_interp_of_mem⟩

theorem ipl_adequacy {Γ : Ctx Atom} {A : Proposition Atom} :
    DerivableIn (IPL Atom) (Γ ⊢ A) ↔ ∀ {H : Type u} [HeytingAlgebra H] (v : Valuation Atom H),
      Γ.inf v.interp ≤ v.interp A :=
  ⟨fun h _ _ _ ↦ h.ipl_soundness, fun h ↦ Lindenbaum.completeness <| h (IPL Atom).val⟩

theorem cpl_adequacy {Γ : Ctx Atom} {A : Proposition Atom} :
    DerivableIn (CPL Atom) (Γ ⊢ A) ↔ ∀ {H : Type u} [BooleanAlgebra H] (v : Valuation Atom H),
      Γ.inf v.interp ≤ v.interp A :=
  ⟨fun h _ _ _ ↦ h.cpl_soundness, fun h ↦ Lindenbaum.completeness <| h (CPL Atom).val⟩

theorem_wanted cpl_adequacy_bool {Γ : Ctx Atom} {A : Proposition Atom} :
    DerivableIn (CPL Atom) (Γ ⊢ A) ↔ ∀ (v : Valuation Atom Bool), Γ.inf v.interp ≤ v.interp A :=
  ⟨fun h v ↦ h.cpl_soundness, ❰cpl_completeness_bool❱⟩

end Cslib.Logic.PL
