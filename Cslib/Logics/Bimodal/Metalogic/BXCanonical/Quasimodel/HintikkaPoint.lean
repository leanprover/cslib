/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Bimodal.Metalogic.BXCanonical.Quasimodel.SubformulaClosure
public import Cslib.Logics.Bimodal.Metalogic.BXCanonical.Frame

/-!
# Hintikka Points

Defines Hintikka points over a Sigma-closure.

## References

* Ported from BimodalLogic/Theories/Bimodal/Metalogic/BXCanonical/Quasimodel/HintikkaPoint.lean
-/

set_option linter.style.emptyLine false
set_option linter.style.longLine false

@[expose] public section

namespace Cslib.Logic.Bimodal.Metalogic.BXCanonical.Quasimodel

open Cslib.Logic.Bimodal
open Cslib.Logic.Bimodal.Metalogic.Core
open Cslib.Logic.Bimodal.Metalogic.Bundle
open Cslib.Logic.Bimodal.Metalogic.BXCanonical

variable {Atom : Type*} [DecidableEq Atom]

/-! ## Hintikka Point Definition -/

structure HintikkaPoint (Sigma : Finset (Formula Atom)) where
  formulas : Finset (Formula Atom)
  subset_sigma : formulas ⊆ Sigma
  locally_consistent : ∀ f ∈ formulas, Formula.neg f ∉ formulas
  bot_free : (Formula.bot : Formula Atom) ∉ formulas

theorem HintikkaPoint.ext {Sigma : Finset (Formula Atom)} {h1 h2 : HintikkaPoint Sigma}
    (heq : h1.formulas = h2.formulas) : h1 = h2 := by
  cases h1; cases h2; simp at heq; subst heq; rfl

instance {Sigma : Finset (Formula Atom)} : DecidableEq (HintikkaPoint Sigma) :=
  fun h1 h2 =>
    if heq : h1.formulas = h2.formulas then
      isTrue (HintikkaPoint.ext heq)
    else
      isFalse (fun h => heq (by cases h; rfl))

theorem HintikkaPoint.mem_sigma {Sigma : Finset (Formula Atom)} (h : HintikkaPoint Sigma)
    {f : Formula Atom} (hf : f ∈ h.formulas) : f ∈ Sigma :=
  h.subset_sigma hf

theorem HintikkaPoint.not_mem_of_neg_mem {Sigma : Finset (Formula Atom)} (h : HintikkaPoint Sigma)
    {f : Formula Atom} (hf : Formula.neg f ∈ h.formulas) : f ∉ h.formulas := by
  intro hf_in
  exact h.locally_consistent f hf_in hf

/-! ## Sigma-Signature -/

open Classical in
noncomputable def sigmaSignatureFormulas (w : BXPoint Atom) (Sigma : Finset (Formula Atom)) :
    Finset (Formula Atom) :=
  Sigma.filter (fun f => f ∈ w.formulas)

open Classical in
theorem sigma_signature_subset (w : BXPoint Atom) (Sigma : Finset (Formula Atom)) :
    sigmaSignatureFormulas w Sigma ⊆ Sigma :=
  Finset.filter_subset _ _

open Classical in
theorem sigma_signature_mem_iff (w : BXPoint Atom) (Sigma : Finset (Formula Atom)) (f : Formula Atom) :
    f ∈ sigmaSignatureFormulas w Sigma ↔ f ∈ Sigma ∧ f ∈ w.formulas := by
  simp [sigmaSignatureFormulas, Finset.mem_filter]

open Classical in
theorem sigma_signature_consistent (w : BXPoint Atom) (Sigma : Finset (Formula Atom)) :
    ∀ f ∈ sigmaSignatureFormulas w Sigma,
      Formula.neg f ∉ sigmaSignatureFormulas w Sigma := by
  intro f hf hfn
  rw [sigma_signature_mem_iff] at hf hfn
  exact set_consistent_not_both w.is_mcs.1 f hf.2 hfn.2

open Classical in
theorem sigma_signature_bot_free (w : BXPoint Atom) (Sigma : Finset (Formula Atom)) :
    (Formula.bot : Formula Atom) ∉ sigmaSignatureFormulas w Sigma := by
  intro h
  rw [sigma_signature_mem_iff] at h
  have : SetConsistent FrameClass.Base w.formulas := w.is_mcs.1
  exact this [(Formula.bot : Formula Atom)] (fun ψ hψ => by simp at hψ; rw [hψ]; exact h.2)
    ⟨DerivationTree.assumption [(Formula.bot : Formula Atom)] (Formula.bot : Formula Atom) (by simp)⟩

open Classical in
noncomputable def sigmaSignature (w : BXPoint Atom) (Sigma : Finset (Formula Atom)) :
    HintikkaPoint Sigma where
  formulas := sigmaSignatureFormulas w Sigma
  subset_sigma := sigma_signature_subset w Sigma
  locally_consistent := sigma_signature_consistent w Sigma
  bot_free := sigma_signature_bot_free w Sigma

open Classical in
theorem sigma_signature_mem {w : BXPoint Atom} {Sigma : Finset (Formula Atom)} {f : Formula Atom} :
    f ∈ (sigmaSignature w Sigma).formulas ↔ f ∈ Sigma ∧ f ∈ w.formulas := by
  simp [sigmaSignature, sigmaSignatureFormulas, Finset.mem_filter]

/-! ## Finiteness -/

theorem hintikka_point_formulas_injective (Sigma : Finset (Formula Atom)) :
    Function.Injective (fun (h : HintikkaPoint Sigma) => h.formulas) :=
  fun h1 h2 heq => HintikkaPoint.ext heq

end Cslib.Logic.Bimodal.Metalogic.BXCanonical.Quasimodel
