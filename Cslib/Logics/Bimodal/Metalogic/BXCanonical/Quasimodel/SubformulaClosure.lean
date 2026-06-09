/-
Copyright (c) 2026 Benjamin Brastmckie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brastmckie
-/

import Cslib.Logics.Bimodal.Syntax.Formula
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image

/-!
# Subformula Closure (Sigma-Closure)

Defines the finite subformula closure for the Hintikka-set quasimodel construction.

## References

* Ported from BimodalLogic/Theories/Bimodal/Metalogic/BXCanonical/Quasimodel/SubformulaClosure.lean
-/

set_option linter.style.emptyLine false
set_option linter.style.longLine false

namespace Cslib.Logic.Bimodal.Metalogic.BXCanonical.Quasimodel

open Cslib.Logic.Bimodal

variable {Atom : Type*} [DecidableEq Atom]

/-! ## Subformula Extraction -/

def subformulas : Formula Atom → Finset (Formula Atom)
  | f@(Formula.atom _) => {f}
  | f@Formula.bot => {f}
  | f@(Formula.imp φ ψ) => insert f (subformulas φ ∪ subformulas ψ)
  | f@(Formula.box φ) => insert f (subformulas φ)
  | f@(Formula.untl φ ψ) => insert f (subformulas φ ∪ subformulas ψ)
  | f@(Formula.snce φ ψ) => insert f (subformulas φ ∪ subformulas ψ)

theorem self_mem_subformulas (f : Formula Atom) : f ∈ subformulas f := by
  cases f <;> simp [subformulas]

/-! ## G/H Enrichment -/

def ghEnrichment (Omega : Finset (Formula Atom)) : Finset (Formula Atom) :=
  Omega ∪ Omega.image Formula.all_future ∪ Omega.image Formula.all_past

/-! ## Full Subformula Closure -/

def SubformulaClosure (target : Formula Atom) : Finset (Formula Atom) :=
  let base := ghEnrichment (subformulas target)
  base ∪ base.image Formula.neg

theorem target_mem (target : Formula Atom) : target ∈ SubformulaClosure target := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_union_left _ (self_mem_subformulas target)

theorem neg_of_base_mem {target f : Formula Atom}
    (h : f ∈ ghEnrichment (subformulas target)) :
    Formula.neg f ∈ SubformulaClosure target := by
  apply Finset.mem_union_right
  exact Finset.mem_image.mpr ⟨f, h, rfl⟩

theorem subformula_mem {target f : Formula Atom} (h : f ∈ subformulas target) :
    f ∈ SubformulaClosure target := by
  apply Finset.mem_union_left
  exact Finset.mem_union_left _ (Finset.mem_union_left _ h)

theorem g_enrichment_mem {target f : Formula Atom} (h : f ∈ subformulas target) :
    Formula.all_future f ∈ SubformulaClosure target := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_image.mpr ⟨f, h, rfl⟩

theorem h_enrichment_mem {target f : Formula Atom} (h : f ∈ subformulas target) :
    Formula.all_past f ∈ SubformulaClosure target := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_image.mpr ⟨f, h, rfl⟩

theorem closure_finite (target : Formula Atom) : (SubformulaClosure target).Nonempty :=
  ⟨target, target_mem target⟩

theorem neg_pairing (target : Formula Atom) :
    ∀ f ∈ ghEnrichment (subformulas target),
      f ∈ SubformulaClosure target ∧ Formula.neg f ∈ SubformulaClosure target := by
  intro f hf
  constructor
  · exact Finset.mem_union_left _ hf
  · exact neg_of_base_mem hf

end Cslib.Logic.Bimodal.Metalogic.BXCanonical.Quasimodel
