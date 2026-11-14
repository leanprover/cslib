/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Init
public import Mathlib.ModelTheory.Bundled
public import Mathlib.ModelTheory.Ultraproducts

/-!
# Elementary classes of structures

A class of first-order structures is *elementary* if it is the class of all models of some theory,
and *finitely axiomatizable* if this theory can be taken to be finite. As in
`Mathlib.ModelTheory.Fraisse`, classes of structures are formalized as sets of bundled structures.

By Łoś's theorem an elementary class is closed under ultraproducts, and the complement of a
finitely axiomatizable class is closed under ultraproducts as well. The latter gives the standard
method for showing that a class is not finitely axiomatizable: exhibit structures outside of the
class with an ultraproduct inside of it.

## Main definitions

* `FirstOrder.Language.IsElementary`: the class is the class of models of a theory.
* `FirstOrder.Language.IsFinitelyAxiomatizable`: the class is the class of models of a finite
  theory.

## Main statements

* `FirstOrder.Language.IsElementary.product_mem`: elementary classes are closed under
  ultraproducts.
* `FirstOrder.Language.not_isFinitelyAxiomatizable_of_product`: a class containing an ultraproduct
  of structures that lie outside of the class is not finitely axiomatizable.
* `FirstOrder.Language.Ultraproduct.infinite_product`: an ultraproduct of structures whose
  cardinalities are eventually above every natural number is infinite.

-/

@[expose] public section

universe u v w w'

namespace FirstOrder.Language

open CategoryTheory (Bundled)

variable {L : Language.{u, v}}

/-- A class of structures is *elementary* if it is the class of all models of a theory. -/
def IsElementary (K : Set (Bundled.{w} L.Structure)) : Prop :=
  ∃ T : L.Theory, K = {M : Bundled.{w} L.Structure | (M : Type w) ⊨ T}

/-- A class of structures is *finitely axiomatizable* if it is the class of all models of a
finite theory. -/
def IsFinitelyAxiomatizable (K : Set (Bundled.{w} L.Structure)) : Prop :=
  ∃ T : L.Theory, T.Finite ∧ K = {M : Bundled.{w} L.Structure | (M : Type w) ⊨ T}

theorem IsFinitelyAxiomatizable.isElementary {K : Set (Bundled.{w} L.Structure)}
    (h : IsFinitelyAxiomatizable K) : IsElementary K :=
  let ⟨T, _, hT⟩ := h
  ⟨T, hT⟩

/-- The class of models of a theory is elementary. -/
theorem isElementary_setOf_model (T : L.Theory) :
    IsElementary {M : Bundled.{w} L.Structure | (M : Type w) ⊨ T} :=
  ⟨T, rfl⟩

section Ultraproduct

variable {K : Set (Bundled.{max w' w} L.Structure)} {ι : Type w'} (U : Ultrafilter ι)
  (M : ι → Type (max w' w)) [∀ a, L.Structure (M a)] [∀ a, Nonempty (M a)]

/-- An elementary class is closed under ultraproducts. -/
theorem IsElementary.product_mem (hK : IsElementary K)
    (h : ∀ᶠ a in (U : Filter ι), (Bundled.of (M a) : Bundled L.Structure) ∈ K) :
    (Bundled.of ((U : Filter ι).Product M) : Bundled L.Structure) ∈ K := by
  obtain ⟨T, rfl⟩ := hK
  refine (Theory.model_iff T).mpr fun φ hφ => (Ultraproduct.sentence_realize φ).mpr ?_
  exact h.mono fun a ha => (Theory.model_iff T).mp ha φ hφ

/-- If an ultraproduct lies in a finitely axiomatizable class, then so do almost all of its
factors. -/
theorem IsFinitelyAxiomatizable.eventually_mem_of_product_mem (hK : IsFinitelyAxiomatizable K)
    (h : (Bundled.of ((U : Filter ι).Product M) : Bundled L.Structure) ∈ K) :
    ∀ᶠ a in (U : Filter ι), (Bundled.of (M a) : Bundled L.Structure) ∈ K := by
  obtain ⟨T, hT, rfl⟩ := hK
  have hall : ∀ φ ∈ T, ∀ᶠ a in (U : Filter ι), M a ⊨ φ := fun φ hφ =>
    (Ultraproduct.sentence_realize φ).mp ((Theory.model_iff T).mp h φ hφ)
  exact ((Filter.eventually_all_finite hT).mpr hall).mono fun a ha => (Theory.model_iff T).mpr ha

/-- A class of structures that contains an ultraproduct of structures lying outside of the class
is not finitely axiomatizable. -/
theorem not_isFinitelyAxiomatizable_of_product
    (h : ∀ a, (Bundled.of (M a) : Bundled L.Structure) ∉ K)
    (hU : (Bundled.of ((U : Filter ι).Product M) : Bundled L.Structure) ∈ K) :
    ¬ IsFinitelyAxiomatizable K := fun hK =>
  let ⟨a, ha⟩ := (hK.eventually_mem_of_product_mem U M hU).exists
  h a ha

end Ultraproduct

/-- An ultraproduct of types whose cardinalities are eventually above every natural number is
infinite. -/
theorem Ultraproduct.infinite_product {ι : Type*} (U : Ultrafilter ι) (M : ι → Type w)
    [∀ a, Nonempty (M a)]
    (h : ∀ n : ℕ, ∀ᶠ a in (U : Filter ι), (n : Cardinal) ≤ Cardinal.mk (M a)) :
    Infinite ((U : Filter ι).Product M) := by
  let _ : ∀ a, Language.empty.Structure (M a) := fun _ => Language.emptyStructure
  rw [← Language.empty.model_infiniteTheory_iff]
  refine ⟨fun φ hφ => ?_⟩
  obtain ⟨n, rfl⟩ := hφ
  rw [Ultraproduct.sentence_realize]
  exact (h n).mono fun a ha => (Sentence.realize_cardGe _ n).2 ha

end FirstOrder.Language
