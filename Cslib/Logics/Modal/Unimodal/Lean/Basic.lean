/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Foundations.Relation.Preserves
public import Cslib.Logics.Modal.Denotation
public import Cslib.Logics.Modal.Lean.Basic
public import Cslib.Logics.Modal.Unimodal.Basic

/-! # Basic Modal Logic for Lean -/

@[expose] public section

namespace Cslib.Logic.Modal

variable {τ : PFunctor} [τ.Unary] [Unique τ.A]

/-- Builds a unimodal predicate model from a binary relation. -/
abbrev Model.unimodalOfPredicates (r : α → α → Prop) : Model α τ (α → Prop) :=
  Modal.Model.ofPredicates (Frame.ofRelation r)

/-- Builds a unimodal container model from a binary relation. -/
abbrev Model.unimodalOfContainers [Membership α β] (r : α → α → Prop) : Model α τ β :=
  Modal.Model.ofContainers (Frame.ofRelation r)

open Model Relation
open scoped InferenceSystem Satisfies Proposition Frame

/-- Under `Model.unimodalOfPredicates r`, `P → □P` is an axiom iff `r` preserves `P`. -/
theorem Satisfies.unimodalOfPredicates_preserves_iff {P : α → Prop} (r : α → α → Prop) :
    (∀ a, ⇓Modal[Model.unimodalOfPredicates (τ := τ) r,a ⊨ P → □P]) ↔ Preserves r P := by
  constructor
  case mp =>
    intro h a₁ a₂ hr hPa₁
    simp only [Satisfies.imp_iff_imp] at h
    specialize h a₁ hPa₁
    simp only [Satisfies.box_iff_forall] at h
    specialize h a₂
    grind only [modal]
  case mpr =>
    grind [Preserves]

/-- Invariants are preserved by the reflexive and transitive closure of the accessibility relation.
-/
@[scoped grind ., modal .]
theorem Satisfies.unimodalOfPredicates_preserves_reflTransGen
    {r : α → α → Prop} {P : α → Prop}
    (h : ∀ a, ⇓Modal[unimodalOfPredicates (τ := τ) r,a ⊨ P → □P]) :
    ∀ a, ⇓Modal[unimodalOfPredicates (τ := τ) (Relation.ReflTransGen r),a ⊨ P → □P] := by
  apply (Satisfies.ofPredicates_preservesMap_iff
    (Frame.ofRelation (τ := τ) (Relation.ReflTransGen r))).mpr
  have hmap : (Frame.ofRelation (τ := τ) r).PreservesMap
      default P (fun _ => P) := by
    exact (Satisfies.ofPredicates_preservesMap_iff (Frame.ofRelation (τ := τ) r)).mp h
  grind

end Cslib.Logic.Modal
