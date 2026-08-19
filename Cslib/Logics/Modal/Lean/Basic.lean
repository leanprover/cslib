/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Logics.Modal.Denotation

/-! # Modal Logic for Lean

This module develops the interplay between modal logic and Lean's propositional language, in order
to enable the use of modal logic to reason about standard Lean relations using `Prop`.
-/

@[expose] public section

namespace Cslib.Logic.Modal

namespace Model

/-- Given a relation `r` on `α`, constructs the modal model whose worlds are elements of `α`
and whose atoms are Lean predicates on `α` (`α → Prop`).

Valuation checks that a world satisfies a predicate. For example, under `Model.ofPredicates r`, `□P`
at `a : α` means that `P a'` holds at every `a'` such that `r a a'`. -/
abbrev ofPredicates (r : α → α → Prop) : Model α (α → Prop) where
  r := r
  v w P := P w

/-- Given a relation `r` on `α` and a container type `β` for `α` (`Membership α β`), constructs the
modal model whose worlds are elements of `α` and whose atoms are of type `β`.

Valuation is membership. For example, under `Model.ofContainers r`, `□b` at `a : α` means that
`a' ∈ b` holds for every `a'` such that `r a a'`. -/
abbrev ofContainers [Membership α β] (r : α → α → Prop) : Model α β where
  r := r
  v w p := w ∈ p

/-- Abbreviation for `Model.ofContainers` where the container type is a `Set`. -/
abbrev ofSets (r : α → α → Prop) : Model α (Set α) := ofContainers r

/-- The set model and predicate model of a relation are definitionally equal. -/
theorem ofSets_eq_ofPredicates (r : α → α → Prop) :
    ofSets r = ofPredicates r := rfl

end Model

open Model Relation
open scoped InferenceSystem Satisfies

/-! ## Models of Lean predicates -/

/-- Under `Model.ofPredicates r`, an atomic proposition `P` holds at `a` iff `P a`. -/
@[scoped grind =]
theorem Satisfies.ofPredicates_atom_iff {P : α → Prop} (r : α → α → Prop) :
    ⇓Modal[ofPredicates r, a ⊨ P] ↔ P a := Iff.rfl

/-- Under `Model.ofPredicates r`, `P → □P` is an axiom iff `r` preserves `P`. -/
@[scoped grind ⇒]
theorem Satisfies.ofPredicates_preserves_iff {P : α → Prop} (r : α → α → Prop) :
    (∀ a, ⇓Modal[ofPredicates r, a ⊨ P → □P]) ↔ Preserves r P := by
  constructor
  case mp =>
    intro h a₁ a₂ hr hPa₁
    grind [h a₁]
  case mpr =>
    grind [Preserves]

/-- Logical equivalence under `Model.ofPredicates r`. -/
abbrev Proposition.Equiv.OfPredicates (r : α → α → Prop) := Proposition.Equiv (ofPredicates r)

/-- Logical equivalence under `Model.ofContainers r`. -/
abbrev Proposition.Equiv.OfContainers [Membership α β] (r : α → α → Prop) :=
  Proposition.Equiv (ofContainers (β := β) r)

/-- Logically equivalent propositions under `Equiv.OfPredicates r` have the same denotation in the
Lean modal model induced by `ofPredicates r`. -/
@[scoped grind ⇒]
theorem Proposition.equivOfPredicates_denotation_eq {r : α → α → Prop}
    {φ₁ φ₂ : Proposition (α → Prop)} :
    (φ₁ ≡[Equiv.OfPredicates r] φ₂) ↔
      φ₁.denotation (ofPredicates r) = φ₂.denotation (ofPredicates r) :=
  equiv_iff_denotation_eq

/-- Logically equivalent propositions under `Equiv.OfContainers r` have the same denotation in the
Lean modal model induced by `ofContainers r`. -/
@[scoped grind ⇒]
theorem Proposition.equivOfContainers_denotation_eq {α} [Membership α β] {r : α → α → Prop}
    {φ₁ φ₂ : Proposition β} :
    (φ₁ ≡[Equiv.OfContainers (β := β) r] φ₂) ↔
      φ₁.denotation (ofContainers r) = φ₂.denotation (ofContainers r) :=
  equiv_iff_denotation_eq

/-- Pointwise conjunction of Lean predicates is logically equivalent to their modal conjunction in
the Lean modal model induced by `r`. -/
theorem Proposition.equivOfPredicates_and {r : α → α → Prop} {P Q : α → Prop} :
    (fun a => P a ∧ Q a) ≡[Equiv.OfPredicates r] (P ∧ Q) := by grind

/-- Under `Equiv.OfContainers r`, if membership in the infimum of two containers is equivalent to
membership in both containers, then atomic infimum is logically equivalent to modal conjunction. -/
theorem Proposition.ofContainers_inf_equiv [Membership α β] [Min β] (r : α → α → Prop) (p q : β)
    (h : ∀ x, x ∈ p ⊓ q ↔ x ∈ p ∧ x ∈ q) :
    (↑(p ⊓ q) : Proposition β) ≡[Equiv.OfContainers r] (p ∧ q) := by grind

end Cslib.Logic.Modal
