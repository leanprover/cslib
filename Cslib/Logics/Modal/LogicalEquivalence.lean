/-
Copyright (c) 2026 Fabrizio Montesi, Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Basic
public import Cslib.Foundations.Logic.LogicalEquivalence

/-! # Logical Equivalence for Modal Propositions

This file defines a one-hole context for `Proposition`, a fill operation that substitutes a
proposition into the hole, and proves that logical equivalence (agreement of satisfaction across all
models and worlds) is a congruence with respect to contexts.

## Main Definitions

* `Proposition.Context` -- a one-hole context matching the `Proposition` constructors
* `Proposition.Context.fill` -- substitute a proposition into the hole
* `Proposition.Equiv` -- two propositions are logically equivalent relative to a class of models
* `LogicalEquivalence` -- typeclass instance connecting equivalence, congruence, and validity

## Design Notes

The `Context` constructors mirror the recursive positions of `Proposition`: `imp` has two
sub-proposition positions (left and right), and `box` has one. The ground constructors `atom` and
`bot` have no sub-propositions, so they do not appear in `Context`.
-/

@[expose] public section

namespace Cslib.Logic.Modal

open scoped InferenceSystem Proposition

/-- Logical equivalence for modal propositions, parametric on a class of models `S`.
Two propositions are equivalent when they are satisfied by the same model-world pairs in `S`. -/
def Proposition.Equiv (S : Set (Model World Atom)) (φ₁ φ₂ : Proposition Atom) : Prop :=
  ∀ m ∈ S, ∀ w : World, ⇓Modal[m,w ⊨ φ₁] ↔ ⇓Modal[m,w ⊨ φ₂]

@[inherit_doc]
scoped notation φ₁ " ≡[" S "] " φ₂ => Proposition.Equiv S φ₁ φ₂

@[simp]
theorem Proposition.equiv_def {S : Set (Model World Atom)}
    {φ₁ φ₂ : Proposition Atom} :
    (φ₁ ≡[S] φ₂) ↔ ∀ m ∈ S, ∀ w : World, ⇓Modal[m,w ⊨ φ₁] ↔ ⇓Modal[m,w ⊨ φ₂] :=
  Iff.rfl

theorem Proposition.equiv_iff {S : Set (Model World Atom)}
    {φ₁ φ₂ : Proposition Atom}
    (h : φ₁ ≡[S] φ₂) {m : Model World Atom} (hm : m ∈ S) {w : World} :
    ⇓Modal[m,w ⊨ φ₁] ↔ ⇓Modal[m,w ⊨ φ₂] :=
  h m hm w

/-- A one-hole context for `Proposition`. Each constructor corresponds to a recursive position
in `Proposition`: `impL` is the left argument of `imp`, `impR` is the right argument, and `box`
is the argument of `box`. The `hole` constructor marks the position to be filled. -/
inductive Proposition.Context (Atom : Type u) : Type u where
  /-- The position to substitute. -/
  | hole
  /-- Context in the left argument of `imp`. -/
  | impL (c : Context Atom) (φ : Proposition Atom)
  /-- Context in the right argument of `imp`. -/
  | impR (φ : Proposition Atom) (c : Context Atom)
  /-- Context under `box`. -/
  | box (c : Context Atom)

/-- Fill the hole in a context with a proposition. -/
@[scoped grind =]
def Proposition.Context.fill : Proposition.Context Atom → Proposition Atom → Proposition Atom
  | .hole, φ => φ
  | .impL c ψ, φ => .imp (c.fill φ) ψ
  | .impR ψ c, φ => .imp ψ (c.fill φ)
  | .box c, φ => .box (c.fill φ)

instance : HasContext (Proposition Atom) :=
  ⟨Proposition.Context Atom, Proposition.Context.fill⟩

@[simp]
theorem Proposition.Context.fill_def (c : Proposition.Context Atom) (φ : Proposition Atom) :
    (c : HasContext.Context (Proposition Atom))<[φ] = c.fill φ := rfl

instance : IsEquiv (Proposition Atom)
    (Proposition.Equiv (World := World) (S : Set (Model World Atom))) where
  refl _ _ _ _ := Iff.rfl
  symm _ _ hab m hm w := (hab m hm w).symm
  trans _ _ _ hab hbc m hm w := (hab m hm w).trans (hbc m hm w)

instance : Congruence (Proposition Atom)
    (Proposition.Equiv (World := World) (S : Set (Model World Atom))) where
  elim := by
    intro ctx a b hab
    change Proposition.Equiv S (ctx.fill a) (ctx.fill b)
    intro m hm
    induction ctx with
    | hole => exact hab m hm
    | impL c _ ih =>
      intro w
      simp only [Proposition.Context.fill, ← derivation_def, Satisfies]
      exact ⟨fun hf ha => hf ((ih w).mpr ha), fun hf ha => hf ((ih w).mp ha)⟩
    | impR _ c ih =>
      intro w
      simp only [Proposition.Context.fill, ← derivation_def, Satisfies]
      exact ⟨fun hf ha => (ih w).mp (hf ha), fun hf ha => (ih w).mpr (hf ha)⟩
    | box c ih =>
      intro w
      simp only [Proposition.Context.fill, ← derivation_def, Satisfies]
      exact ⟨fun hf w' hr => (ih w').mp (hf w' hr),
             fun hf w' hr => (ih w').mpr (hf w' hr)⟩

/-- Judgemental contexts for satisfaction. -/
structure Satisfies.Context (World : Type*) (Atom : Type*) where
  /-- The class of models. -/
  S : Set (Model World Atom)
  /-- The model. -/
  m : Model World Atom
  /-- Evidence that the model belongs to the class. -/
  hm : m ∈ S
  /-- The world satisfying the proposition. -/
  w : World

/-- Fills a judgemental context with a proposition to obtain a judgement. -/
def Satisfies.Context.fill (c : Satisfies.Context World Atom) (φ : Proposition Atom) :
    Judgement World Atom :=
  ⟨c.m, c.w, φ⟩

instance : HasHContext (Judgement World Atom) (Proposition Atom) :=
  ⟨Satisfies.Context World Atom, Satisfies.Context.fill⟩

instance : LogicalEquivalence
    (Proposition Atom) (Judgement World Atom) Satisfies.Bundled where
  eqv := Proposition.Equiv Set.univ
  eqvFillValid heqv c h := by
    change Satisfies c.m c.w _
    have h' : Satisfies c.m c.w _ := h
    exact (heqv c.m (Set.mem_univ _) c.w).mp h'

end Cslib.Logic.Modal
