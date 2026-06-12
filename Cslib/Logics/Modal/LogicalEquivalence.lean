/-
Copyright (c) 2026 Fabrizio Montesi, Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Modal.Basic

/-! # Logical Equivalence for Modal Propositions

This file defines a one-hole context for `Proposition`, a fill operation that substitutes a
proposition into the hole, and proves that logical equivalence (agreement of satisfaction across all
models and worlds) is a congruence with respect to contexts.

## Main Definitions

* `Proposition.Context` -- a one-hole context matching the `Proposition` constructors
* `Proposition.Context.fill` -- substitute a proposition into the hole
* `LogicallyEquivalent` -- two propositions are logically equivalent when they are satisfied by
  exactly the same model-world pairs
* `LogicallyEquivalent.congruence` -- logical equivalence is preserved under all contexts

## Design Notes

The `Context` constructors mirror the recursive positions of `Proposition`: `imp` has two
sub-proposition positions (left and right), and `box` has one. The ground constructors `atom` and
`bot` have no sub-propositions, so they do not appear in `Context`.

This file states logical equivalence and its congruence directly rather than instantiating the
shared `Cslib.Logic.LogicalEquivalence` typeclass (as `Cslib.Logic.HML` does). That typeclass is
built around a single fixed relation `eqv : Proposition → Proposition → Prop` together with a
`Satisfies`-to-judgement bundling adapter (`HasContext`/`HasHContext`/`eqvFillValid`). Two points
make it a poor fit here. First, modal equivalence is naturally relative to a class of admissible
models -- logic `K` over all models, `T` over reflexive models, and so on -- which a single fixed
`eqv` cannot express; only the all-models case fits the interface. Second, instantiating the class
requires repackaging the three-place `Satisfies m w φ` into a one-argument judgement purely to
satisfy `Valid : Judgement → Sort`, which is indirection the modal development does not otherwise
need: the only fact required downstream is congruence, proved here in a few lines by induction on
`Context`.
-/

@[expose] public section

namespace Cslib.Logic.Modal

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
def Proposition.Context.fill : Proposition.Context Atom → Proposition Atom → Proposition Atom
  | .hole, φ => φ
  | .impL c ψ, φ => c.fill φ → ψ
  | .impR ψ c, φ => ψ → c.fill φ
  | .box c, φ => □(c.fill φ)

/-- Two propositions are logically equivalent when they agree on satisfaction across all models
and worlds. -/
def LogicallyEquivalent.{v} {Atom : Type u} (φ ψ : Proposition Atom) : Prop :=
  ∀ (World : Type v) (m : Model World Atom) (w : World), Satisfies m w φ ↔ Satisfies m w ψ

/-- Logical equivalence is a congruence: if `φ` and `ψ` are logically equivalent, then
`c.fill φ` and `c.fill ψ` are logically equivalent for any context `c`. -/
theorem LogicallyEquivalent.congruence.{v} {Atom : Type u} {φ ψ : Proposition Atom}
    (c : Proposition.Context Atom) (h : LogicallyEquivalent.{v} φ ψ) :
    LogicallyEquivalent.{v} (c.fill φ) (c.fill ψ) := by
  intro World m
  induction c with
  | hole => exact h World m
  | impL c _ ih =>
    intro w
    simp only [Proposition.Context.fill, Satisfies]
    exact ⟨fun hf ha => hf ((ih w).mpr ha), fun hf ha => hf ((ih w).mp ha)⟩
  | impR _ c ih =>
    intro w
    simp only [Proposition.Context.fill, Satisfies]
    exact ⟨fun hf ha => (ih w).mp (hf ha), fun hf ha => (ih w).mpr (hf ha)⟩
  | box c ih =>
    intro w
    simp only [Proposition.Context.fill, Satisfies]
    exact ⟨fun hf w' hr => (ih w').mp (hf w' hr),
           fun hf w' hr => (ih w').mpr (hf w' hr)⟩

end Cslib.Logic.Modal
