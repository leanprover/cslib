/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Logics.Modal.Basic

/-! # Denotational semantics for Modal Logic

A denotational semantics for modal logic, inspired by the one for Hennessy-Milner Logic
(`Cslib.Logic.HML`).
-/

@[expose] public section

namespace Cslib.Logic.Modal

open scoped Proposition InferenceSystem

/-- Denotation of a proposition. -/
@[simp, scoped grind =]
def Proposition.denotation (m : Model World Atom) :
    Proposition Atom → Set World
  | .atom p => {w | m.v w p}
  | .neg φ => (φ.denotation m)ᶜ
  | .and φ₁ φ₂ => φ₁.denotation m ∩ φ₂.denotation m
  | .diamond φ => {w | ∃ w', m.r w w' ∧ w' ∈ φ.denotation m}

/-- Characterisation theorem for the denotational semantics. -/
@[scoped grind =]
theorem satisfies_mem_denotation {m : Model World Atom} {φ : Proposition Atom} :
    w ∈ φ.denotation m ↔ ⇓Modal[m,w ⊨ φ] := by
  induction φ generalizing w <;> grind

/-- A world is in the denotation of a proposition iff it is not in the denotation of the negation
of the proposition. -/
@[scoped grind =]
theorem neg_denotation {m : Model World Atom} (φ : Proposition Atom) :
    w ∉ (¬φ).denotation m ↔ w ∈ φ.denotation m := by
  grind [_=_ satisfies_mem_denotation]

/-- Two worlds are theory-equivalent iff they are denotationally equivalent. -/
theorem theoryEq_denotation_eq {m : Model World Atom} {w₁ w₂ : World} :
    (TheoryEq m w₁ w₂) ↔
    (∀ (φ : Proposition Atom), w₁ ∈ (φ.denotation m) ↔ w₂ ∈ (φ.denotation m)) := by
  apply Iff.intro <;> grind [_=_ satisfies_mem_denotation]

end Cslib.Logic.Modal
