/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Cslib.Logics.BTL.Basic

namespace CslibTests.BTL

open Cslib Logic Modal BTL
open scoped InferenceSystem Satisfies

-- The timeline is 0 → 1 → 2, with the atom true only at 1.
private def timeline : BTL.Model Nat Unit where
  r w w' := w + 1 = w' ∧ w' < 3
  v w _ := w = 1

example : ⇓BTL[timeline,0 ⊨ F (() : Unit)] := by
  rw [Satisfies.btl_future_iff_exists]
  exact ⟨1, by simp [timeline], rfl⟩

example : ⇓BTL[timeline,2 ⊨ P (() : Unit)] := by
  rw [Satisfies.btl_past_iff_exists]
  exact ⟨1, by simp [timeline], rfl⟩

example : ⇓BTL[timeline,0 ⊨ G (() : Unit)] := by
  rw [Satisfies.btl_always_iff_forall]
  intro w hw
  exact hw.1.symm

example : ⇓BTL[timeline,2 ⊨ H (() : Unit)] := by
  rw [Satisfies.btl_hasAlwaysBeen_iff_forall]
  intro w hw
  change w = 1
  have := hw.1
  grind

-- Endpoint boxes are vacuous, and endpoint diamonds are false.
example : ⇓BTL[timeline,0 ⊨ H ⊥] := by
  rw [Satisfies.btl_hasAlwaysBeen_iff_forall]
  intro w hw
  have := hw.1
  grind

example : ⇓BTL[timeline,2 ⊨ ¬F ⊤] := by
  rw [Satisfies.not_iff_not, Satisfies.btl_future_iff_exists]
  rintro ⟨w, hw, _⟩
  obtain ⟨h₁, h₂⟩ := hw
  grind

-- The present is not implicitly included.
example : ⇓BTL[timeline,1 ⊨ ¬F (() : Unit) ∧ ¬P (() : Unit)] := by
  simp only [Satisfies.and_iff_and, Satisfies.not_iff_not,
    Satisfies.btl_future_iff_exists, Satisfies.btl_past_iff_exists, Satisfies.btl_atom_iff]
  change (¬∃ w, (1 + 1 = w ∧ w < 3) ∧ w = 1) ∧
    (¬∃ w, (w + 1 = 1 ∧ 1 < 3) ∧ w = 1)
  grind

-- The relation is not implicitly closed under transitivity.
example : ⇓BTL[timeline,0 ⊨ F F ⊤ ∧ ¬F ¬(() : Unit)] := by
  rw [Satisfies.and_iff_and]
  constructor
  · apply Satisfies.btl_future_intro (w' := 1) (by simp [timeline])
    apply Satisfies.btl_future_intro (w' := 2) (by simp [timeline])
    exact Satisfies.true
  · rw [Satisfies.not_iff_not, Satisfies.btl_future_iff_exists]
    rintro ⟨w, hw, h⟩
    exact h hw.1.symm

-- Temporal propositions support the existing modal automation and equivalence API.
example (m : BTL.Model World Atom) (hr : m.r w w') (φ : BTL.Proposition Atom)
    (h : ⇓BTL[m,w' ⊨ φ]) : ⇓BTL[m,w ⊨ F φ] := by
  rw [Satisfies.btl_future_iff_exists]
  exact ⟨w', hr, h⟩

example (m : BTL.Model World Atom) (φ : BTL.Proposition Atom) :
    G φ ≡[Modal.Proposition.Equiv m.toModal] ¬F ¬φ := by
  rw [Modal.Proposition.equiv_iff_forall_iff, BTL.Proposition.always_eq_not_future_not]
  intro w
  rfl

end CslibTests.BTL
