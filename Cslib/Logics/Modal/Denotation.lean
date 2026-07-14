/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Logics.Modal.Basic
public import Mathlib.Data.Set.Basic

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
  | .bot => ∅
  | .imp φ₁ φ₂ => (φ₁.denotation m)ᶜ ∪ φ₂.denotation m
  | .and φ₁ φ₂ => φ₁.denotation m ∩ φ₂.denotation m
  | .or φ₁ φ₂ => φ₁.denotation m ∪ φ₂.denotation m
  | .box φ => {w | ∀ w', m.r w w' → w' ∈ φ.denotation m}
  | .diamond φ => {w | ∃ w', m.r w w' ∧ w' ∈ φ.denotation m}

/-- Characterisation theorem for the denotational semantics. -/
@[scoped grind =]
theorem satisfies_mem_denotation {m : Model World Atom} {φ : Proposition Atom} :
    w ∈ φ.denotation m ↔ ⇓Modal[m,w ⊨ φ] := by
  induction φ generalizing w with
  | atom p => simp [Proposition.denotation, ← derivation_def, Satisfies]
  | bot => simp [Proposition.denotation, ← derivation_def, Satisfies]
  | imp φ₁ φ₂ ih₁ ih₂ =>
    simp only [Proposition.denotation, Set.mem_union, Set.mem_compl_iff, ← derivation_def,
      Satisfies]
    constructor
    · intro h hs₁
      rcases h with h | h
      · exact absurd (ih₁.mpr hs₁) h
      · exact ih₂.mp h
    · intro h
      by_cases hs : w ∈ φ₁.denotation m
      · exact Or.inr (ih₂.mpr (h (ih₁.mp hs)))
      · exact Or.inl hs
  | and φ₁ φ₂ ih₁ ih₂ =>
    simp only [Proposition.denotation, Set.mem_inter_iff, ← derivation_def, Satisfies]
    exact ⟨fun ⟨h1, h2⟩ => ⟨ih₁.mp h1, ih₂.mp h2⟩, fun ⟨h1, h2⟩ => ⟨ih₁.mpr h1, ih₂.mpr h2⟩⟩
  | or φ₁ φ₂ ih₁ ih₂ =>
    simp only [Proposition.denotation, Set.mem_union, ← derivation_def, Satisfies]
    exact ⟨fun h => h.imp ih₁.mp ih₂.mp, fun h => h.imp ih₁.mpr ih₂.mpr⟩
  | box φ ih =>
    simp only [Proposition.denotation, Set.mem_setOf_eq, ← derivation_def, Satisfies]
    exact ⟨fun h w' hr => ih.mp (h w' hr), fun h w' hr => ih.mpr (h w' hr)⟩
  | diamond φ ih =>
    simp only [Proposition.denotation, Set.mem_setOf_eq, ← derivation_def, Satisfies]
    exact ⟨fun ⟨w', hr, hs⟩ => ⟨w', hr, ih.mp hs⟩, fun ⟨w', hr, hs⟩ => ⟨w', hr, ih.mpr hs⟩⟩

/-- A world is in the denotation of a proposition iff it is not in the denotation of the negation
of the proposition. -/
@[scoped grind =]
theorem not_denotation {m : Model World Atom} (φ : Proposition Atom) :
    w ∉ (¬φ).denotation m ↔ w ∈ φ.denotation m := by
  simp [Proposition.neg_def, Proposition.denotation]

/-- Two worlds are theory-equivalent iff they are denotationally equivalent. -/
theorem theoryEq_denotation_eq {m : Model World Atom} {w₁ w₂ : World} :
    (TheoryEq m w₁ w₂) ↔
    (∀ (φ : Proposition Atom), w₁ ∈ (φ.denotation m) ↔ w₂ ∈ (φ.denotation m)) := by
  constructor
  · intro h φ
    have hext := TheoryEq.ext_iff.mp h φ
    exact ⟨fun h₁ => satisfies_mem_denotation.mpr (hext.mp (satisfies_mem_denotation.mp h₁)),
           fun h₂ => satisfies_mem_denotation.mpr (hext.mpr (satisfies_mem_denotation.mp h₂))⟩
  · intro h
    apply TheoryEq.ext_iff.mpr
    intro φ
    have hd := h φ
    exact ⟨fun h₁ => satisfies_mem_denotation.mp (hd.mp (satisfies_mem_denotation.mpr h₁)),
           fun h₂ => satisfies_mem_denotation.mp (hd.mpr (satisfies_mem_denotation.mpr h₂))⟩

end Cslib.Logic.Modal
