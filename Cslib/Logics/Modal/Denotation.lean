/-
Copyright (c) 2026 Fabrizio Montesi, Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Benjamin Brast-McKie
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
  | .bot => ∅
  | .imp φ₁ φ₂ => (φ₁.denotation m)ᶜ ∪ φ₂.denotation m
  | .box φ => {w | ∀ w', m.r w w' → w' ∈ φ.denotation m}

/-- Characterisation theorem for the denotational semantics. -/
@[scoped grind =]
theorem satisfies_mem_denotation {m : Model World Atom} {φ : Proposition Atom} :
    w ∈ φ.denotation m ↔ ⇓Modal[m,w ⊨ φ] := by
  induction φ generalizing w with
  | atom p => simp [Proposition.denotation, derivation_def, Satisfies]
  | bot => simp [Proposition.denotation, derivation_def, Satisfies]
  | imp φ₁ φ₂ ih₁ ih₂ =>
    simp only [Proposition.denotation, Set.mem_union, Set.mem_compl_iff, derivation_def, Satisfies]
    constructor
    · intro h hs₁
      rcases h with h | h
      · exact absurd (ih₁.mpr hs₁) h
      · exact ih₂.mp h
    · intro h
      by_cases hs : w ∈ φ₁.denotation m
      · exact Or.inr (ih₂.mpr (h (ih₁.mp hs)))
      · exact Or.inl hs
  | box φ ih =>
    simp only [Proposition.denotation, Set.mem_setOf_eq, derivation_def, Satisfies]
    exact ⟨fun h w' hr => ih.mp (h w' hr), fun h w' hr => ih.mpr (h w' hr)⟩

/-- A world is in the denotation of a proposition iff it is not in the denotation of the negation
of the proposition. -/
@[scoped grind =]
theorem neg_denotation {m : Model World Atom} (φ : Proposition Atom) :
    w ∉ (¬φ).denotation m ↔ w ∈ φ.denotation m := by
  simp only [Proposition.denotation, Set.mem_union, Set.mem_compl_iff]
  constructor
  · intro h
    push Not at h
    exact h.1
  · intro h hc
    rcases hc with hc | hc
    · exact hc h
    · simp at hc

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
