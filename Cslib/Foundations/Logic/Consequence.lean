/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

module

public import Cslib.Foundations.Syntax.Context
public import Cslib.Foundations.Logic.InferenceSystem

/-! # Semantic consequence

Semantic consequence and validity for inference systems whose judgements pair a model with a
proposition. The model is captured as a judgemental context (`HasHContext Judgement α`): a
judgement with the proposition missing. A proposition is a consequence of a set of premises when
every context deriving all the premises derives it, and it is valid when every context derives it.
Both notions can be restricted to a class of contexts, which is how consequence over the two-valued
valuations of a many-valued logic, or over a frame class in modal logic, arises.

Derivations are required to be propositions (`InferenceSystem.{_, _, 0}`), as they are for
satisfaction judgements. Proof systems whose derivations are data are not covered.

## Main definitions

- `Cslib.Logic.EntailsWithin`: consequence over a class of judgemental contexts.
- `Cslib.Logic.Entails`: consequence over all judgemental contexts.
- `Cslib.Logic.ValidWithin`: validity over a class of judgemental contexts.
- `Cslib.Logic.Valid`: validity, that is, derivability in every judgemental context.

## Main results

- `Cslib.Logic.validWithin_iff_entailsWithin_empty`: validity is consequence from no premises.
- `Cslib.Logic.EntailsWithin.mono` and `Cslib.Logic.EntailsWithin.trans`: weakening and cut.
- `Cslib.Logic.EntailsWithin.anti`: consequence over a class of contexts is consequence over any
  subclass.
- `Cslib.Logic.entailsWithin_of_incompatible`: incompatible premises entail everything.
-/

@[expose] public section

namespace Cslib.Logic

open scoped InferenceSystem

variable (J : Type*) {α : Type*} (S : Type*) [HasHContext J α] [InferenceSystem.{_, _, 0} S J]

/-- Consequence over a class `C` of judgemental contexts: every context in `C` deriving all the
premises in `Γ` derives `φ`. -/
def EntailsWithin (C : Set (HasHContext.Context J α)) (Γ : Set α) (φ : α) : Prop :=
  ∀ c ∈ C, (∀ ψ ∈ Γ, S⇓(c<[ψ])) → S⇓(c<[φ])

/-- Consequence over all judgemental contexts. -/
abbrev Entails (Γ : Set α) (φ : α) : Prop := EntailsWithin J S Set.univ Γ φ

/-- Validity over a class `C` of judgemental contexts: every context in `C` derives `φ`. -/
def ValidWithin (C : Set (HasHContext.Context J α)) (φ : α) : Prop := ∀ c ∈ C, S⇓(c<[φ])

/-- Validity: derivable in every judgemental context. -/
abbrev Valid (φ : α) : Prop := ValidWithin J S Set.univ φ

variable {J S}

/-- Validity over a class of contexts is consequence from no premises over that class. -/
theorem validWithin_iff_entailsWithin_empty {C : Set (HasHContext.Context J α)} {φ : α} :
    ValidWithin J S C φ ↔ EntailsWithin J S C ∅ φ :=
  ⟨fun h c hc _ => h c hc, fun h c hc => h c hc fun _ h => h.elim⟩

/-- Validity is consequence from no premises. -/
theorem valid_iff_entails_empty {φ : α} : Valid J S φ ↔ Entails J S ∅ φ :=
  validWithin_iff_entailsWithin_empty

/-- Every premise is a consequence. -/
theorem entailsWithin_of_mem {C : Set (HasHContext.Context J α)} {Γ : Set α} {φ : α}
    (h : φ ∈ Γ) : EntailsWithin J S C Γ φ :=
  fun _ _ hΓ => hΓ _ h

/-- Weakening: consequence is preserved by adding premises. -/
theorem EntailsWithin.mono {C : Set (HasHContext.Context J α)} {Γ Δ : Set α} {φ : α}
    (hΓ : EntailsWithin J S C Γ φ) (h : Γ ⊆ Δ) : EntailsWithin J S C Δ φ :=
  fun c hc hv => hΓ c hc fun ψ hψ => hv ψ (h hψ)

/-- Cut: if every premise in `Δ` is a consequence of `Γ`, so is every consequence of `Δ`. -/
theorem EntailsWithin.trans {C : Set (HasHContext.Context J α)} {Γ Δ : Set α} {φ : α}
    (h₁ : ∀ ψ ∈ Δ, EntailsWithin J S C Γ ψ) (h₂ : EntailsWithin J S C Δ φ) :
    EntailsWithin J S C Γ φ :=
  fun c hc hv => h₂ c hc fun ψ hψ => h₁ ψ hψ c hc hv

/-- Consequence over a class of contexts is consequence over any subclass. -/
theorem EntailsWithin.anti {C D : Set (HasHContext.Context J α)} {Γ : Set α} {φ : α}
    (h : EntailsWithin J S D Γ φ) (hCD : C ⊆ D) : EntailsWithin J S C Γ φ :=
  fun c hc => h c (hCD hc)

/-- Incompatible premises entail everything: if `φ` and `ψ` are premises and no context in `C`
derives both, then every proposition is a consequence over `C`. -/
theorem entailsWithin_of_incompatible {C : Set (HasHContext.Context J α)} {Γ : Set α} {φ ψ : α}
    (h₁ : φ ∈ Γ) (h₂ : ψ ∈ Γ) (h : ∀ c ∈ C, S⇓(c<[φ]) → ¬S⇓(c<[ψ])) (χ : α) :
    EntailsWithin J S C Γ χ :=
  fun _ hc hΓ => absurd (hΓ _ h₂) (h _ hc (hΓ _ h₁))

end Cslib.Logic
