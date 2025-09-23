/-
Copyright (c) 2025 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.SDiff

/-!
# Gentzen's NJ

Natural deduction for intuitionistic propositional logic.

## Main definitions

- `Proposition` : a type of propositions with atoms in a given type.
- `Derivation` :  natural deduction derivation, done in "sequent style", ie with explicit
hypotheses at each step. Contexts are `Finset`'s of propositions, which avoids explicit weakening
and exchange, and the axiom rule derives `{A} ∪ Γ ⊢ A` for any context `Γ`, allowing weakening to
be a derived rule.
- `Derivable` : defined as `Nonempty (Derivation S)`.
- `Proposition.equiv` and `Proposition.Equiv` : `Type`- and `Prop`-valued equivalence of
propositions.

## Main results

- `Derivation.weak` : weakening as a derived rule.
- `Derivation.subs` : substituting a derivation for a hypothesis.
- `equiv_equivalence` : equivalence of propositions is an equivalence.

## References

- Dag Prawitz, *Natural Deduction: a proof-theoretical study*.
- The sequent-style natural deduction I present here doesn't seem to be common, but it is tersely
presented in §10.4 of Troelstra & van Dalen's *Constructivism in Mathematics: an introduction*.
(Suggestions of better references welcome!)
-/

universe u

variable {Atom : Type u} [DecidableEq Atom]

namespace IPL

/-- Propositions. We view negation as a defined connective ~A := A → ⊥ -/
inductive Proposition (Atom : Type u) : Type u where
  /-- Propositional atoms -/
  | atom (x : Atom)
  /-- Falsum -/
  | bot
  /-- Conjunction -/
  | conj (a b : Proposition Atom)
  /-- Disjunction -/
  | disj (a b : Proposition Atom)
  /-- Implication -/
  | impl (a b : Proposition Atom)
deriving DecidableEq, BEq

namespace NJ

open Proposition

/-- Contexts are finsets of propositions. -/
abbrev Ctx (Atom) := Finset (Proposition Atom)

/-- Sequents {A₁, ..., Aₙ} ⊢ B. -/
abbrev Sequent (Atom) := Ctx Atom × Proposition Atom

/-- A derivation of {A₁, ..., Aₙ} ⊢ B demonstrates B using (undischarged) assumptions among Aᵢ. -/
inductive Derivation : Sequent Atom → Type _ where
  /-- Axiom (or assumption) -/
  | ax (Γ : Ctx Atom) (A : Proposition Atom) : Derivation ⟨insert A Γ, A⟩
  /-- Falsum elimination (ex falso quodlibet) -/
  | botE {Γ : Ctx Atom} (A : Proposition Atom) : Derivation ⟨Γ, bot⟩ → Derivation ⟨Γ, A⟩
  /-- Conjunction introduction -/
  | conjI {Γ : Ctx Atom} {A B : Proposition Atom} :
      Derivation ⟨Γ, A⟩ → Derivation ⟨Γ, B⟩ → Derivation ⟨Γ, conj A B⟩
  /-- Conjunction elimination left -/
  | conjE₁ {Γ : Ctx Atom} {A B : Proposition Atom} : Derivation ⟨Γ, conj A B⟩ → Derivation ⟨Γ, A⟩
  /-- Conjunction elimination right -/
  | conjE₂ {Γ : Ctx Atom} {A B : Proposition Atom} : Derivation ⟨Γ, conj A B⟩ → Derivation ⟨Γ, B⟩
  /-- Disjunction introduction left -/
  | disjI₁ {Γ : Ctx Atom} {A B : Proposition Atom} : Derivation ⟨Γ, A⟩ → Derivation ⟨Γ, disj A B⟩
  /-- Disjunction introduction right -/
  | disjI₂ {Γ : Ctx Atom} {A B : Proposition Atom} : Derivation ⟨Γ, B⟩ → Derivation ⟨Γ, disj A B⟩
  /-- Disjunction elimination -/
  | disjE {Γ : Ctx Atom} {A B C : Proposition Atom} : Derivation ⟨Γ, disj A B⟩ →
      Derivation ⟨insert A Γ, C⟩ → Derivation ⟨insert B Γ, C⟩ → Derivation ⟨Γ, C⟩
  /-- Implication introduction -/
  | implI {A B : Proposition Atom} (Γ : Ctx Atom) :
      Derivation ⟨insert A Γ, B⟩ → Derivation ⟨Γ, impl A B⟩
  /-- Implication elimination -/
  | implE {Γ : Ctx Atom} {A B : Proposition Atom} :
      Derivation ⟨Γ, impl A B⟩ → Derivation ⟨Γ, A⟩ → Derivation ⟨Γ, B⟩

/-- A sequent is derivable if it has a derivation. -/
def Derivable (S : Sequent Atom) := Nonempty (Derivation S)

/-- A proposition is derivable if it has a derivation from the empty context. -/
def Proposition.PDerivable (A : Proposition Atom) := Nonempty (Derivation ⟨∅,A⟩)

/-- An equivalence between A and B is a derivation of B from A and vice-versa. -/
def Proposition.equiv (A B : Proposition Atom) := Derivation ⟨{A},B⟩ × Derivation ⟨{B},A⟩

/-- Two propositions A and B are equivalent if B can be derived from A and vice-versa. -/
def Proposition.Equiv (A B : Proposition Atom) := Derivable ⟨{A},B⟩ ∧ Derivable ⟨{B},A⟩

open Derivation

/-- A fixed choice of a derivable proposition (of course any two are equivalent). -/
def Proposition.top : Proposition Atom := impl bot bot

def derivationTop : Derivation (Atom := Atom) ⟨∅,Proposition.top⟩ := by
  apply implI
  exact ax (Atom := Atom) ∅ bot

theorem top_derivable : Proposition.PDerivable (Atom := Atom) Proposition.top := ⟨derivationTop⟩

/-! ### Common proof patterns -/

/-- A convenient reformulation of the axiom rule. -/
def Derivation.ax' {Γ : Ctx Atom} {A : Proposition Atom} (h : A ∈ Γ) : Derivation ⟨Γ,A⟩ := by
  have : Γ = insert A Γ := by grind
  rw [this]
  apply ax

/-- Weakening is a derived rule. -/
def Derivation.weak {Γ : Ctx Atom} {A : Proposition Atom} (Δ : Ctx Atom)
    (D : Derivation ⟨Γ, A⟩) : Derivation ⟨Γ ∪ Δ, A⟩ := by
  match D with
  | ax Γ A =>
    rw [Finset.insert_union A Γ Δ]
    exact ax (Γ ∪ Δ) A
  | botE A D => exact botE A <| D.weak Δ
  | conjI D D' => exact conjI (D.weak Δ) (D'.weak Δ)
  | conjE₁ D => exact conjE₁ <| D.weak Δ
  | conjE₂ D => exact conjE₂ <| D.weak Δ
  | disjI₁ D => exact disjI₁ <| D.weak Δ
  | disjI₂ D => exact disjI₂ <| D.weak Δ
  | @disjE _ _ _ A B _ D D' D'' =>
    apply disjE (D.weak Δ)
    · rw [←Finset.insert_union A Γ Δ]; exact D'.weak Δ
    · rw [←Finset.insert_union B Γ Δ]; exact D''.weak Δ
  | @implI _ _ A B Γ D =>
    apply implI
    rw [←Finset.insert_union A Γ Δ]; exact D.weak Δ
  | implE D D' => exact implE (D.weak Δ) (D'.weak Δ)

theorem Derivable.weak {Γ : Ctx Atom} {A : Proposition Atom} (Δ : Ctx Atom)
    (h : Derivable ⟨Γ, A⟩) : Derivable ⟨Γ ∪ Δ, A⟩ := by
  let ⟨D⟩ := h
  exact ⟨D.weak Δ⟩

def Derivation.weak' {Γ Δ : Ctx Atom} {A : Proposition Atom} (h : Γ ⊆ Δ) (D : Derivation ⟨Γ, A⟩) :
    Derivation ⟨Δ, A⟩ := Finset.union_sdiff_of_subset h ▸ D.weak (Δ \ Γ)

theorem Derivable.weak' {Γ Δ : Ctx Atom} {A : Proposition Atom} (h_ext : Γ ⊆ Δ)
    (h : Derivable ⟨Γ, A⟩) : Derivable ⟨Δ, A⟩ := by
  let ⟨D⟩ := h
  exact ⟨D.weak' h_ext⟩

/-- Substitution of a derivation `E` for one of the hypotheses in the context `Gamma` of `D`. -/
def Derivation.subs {Γ Δ : Ctx Atom} {A B : Proposition Atom}
    (D : Derivation ⟨Γ, B⟩) (E : Derivation ⟨Δ, A⟩) : Derivation ⟨(Γ \ {A}) ∪ Δ, B⟩ := by
  match D with
  | ax _ _ =>
    by_cases B = A
    case pos h =>
      rw [h, Finset.union_comm]
      exact E.weak _
    case neg h =>
      have : B ∉ ({A} : Finset (Proposition Atom)) := Finset.notMem_singleton.mpr h
      rw [Finset.insert_sdiff_of_notMem (h := this)]
      exact (ax _ B).weak _
  | botE _ D => exact botE B <| D.subs E
  | conjI D D' => exact conjI (D.subs E) (D'.subs E)
  | conjE₁ D => exact conjE₁ <| D.subs E
  | conjE₂ D => exact conjE₂ <| D.subs E
  | disjI₁ D => exact disjI₁ <| D.subs E
  | disjI₂ D => exact disjI₂ <| D.subs E
  | @disjE _ _ _ C C' B D D' D'' =>
    apply disjE (D.subs E)
    · by_cases C = A
      case pos h =>
        rw [h] at D' ⊢
        have : insert A ((Γ \ {A}) ∪ Δ) = (insert A Γ) ∪ Δ := by grind
        rw [this]
        exact D'.weak _
      case neg h =>
        have : insert C ((Γ \ {A}) ∪ Δ) = ((insert C Γ) \ {A}) ∪ Δ := by grind
        rw [this]
        exact D'.subs E
    · by_cases C' = A
      case pos h =>
        rw [h] at D'' ⊢
        have : insert A ((Γ \ {A}) ∪ Δ) = (insert A Γ) ∪ Δ := by grind
        rw [this]
        exact D''.weak _
      case neg h =>
        have : insert C' ((Γ \ {A}) ∪ Δ) = ((insert C' Γ) \ {A}) ∪ Δ := by grind
        rw [this]
        exact D''.subs E
  | @implI _ _ A' B _ D =>
    apply implI
    by_cases A' = A
    case pos h =>
      rw [h] at D ⊢
      have : insert A (Γ \ {A} ∪ Δ) = insert A Γ ∪ Δ := by grind
      rw [this]
      exact D.weak Δ
    case neg h =>
      have : insert A' ((Γ \ {A}) ∪ Δ) = ((insert A' Γ) \ {A}) ∪ Δ := by grind
      rw [this]
      exact D.subs E
  | implE D D' => exact implE (D.subs E) (D'.subs E)

theorem Derivable.subs {Γ Δ : Ctx Atom} {A B : Proposition Atom}
    (h₁ : Derivable ⟨Γ, B⟩) (h₂ : Derivable ⟨Δ, A⟩) : Derivable ⟨(Γ \ {A}) ∪ Δ, B⟩ :=
  let ⟨D⟩ := h₁; let ⟨E⟩ := h₂; ⟨D.subs E⟩

def Derivation.subs' {Γ : Ctx Atom} {A B : Proposition Atom}
    (D : Derivation ⟨{A}, B⟩) (E : Derivation ⟨Γ, A⟩) : Derivation ⟨Γ, B⟩ := by
  have : Γ = ({A} \ {A}) ∪ Γ := by grind
  rw [this]
  exact D.subs E

theorem Derivable.subs' {Γ : Ctx Atom} {A B : Proposition Atom}
    (h : Derivable ⟨{A}, B⟩) (h' : Derivable ⟨Γ, A⟩) : Derivable ⟨Γ, B⟩ :=
  let ⟨D⟩ := h; let ⟨E⟩ := h'; ⟨D.subs' E⟩

/-! ### Properties of NJ-equivalence -/

theorem Proposition.derivable_iff_equiv_top (A : Proposition Atom) :
    PDerivable A ↔ Proposition.Equiv A top := by
  constructor <;> intro h
  · constructor
    · exact ⟨derivationTop.weak' (Δ := {A}) (by grind)⟩
    · let ⟨D⟩ := h
      exact ⟨D.weak' (Δ := {Proposition.top}) (by grind)⟩
  · let ⟨D⟩ := h.2
    exact ⟨D.subs' derivationTop⟩

/-- Change the conclusion along an equivalence. -/
def mapEquivConclusion (Γ : Ctx Atom) {A B : Proposition Atom} (e : Proposition.equiv A B) :
    Derivation ⟨Γ, A⟩ → Derivation ⟨Γ, B⟩ := e.1.subs'

theorem equivalent_derivability (Γ : Ctx Atom) {A B : Proposition Atom} (h : Proposition.Equiv A B)
    : Derivable ⟨Γ, A⟩ ↔ Derivable ⟨Γ, B⟩ := ⟨h.1.subs', h.2.subs'⟩

/-- Replace a hypothesis along an equivalence. -/
def mapEquivHypothesis (Γ : Ctx Atom) {A B : Proposition Atom} (e : Proposition.equiv A B)
    (C : Proposition Atom) (D : Derivation ⟨insert A Γ, C⟩) : Derivation ⟨insert B Γ, C⟩ := by
  have : insert B Γ = (insert A Γ \ {A}) ∪ (insert B Γ) := by grind
  rw [this]
  refine D.subs ?_
  exact e.2.weak' (by grind)

theorem equivalent_hypotheses (Γ : Ctx Atom) {A B : Proposition Atom} (h : Proposition.Equiv A B)
    (C : Proposition Atom) : Derivable ⟨insert A Γ, C⟩ ↔ Derivable ⟨insert B Γ, C⟩ := by
  let ⟨⟨D⟩, ⟨D'⟩⟩ := h
  constructor
  · intro ⟨DA⟩
    have : insert B Γ = (insert A Γ \ {A}) ∪ (insert B Γ) := by grind
    rw [this]
    refine ⟨DA.subs ?_⟩
    exact D'.weak' (by grind)
  · intro ⟨DB⟩
    have : insert A Γ = (insert B Γ \ {B}) ∪ (insert A Γ) := by grind
    rw [this]
    refine ⟨DB.subs ?_⟩
    exact D.weak' (by grind)

def reflEquiv (A : Proposition Atom) : Proposition.equiv A A :=
  let D : Derivation ⟨{A},A⟩ := ax' <| by grind;
  ⟨D,D⟩

def commEquiv {A B : Proposition Atom} (e : Proposition.equiv A B) : Proposition.equiv B A :=
  ⟨e.2, e.1⟩

def transEquiv {A B C : Proposition Atom} (e : Proposition.Equiv A B) (e' : Proposition.Equiv B C) :
    Proposition.Equiv A C := ⟨e'.1.subs' e.1, e.2.subs' e'.2⟩

theorem equivalent_refl (A : Proposition Atom) : Proposition.Equiv A A := by
  have : Derivable ⟨{A},A⟩ := ⟨ax' <| by grind⟩
  grind [Proposition.Equiv]

theorem equivalent_comm {A B : Proposition Atom} :
    Proposition.Equiv A B → Proposition.Equiv B A := by grind [Proposition.Equiv]

theorem equivalent_trans {A B C : Proposition Atom} :
    Proposition.Equiv A B → Proposition.Equiv B C → Proposition.Equiv A C := by
  grind [Proposition.Equiv, Derivable.subs']

/-- Equivalence is indeed an equivalence relation. -/
theorem equiv_equivalence : Equivalence (Proposition.Equiv (Atom := Atom)) :=
  ⟨equivalent_refl, equivalent_comm, equivalent_trans⟩

protected def propositionSetoid : Setoid (Proposition Atom) :=
  ⟨Proposition.Equiv, equiv_equivalence⟩

end NJ

end IPL
