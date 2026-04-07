/-
Copyright (c) 2025 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/
module

public import Cslib.Logics.Propositional.Defs
public import Cslib.Foundations.Logic.InferenceSystem
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Finset.SDiff
public import Mathlib.Data.Finset.Image

@[expose] public section

/-! # Natural deduction for propositional logic

We define, for minimal logic, deduction trees (a `Type`) and derivability (a `Prop`) relative to a
`Theory` (set of propositions).

## Main definitions

- `Theory.Derivation` :  natural deduction derivation, done in "sequent style", ie with explicit
hypotheses at each step. Contexts are `Finset`'s of propositions, which avoids explicit contraction
and exchange, and the axiom rule derives `{A} ∪ Γ ⊢ A` for any context `Γ`, allowing weakening to
be a derived rule.
- `Theory.PDerivable`, `Theory.SDerivable` : a proposition `A` (resp sequent `S`) is derivable if
it has a derivation.
- `Theory.equiv` : `Type`-valued equivalence of propositions.
- `Theory.Equiv` : `Prop`-valued equivalence of propositions.
- The unconditional versions `Derivable`, `SDerivable` and `Equiv` are abbreviations for the
relevant concept relative to the empty theory `MPL`.

## Main results

- `Derivation.weak` : weakening as a derived rule.
- `Derivation.cut`, `Derivation.subs` : replace a hypothesis in a derivation — the two versions
differ in the construction of the relevant derivation.
- `Theory.equiv_equivalence` : equivalence of propositions is an equivalence relation.

## Notation

For `T`-derivability, -sequent-derivability and -equivalence we introduce the notations `⊢[T] A`,
`Γ ⊢[T] A` and `A ≡[T] B`, respectively.

## References

- Dag Prawitz, *Natural Deduction: a proof-theoretical study*.
- The sequent-style natural deduction I present here doesn't seem to be common, but it is tersely
presented in §10.4 of Troelstra & van Dalen's *Constructivism in Mathematics: an introduction*, and
in §2.2 of Sorensen & Urzyczyn's *Lectures on the Curry-Howard Isomorphism*. (Suggestions of better
references welcome!)
-/

universe u

namespace Cslib.Logic.PL

open Proposition Theory InferenceSystem Derivable

variable {Atom : Type u} [DecidableEq Atom]-- {T : Theory Atom}

/-- Contexts are finsets of propositions. -/
abbrev Ctx (Atom) := Finset (Proposition Atom)

/-- Map a context along a change of `Atom`. -/
def Ctx.map {Atom Atom' : Type u} [DecidableEq Atom'] (f : Atom → Atom') :
    Ctx Atom → Ctx Atom' := Finset.image (Proposition.map f)

/-- Sequents {A₁, ..., Aₙ} ⊢ B. -/
abbrev Sequent {Atom} := Theory Atom × Ctx Atom × Proposition Atom

scoped notation Γ:60 " ⊢[" T "] " A => (⟨T, Γ, A⟩ : Sequent)

abbrev Sequent₁ {Atom} := Theory Atom × Proposition Atom

scoped notation "⊢[" T "] " A => (⟨T, A⟩ : Sequent₁)

/-- A `T`-derivation of {A₁, ..., Aₙ} ⊢ B demonstrates B using (undischarged) assumptions among Aᵢ,
possibly appealing to axioms from `T`. -/
inductive Derivation : Sequent → Type _ where
  /-- Axiom -/
  | ax {Γ : Ctx Atom} {A : Proposition Atom} (_ : A ∈ T) : Derivation ⟨T, Γ, A⟩
  /-- Assumption -/
  | ass {Γ : Ctx Atom} {A : Proposition Atom} (_ : A ∈ Γ) : Derivation ⟨T, Γ, A⟩
  /-- Conjunction introduction -/
  | conjI {Γ : Ctx Atom} {A B : Proposition Atom} :
      Derivation ⟨T, Γ, A⟩ → Derivation ⟨T, Γ, B⟩ → Derivation ⟨T, Γ, A ∧ B⟩
  /-- Conjunction elimination left -/
  | conjE₁ {Γ : Ctx Atom} {A B : Proposition Atom} : Derivation ⟨T, Γ, A ∧ B⟩ → Derivation ⟨T, Γ, A⟩
  /-- Conjunction elimination right -/
  | conjE₂ {Γ : Ctx Atom} {A B : Proposition Atom} : Derivation ⟨T, Γ, A ∧ B⟩ → Derivation ⟨T, Γ, B⟩
  /-- Disjunction introduction left -/
  | disjI₁ {Γ : Ctx Atom} {A B : Proposition Atom} : Derivation ⟨T, Γ, A⟩ → Derivation ⟨T, Γ, A ∨ B⟩
  /-- Disjunction introduction right -/
  | disjI₂ {Γ : Ctx Atom} {A B : Proposition Atom} : Derivation ⟨T, Γ, B⟩ → Derivation ⟨T, Γ, A ∨ B⟩
  /-- Disjunction elimination -/
  | disjE {Γ : Ctx Atom} {A B C : Proposition Atom} : Derivation ⟨T, Γ, A ∨ B⟩ →
      Derivation ⟨T, insert A Γ, C⟩ → Derivation ⟨T, insert B Γ, C⟩ → Derivation ⟨T, Γ, C⟩
  /-- Implication introduction -/
  | implI {A B : Proposition Atom} (Γ : Ctx Atom) :
      Derivation ⟨T, insert A Γ, B⟩ → Derivation ⟨T, Γ, A → B⟩
  /-- Implication elimination -/
  | implE {Γ : Ctx Atom} {A B : Proposition Atom} :
      Derivation ⟨T, Γ, A → B⟩ → Derivation ⟨T, Γ, A⟩ → Derivation ⟨T, Γ, B⟩

instance : InferenceSystem (Sequent (Atom := Atom)) where
  derivation := Derivation

instance : InferenceSystem (Sequent₁ (Atom := Atom)) where
  derivation S₁ := Derivation ⟨S₁.1, ∅, S₁.2⟩

variable {T : Theory Atom}

theorem Derivable.iff_derivable_empty {A : Proposition Atom} :
    Derivable (⊢[T] A) ↔ Derivable (∅ ⊢[T] A) := by rfl

/-- An equivalence between A and B is a derivation of B from A and vice-versa. -/
def Theory.equiv (A B : Proposition Atom) :=
  ⇓({A} ⊢[T] B) × ⇓({B} ⊢[T] A)

def Theory.equiv.mp {A B : Proposition Atom} (e : T.equiv A B) : (⇓({A} ⊢[T] B)) := e.1

def Theory.equiv.mpr {A B : Proposition Atom} (e : T.equiv A B) : (⇓({B} ⊢[T] A)) := e.2

/-- `A` and `B` are T-equivalent if `T.equiv A B` is nonempty. -/
def Theory.Equiv (A B : Proposition Atom) := Nonempty (T.equiv A B)

@[inherit_doc]
scoped notation A " ≡[" T' "] " B:29 => Theory.Equiv (T := T') A B

lemma Theory.Equiv.mp {A B : Proposition Atom} (h : A ≡[T] B) : Derivable ({A} ⊢[T] B) :=
  let ⟨D, _⟩ := h; ⟨D⟩

lemma Theory.Equiv.mpr {A B : Proposition Atom} (h : A ≡[T] B) : Derivable ({B} ⊢[T] A) :=
  let ⟨_,D⟩ := h; ⟨D⟩

theorem Theory.equiv_iff {A B : Proposition Atom} :
  A ≡[T] B ↔ Derivable ({A} ⊢[T] B) ∧ Derivable ({B} ⊢[T] A) := by
  constructor
  · intro h
    exact ⟨h.mp, h.mpr⟩
  · intro ⟨⟨D⟩,⟨E⟩⟩
    exact ⟨D,E⟩

/-- Minimally equivalent propositions. -/
abbrev Equiv : Proposition Atom → Proposition Atom → Prop := MPL.Equiv

@[inherit_doc]
scoped infix:29 " ≡ " => Equiv

open Derivation

/-! ### Operations on derivations -/

/-- Weakening is a derived rule. -/
def Derivation.weak {T T' : Theory Atom} {Γ Δ : Ctx Atom} {A : Proposition Atom}
    (hTheory : T ⊆ T') (hCtx : Γ ⊆ Δ) : Derivation (Γ ⊢[T] A) → Derivation (Δ ⊢[T'] A)
  | ax hA => ax <| hTheory hA
  | ass hA => ass <| hCtx hA
  | conjI D D' => conjI (D.weak hTheory hCtx) (D'.weak hTheory hCtx)
  | conjE₁ D => conjE₁ <| D.weak hTheory hCtx
  | conjE₂ D => conjE₂ <| D.weak hTheory hCtx
  | disjI₁ D => disjI₁ <| D.weak hTheory hCtx
  | disjI₂ D => disjI₂ <| D.weak hTheory hCtx
  | @disjE _ _ _ _ A B _ D D' D'' =>
    disjE (D.weak hTheory hCtx)
      (D'.weak hTheory <| Finset.insert_subset_insert _ hCtx)
      (D''.weak hTheory <| Finset.insert_subset_insert _ hCtx)
  | @implI _ _ _ A B Γ D => implI (Δ) <| D.weak hTheory <| Finset.insert_subset_insert _ hCtx
  | implE D D' => implE (D.weak hTheory hCtx) (D'.weak hTheory hCtx)

/-- Weakening the theory only. -/
def Derivation.weak_theory {T T' : Theory Atom} {Γ : Ctx Atom} {A : Proposition Atom}
    (hTheory : T ⊆ T') : ⇓(Γ ⊢[T] A) → ⇓(Γ ⊢[T'] A):=
  Derivation.weak hTheory Finset.Subset.rfl

/-- Weakening the context only. -/
def Derivation.weak_ctx {T : Theory Atom} {Γ Δ : Ctx Atom} {A : Proposition Atom}
    (hCtx : Γ ⊆ Δ) : ⇓(Γ ⊢[T] A) → ⇓(Δ ⊢[T] A) :=
  Derivation.weak Set.Subset.rfl hCtx

/-- Proof irrelevant weakening. -/
theorem Derivable.weak {T T' : Theory Atom} {Γ Δ : Ctx Atom} {A : Proposition Atom}
    (hTheory : T ⊆ T') (hCtx : Γ ⊆ Δ) : Derivable (Γ ⊢[T] A) → Derivable (Δ ⊢[T'] A)
  | ⟨D⟩ => ⟨D.weak hTheory hCtx⟩

/-- Proof irrelevant weakening of the theory. -/
theorem Derivable.weak_theory {T T' : Theory Atom} {Γ : Ctx Atom} {A : Proposition Atom}
    (hTheory : T ⊆ T') : Derivable (Γ ⊢[T] A) → Derivable (Γ ⊢[T'] A)
  | ⟨D⟩ => ⟨D.weak_theory hTheory⟩

/-- Proof irrelevant weakening of the context. -/
theorem Derivable.weak_ctx {T : Theory Atom} {Γ Δ : Ctx Atom} {A : Proposition Atom}
    (hCtx : Γ ⊆ Δ) : Derivable (Γ ⊢[T] A) → Derivable (Δ ⊢[T] A)
  | ⟨D⟩ => ⟨D.weak_ctx hCtx⟩

/--
Implement the cut rule, removing a hypothesis `A` from `E` using a derivation `D`. This is *not*
substitution, which would replace appeals to `A` in `E` by the whole derivation `D`.
-/
def Derivation.cut {Γ Δ : Ctx Atom} {A B : Proposition Atom}
    (D : ⇓(Γ ⊢[T] A)) (E : ⇓(insert A Δ ⊢[T] B)) : ⇓((Γ ∪ Δ) ⊢[T] B) := by
  refine implE ?_ (D.weak_ctx Finset.subset_union_left)
  have : insert A Δ ⊆ insert A (Γ ∪ Δ) := by grind
  exact implI (Γ ∪ Δ) <| E.weak_ctx this

/-- Proof irrelevant cut rule. -/
theorem Derivable.cut {Γ Δ : Ctx Atom} {A B : Proposition Atom} :
    Derivable (Γ ⊢[T] A) → Derivable ((insert A Δ) ⊢[T] B) → Derivable ((Γ ∪ Δ) ⊢[T] B)
  | ⟨D⟩, ⟨E⟩ => ⟨D.cut E⟩

/-- Remove unnecessary hypotheses. This can't be computable because it requires picking an order
on the finset `Δ`. -/
theorem Theory.SDerivable.cut_away {Γ Δ : Ctx Atom} {B : Proposition Atom}
    (hΔ : ∀ A ∈ Δ, Derivable (Γ ⊢[T] A)) (hDer : Derivable ((Γ ∪ Δ) ⊢[T] B)) :
    Derivable (Γ ⊢[T] B) := by
  induction Δ using Finset.induction with
  | empty => exact Derivable.weak_ctx (by grind) hDer
  | insert A Δ hA ih =>
    apply ih
    · intro A' hA'
      exact hΔ A' <| Finset.mem_insert_of_mem hA'
    · apply Finset.union_left_idem Γ Δ ▸ Derivable.cut (Δ := Γ ∪ Δ)
      · exact hΔ A <| Finset.mem_insert_self A Δ
      · rwa [← Finset.union_insert A Γ Δ]

/-- Substitution of a derivation `D` for one of the hypotheses in the context `Δ` of `E`. -/
def Derivation.subs {Γ Δ : Ctx Atom} {A B : Proposition Atom}
    (D : Derivation (Γ ⊢[T] A)) (E : Derivation (Δ ⊢[T] B)) : ⇓((Γ ∪ (Δ \ {A})) ⊢[T] B) := by
  match E with
  | ax hB => exact ax hB
  | ass hB =>
    by_cases A = B
    case pos h =>
      rw [←h]
      apply D.weak_ctx (Δ := Γ ∪ (Δ \ {A})) <| by grind
    case neg h =>
      exact ass <| by grind
  | conjI E E' => exact conjI (D.subs E) (D.subs E')
  | conjE₁ E => exact conjE₁ <| D.subs E
  | conjE₂ E => exact conjE₂ <| D.subs E
  | disjI₁ E => exact disjI₁ <| D.subs E
  | disjI₂ E => exact disjI₂ <| D.subs E
  | @disjE _ _ _ _ C C' _ E E' E'' .. =>
    apply disjE (D.subs E)
    · by_cases C = A
      case pos h =>
        rw [h] at E' ⊢
        exact E'.weak_ctx <| by grind
      case neg h =>
        have : insert C (Γ ∪ (Δ \ {A})) = Γ ∪ (insert C Δ \ {A}) := by grind
        rw [this]
        exact D.subs E'
    · by_cases C' = A
      case pos h =>
        rw [h] at E'' ⊢
        exact E''.weak_ctx <| by grind
      case neg h =>
        have : insert C' (Γ ∪ (Δ \ {A})) = Γ ∪ (insert C' Δ \ {A}) := by grind
        rw [this]
        exact D.subs E''
  | @implI _ _ _ A' _ _ E .. =>
    apply implI
    by_cases A' = A
    case pos h =>
      rw [h] at E ⊢
      have : insert A (Γ ∪ Δ \ {A}) = Γ ∪ insert A Δ := by grind
      rw [this]
      apply E.weak_ctx <| by grind
    case neg h =>
      have : insert A' (Γ ∪ Δ \ {A}) = Γ ∪ (insert A' Δ \ {A}) := by grind
      rw [this]
      exact D.subs E
  | implE E E' => exact implE (D.subs E) (D.subs E')

/-- Transport a derivation along a map of atoms. -/
def Derivation.map {Atom Atom' : Type u} [DecidableEq Atom] [DecidableEq Atom']
    {T : Theory Atom} (f : Atom → Atom') {Γ : Ctx Atom} {B : Proposition Atom} :
    Derivation (Γ ⊢[T] B) → Derivation (Γ.map f ⊢[f <$> T] f <$> B)
  | ax h => ax <| Set.mem_image_of_mem (Proposition.map f) h
  | ass h => ass <| Finset.mem_image_of_mem (Proposition.map f) h
  | conjI D E => conjI (D.map f) (E.map f)
  | conjE₁ D => conjE₁ (D.map f)
  | conjE₂ D => conjE₂ (D.map f)
  | disjI₁ D => disjI₁ (D.map f)
  | disjI₂ D => disjI₂ (D.map f)
  | disjE D E E' => disjE (D.map f)
    ((Finset.image_insert (Proposition.map f) _ _) ▸ E.map f)
    ((Finset.image_insert (Proposition.map f) _ _) ▸ E'.map f)
  | implI _ D => implI _ <| (Finset.image_insert (Proposition.map f) _ _) ▸ (D.map f)
  | implE D E => implE (D.map f) (E.map f)

theorem Theory.Derivable.map {Atom' : Type u} [DecidableEq Atom'] {T : Theory Atom}
    (f : Atom → Atom') {Γ : Ctx Atom} {B : Proposition Atom} :
    Derivable (Γ ⊢[T] B) → Derivable ((Γ.map f) ⊢[f <$> T] (f <$> B))
  | ⟨D⟩ => ⟨D.map f⟩

/-! ### Properties of equivalence -/

/-- A derivation of the canonical tautology. -/
def derivationTop [Inhabited Atom] : ⇓(⊢[T] ⊤) :=
  implI ∅ <| ass <| by grind

theorem derivable_top [Inhabited Atom] : Derivable (⊢[T] ⊤) := ⟨derivationTop⟩

theorem derivable_iff_equiv_top [Inhabited Atom] (A : Proposition Atom) :
    Derivable (⊢[T] A) ↔ A ≡[T] ⊤ := by
  constructor <;> intro h
  · refine ⟨derivationTop.weak_ctx <| by grind, ?_⟩
    let D := Classical.choice h
    exact D.weak_ctx <| by grind
  · have := Derivable.cut (derivable_top (T := T)) (B := A) (Δ := ∅)
    rw [←show (∅ : Ctx Atom) = ∅ ∪ ∅ by rfl] at this
    exact this h.mpr

/-- Change the conclusion along an equivalence. -/
def mapEquivConclusion (Γ : Ctx Atom) {A B : Proposition Atom} (e : T.equiv A B)
    (D : ⇓(Γ ⊢[T] A)) : ⇓(Γ ⊢[T] B) :=
  Γ.union_empty ▸ Derivation.cut (Δ := ∅) D e.1

theorem Theory.equiv_iff_equiv_derivable {A B : Proposition Atom} :
    A ≡[T] B ↔ ∀ Γ : Ctx Atom, Derivable (Γ ⊢[T] A) ↔ Derivable (Γ ⊢[T] B) := by
  constructor
  · intro ⟨D, E⟩ Γ
    constructor <;> intro ⟨F⟩
    · exact Γ.union_empty ▸ ⟨Derivation.cut (Δ := ∅) F D⟩
    · exact Γ.union_empty ▸ ⟨Derivation.cut (Δ := ∅) F E⟩
  · intro h
    rw [Theory.equiv_iff]
    constructor
    · exact (h {A}).mp ⟨ass <| by grind⟩
    · exact (h {B}).mpr ⟨ass <| by grind⟩

/-- Replace a hypothesis along an equivalence. -/
def mapEquivHypothesis (Γ : Ctx Atom) {A B : Proposition Atom} (e : T.equiv A B)
    (C : Proposition Atom) (D : ⇓(insert A Γ ⊢[T] C)) : ⇓(insert B Γ ⊢[T] C) := by
  have : insert B Γ = {B} ∪ Γ := rfl
  exact this ▸ Derivation.cut e.2 D

theorem Theory.equiv_iff_equiv_hypothesis {A B : Proposition Atom} :
    A ≡[T] B ↔
      ∀ (Γ : Ctx Atom) (C : Proposition Atom),
      Derivable ((insert A Γ) ⊢[T] C) ↔ Derivable ((insert B Γ) ⊢[T] C) := by
  constructor
  · intro ⟨D,E⟩ Γ C
    constructor <;> intro ⟨F⟩
    · have : insert B Γ = {B} ∪ Γ := rfl
      exact ⟨this ▸ Derivation.cut E F⟩
    · have : insert A Γ = {A} ∪ Γ := rfl
      exact ⟨this ▸ Derivation.cut D F⟩
  · intro h
    rw [Theory.equiv_iff]
    constructor
    · exact (h ∅ B).mpr ⟨ass <| by grind⟩
    · exact (h ∅ A).mp ⟨ass <| by grind⟩

/-- An equivalence of a proposition with itself. -/
def reflEquiv (A : Proposition Atom) : T.equiv A A :=
  let D : ⇓({A} ⊢[T] A) := ass <| by grind;
  ⟨D, D⟩

/-- Reverse an equivalence. -/
def commEquiv {A B : Proposition Atom} (e : T.equiv A B) : T.equiv B A :=
  ⟨e.2, e.1⟩

/-- Compose two equivalences. -/
def transEquiv {A B C : Proposition Atom} (eAB : T.equiv A B)
    (eBC : T.equiv B C) : T.equiv A C :=
  ⟨mapEquivConclusion _ eBC eAB.1, mapEquivConclusion _ (commEquiv eAB) eBC.2⟩

@[refl]
theorem equivalent_refl {T : Theory Atom} (A : Proposition Atom) : A ≡[T] A := by
  exact ⟨reflEquiv A⟩

theorem equivalent_comm {T : Theory Atom} {A B : Proposition Atom} :
    (A ≡[T] B) → B ≡[T] A
  | ⟨e⟩ => ⟨commEquiv e⟩

theorem equivalent_trans {T : Theory Atom} {A B C : Proposition Atom} :
    (A ≡[T] B) → (B ≡[T] C) → A ≡[T] C
  | ⟨e⟩, ⟨e'⟩ => ⟨transEquiv e e'⟩

/-- Equivalence is indeed an equivalence relation. -/
theorem Theory.equiv_equivalence (T : Theory Atom) : Equivalence (T.Equiv (Atom := Atom)) :=
  ⟨equivalent_refl, equivalent_comm, equivalent_trans⟩

/-- The setoid of propositions under equivalence. -/
protected def Theory.propositionSetoid (T : Theory Atom) : Setoid (Proposition Atom) :=
  ⟨T.Equiv, T.equiv_equivalence⟩

end Cslib.Logic.PL
