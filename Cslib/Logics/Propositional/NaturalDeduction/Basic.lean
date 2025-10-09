/-
Copyright (c) 2025 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/
import Cslib.Logics.Propositional.Defs
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.SDiff
import Mathlib.Data.Finset.Image

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
- `Theory.WeakerThan` : a theory `T` is weaker than `T'` if every axiom in `T` is `T'`-derivable.

## Main results

- `Derivation.weak` : weakening as a derived rule.
- `Derivation.cut`, `Derivation.subs` : replace a hypothesis in a derivation — the two versions
differ in the construction of the relevant derivation.
- `Theory.equiv_equivalence` : equivalence of propositions is an equivalence relation.
- `instPreorderTheory` : the relation `Theory.WeakerThan` is a preorder.

## Notation

For `T`-derivability, -sequent-derivability and -equivalence we introduce the notations `⊢[T] A`,
`Γ ⊢[T] A` and `A ≡[T] B`, respectively. `T.WeakerThan T'` is denoted `T ≤ T'`.

## References

- Dag Prawitz, *Natural Deduction: a proof-theoretical study*.
- The sequent-style natural deduction I present here doesn't seem to be common, but it is tersely
presented in §10.4 of Troelstra & van Dalen's *Constructivism in Mathematics: an introduction*.
(Suggestions of better references welcome!)
-/


universe u

namespace PL

open Proposition Theory

variable {Atom : Type u} [DecidableEq Atom] {T : Theory Atom}

/-- Contexts are finsets of propositions. -/
abbrev Ctx (Atom) := Finset (Proposition Atom)

def Ctx.map {Atom Atom' : Type u} [DecidableEq Atom] [DecidableEq Atom'] (f : Atom → Atom') :
    Ctx Atom → Ctx Atom' := Finset.image (Proposition.map f)

/-- Sequents {A₁, ..., Aₙ} ⊢ B. -/
abbrev Sequent (Atom) := Ctx Atom × Proposition Atom

/-- A `T`-derivation of {A₁, ..., Aₙ} ⊢ B demonstrates B using (undischarged) assumptions among Aᵢ,
possibly appealing to axioms from `T`. -/
inductive Theory.Derivation : Sequent Atom → Type _ where
  /-- Axiom -/
  | ax {Γ : Ctx Atom} {A : Proposition Atom} (_ : A ∈ T) : Derivation ⟨Γ, A⟩
  /-- Assumption -/
  | ass {Γ : Ctx Atom} {A : Proposition Atom} (_ : A ∈ Γ) : Derivation ⟨Γ, A⟩
  /-- Conjunction introduction -/
  | conjI {Γ : Ctx Atom} {A B : Proposition Atom} :
      Derivation ⟨Γ, A⟩ → Derivation ⟨Γ, B⟩ → Derivation ⟨Γ, A ⋏ B⟩
  /-- Conjunction elimination left -/
  | conjE₁ {Γ : Ctx Atom} {A B : Proposition Atom} : Derivation ⟨Γ, A ⋏ B⟩ → Derivation ⟨Γ, A⟩
  /-- Conjunction elimination right -/
  | conjE₂ {Γ : Ctx Atom} {A B : Proposition Atom} : Derivation ⟨Γ, A ⋏ B⟩ → Derivation ⟨Γ, B⟩
  /-- Disjunction introduction left -/
  | disjI₁ {Γ : Ctx Atom} {A B : Proposition Atom} : Derivation ⟨Γ, A⟩ → Derivation ⟨Γ, A ⋎ B⟩
  /-- Disjunction introduction right -/
  | disjI₂ {Γ : Ctx Atom} {A B : Proposition Atom} : Derivation ⟨Γ, B⟩ → Derivation ⟨Γ, A ⋎ B⟩
  /-- Disjunction elimination -/
  | disjE {Γ : Ctx Atom} {A B C : Proposition Atom} : Derivation ⟨Γ, A ⋎ B⟩ →
      Derivation ⟨insert A Γ, C⟩ → Derivation ⟨insert B Γ, C⟩ → Derivation ⟨Γ, C⟩
  /-- Implication introduction -/
  | implI {A B : Proposition Atom} (Γ : Ctx Atom) :
      Derivation ⟨insert A Γ, B⟩ → Derivation ⟨Γ, A ⟶ B⟩
  /-- Implication elimination -/
  | implE {Γ : Ctx Atom} {A B : Proposition Atom} :
      Derivation ⟨Γ, A ⟶ B⟩ → Derivation ⟨Γ, A⟩ → Derivation ⟨Γ, B⟩

/-- A sequent is derivable if it has a derivation. -/
def Theory.SDerivable (S : Sequent Atom) := Nonempty (T.Derivation S)

/-- A proposition is derivable if it has a derivation from the empty context. -/
def Theory.PDerivable (A : Proposition Atom) := T.SDerivable ⟨∅, A⟩

@[inherit_doc]
scoped notation Γ " ⊢[" T' "] " A:90 => Theory.SDerivable (T := T') ⟨Γ, A⟩

@[inherit_doc]
scoped notation "⊢[" T' "] " A:90 => Theory.PDerivable (T := T') A

theorem Theory.Derivable.iff_sDerivable_empty {A : Proposition Atom} :
    ⊢[T] A ↔ ∅ ⊢[T] A := by rfl

abbrev SDerivable (S : Sequent Atom) := MPL.SDerivable S

abbrev PDerivable (A : Proposition Atom) := MPL.PDerivable A

scoped notation Γ " ⊢ " A:90 => SDerivable ⟨Γ,A⟩

scoped notation "⊢ " A:90 => PDerivable A

/-- An equivalence between A and B is a derivation of B from A and vice-versa. -/
def Theory.equiv (A B : Proposition Atom) := T.Derivation ⟨{A},B⟩ × T.Derivation ⟨{B},A⟩

/-- `A` and `B` are T-equivalent if `T.equiv A B` is nonempty. -/
def Theory.Equiv (A B : Proposition Atom) := Nonempty (T.equiv A B)

@[inherit_doc]
scoped notation A " ≡[" T' "] " B:29 => Theory.Equiv (T := T') A B

lemma Theory.Equiv.mp {A B : Proposition Atom} (h : A ≡[T] B) : {A} ⊢[T] B :=
  let ⟨D,_⟩ := h; ⟨D⟩

lemma Theory.Equiv.mpr {A B : Proposition Atom} (h : A ≡[T] B) : {B} ⊢[T] A :=
  let ⟨_,D⟩ := h; ⟨D⟩

@[grind]
theorem Theory.equiv_iff {A B : Proposition Atom} : A ≡[T] B ↔ {A} ⊢[T] B ∧ {B} ⊢[T] A := by
  constructor
  · intro h
    exact ⟨h.mp, h.mpr⟩
  · intro ⟨⟨D⟩,⟨E⟩⟩
    exact ⟨D,E⟩

abbrev Equiv : Proposition Atom → Proposition Atom → Prop := MPL.Equiv

scoped infix:29 " ≡ " => Equiv

open Derivation

/-! ### Operations on derivations -/

/-- Weakening is a derived rule. -/
def Theory.Derivation.weak {T T' : Theory Atom} {Γ Δ : Ctx Atom} {A : Proposition Atom}
    (hTheory : T ⊆ T') (hCtx : Γ ⊆ Δ) : T.Derivation ⟨Γ, A⟩ → T'.Derivation ⟨Δ, A⟩
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
def Theory.Derivation.weak_theory {T T' : Theory Atom} {Γ : Ctx Atom} {A : Proposition Atom}
    (hTheory : T ⊆ T') : T.Derivation ⟨Γ, A⟩ → T'.Derivation ⟨Γ, A⟩ :=
  Theory.Derivation.weak hTheory (by rfl)

/-- Weakening the context only. -/
def Theory.Derivation.weak_ctx {T : Theory Atom} {Γ Δ : Ctx Atom} {A : Proposition Atom}
    (hCtx : Γ ⊆ Δ) : T.Derivation ⟨Γ, A⟩ → T.Derivation ⟨Δ, A⟩ :=
  Theory.Derivation.weak (by rfl) hCtx

/-- Proof irrelevant weakening. -/
theorem Theory.SDerivable.weak {T T' : Theory Atom} {Γ Δ : Ctx Atom} {A : Proposition Atom}
    (hTheory : T ⊆ T') (hCtx : Γ ⊆ Δ) : Γ ⊢[T] A → (T'.SDerivable ⟨Δ, A⟩)
  | ⟨D⟩ => ⟨D.weak hTheory hCtx⟩

/-- Proof irrelevant weakening of the theory. -/
theorem Theory.SDerivable.weak_theory {T T' : Theory Atom} {Γ : Ctx Atom} {A : Proposition Atom}
    (hTheory : T ⊆ T') : Γ ⊢[T] A → Γ ⊢[T'] A
  | ⟨D⟩ => ⟨D.weak_theory hTheory⟩

/-- Proof irrelevant weakening of the context. -/
theorem Theory.SDerivable.weak_ctx {T : Theory Atom} {Γ Δ : Ctx Atom} {A : Proposition Atom}
    (hCtx : Γ ⊆ Δ) : Γ ⊢[T] A → Δ ⊢[T] A
  | ⟨D⟩ => ⟨D.weak_ctx hCtx⟩

/--
Implement the cut rule, removing a hypothesis `A` from `E` using a derivation `D`. This is *not*
substitution, which would replace appeals to `A` in `E` by the whole derivation `D`.
-/
def Theory.Derivation.cut {Γ Δ : Ctx Atom} {A B : Proposition Atom}
    (D : T.Derivation ⟨Γ, A⟩) (E : T.Derivation ⟨insert A Δ, B⟩) : T.Derivation ⟨Γ ∪ Δ, B⟩ := by
  refine implE ?_ (D.weak_ctx Finset.subset_union_left)
  have : insert A Δ ⊆ insert A (Γ ∪ Δ) := by grind
  exact implI (Γ ∪ Δ) <| E.weak_ctx this

/-- Proof irrelevant cut rule. -/
theorem Theory.SDerivable.cut {Γ Δ : Ctx Atom} {A B : Proposition Atom} :
    Γ ⊢[T] A → (insert A Δ) ⊢[T] B → (Γ ∪ Δ) ⊢[T] B
  | ⟨D⟩, ⟨E⟩ => ⟨D.cut E⟩

/-- Remove unnecessary hypotheses. This can't be computable because it requires picking an order
on the finset `Δ`. -/
theorem Theory.SDerivable.cut_away {Γ Δ : Ctx Atom} {B : Proposition Atom}
    (hΔ : ∀ A ∈ Δ, Γ ⊢[T] A) (hDer : (Γ ∪ Δ) ⊢[T] B) : Γ ⊢[T] B := by
  induction Δ using Finset.induction with
  | empty => exact hDer.weak_ctx (by grind)
  | insert A Δ hA ih =>
    apply ih
    · intro A' hA'
      exact hΔ A' <| Finset.mem_insert_of_mem hA'
    · apply Finset.union_left_idem Γ Δ ▸ Theory.SDerivable.cut (Δ := Γ ∪ Δ)
      · exact hΔ A <| Finset.mem_insert_self A Δ
      · rwa [← Finset.union_insert A Γ Δ]

/-- Substitution of a derivation `D` for one of the hypotheses in the context `Δ` of `E`. -/
def Theory.Derivation.subs {Γ Δ : Ctx Atom} {A B : Proposition Atom}
    (D : T.Derivation ⟨Γ, A⟩) (E : T.Derivation ⟨Δ, B⟩) : T.Derivation ⟨Γ ∪ (Δ \ {A}), B⟩ := by
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
def Theory.Derivation.map {Atom Atom' : Type u} [DecidableEq Atom] [DecidableEq Atom']
    {T : Theory Atom} (f : Atom → Atom') {Γ : Ctx Atom} {B : Proposition Atom} :
    T.Derivation ⟨Γ, B⟩ → (T.map f).Derivation ⟨Γ.map f, B.map f⟩
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

theorem Theory.Derivable.image {Atom' : Type u} [DecidableEq Atom'] {T : Theory Atom}
    (f : Atom → Atom') {Γ : Ctx Atom} {B : Proposition Atom} :
    Γ ⊢[T] B → (Γ.map f) ⊢[T.map f] (B.map f) := by
  intro ⟨D⟩
  exact ⟨D.map f⟩

/-! ### Properties of equivalence -/

def Theory.derivationTop [Inhabited Atom] : T.Derivation ⟨∅, ⊤⟩ :=
  implI ∅ <| ass <| by grind

theorem Theory.pDerivable_top [Inhabited Atom] : ⊢[T] ⊤ := ⟨T.derivationTop⟩

theorem Theory.pDerivable_iff_equiv_top [Inhabited Atom] (A : Proposition Atom) :
    ⊢[T] A ↔ A ≡[T] ⊤ := by
  constructor <;> intro h
  · refine ⟨T.derivationTop.weak_ctx <| by grind, ?_⟩
    let D := Classical.choice h
    exact D.weak_ctx <| by grind
  · have : (∅ : Ctx Atom) = ∅ ∪ ∅ := rfl
    rw [PDerivable, this]
    refine Theory.SDerivable.cut T.pDerivable_top h.mpr

/-- Change the conclusion along an equivalence. -/
def mapEquivConclusion (Γ : Ctx Atom) {A B : Proposition Atom} (e : T.equiv A B)
    (D : T.Derivation ⟨Γ, A⟩) : T.Derivation ⟨Γ, B⟩ :=
  Γ.union_empty ▸ Theory.Derivation.cut (Δ := ∅) D e.1

theorem Theory.equiv_iff_equiv_conclusion {A B : Proposition Atom} :
    A ≡[T] B ↔ ∀ Γ : Ctx Atom, Γ ⊢[T] A ↔ Γ ⊢[T] B := by
  constructor
  · intro ⟨D,E⟩ Γ
    constructor <;> intro ⟨F⟩
    · exact Γ.union_empty ▸ ⟨Theory.Derivation.cut (Δ := ∅) F D⟩
    · exact Γ.union_empty ▸ ⟨Theory.Derivation.cut (Δ := ∅) F E⟩
  · intro h
    rw [Theory.equiv_iff]
    constructor
    · exact (h {A}).mp ⟨ass <| by grind⟩
    · exact (h {B}).mpr ⟨ass <| by grind⟩

/-- Replace a hypothesis along an equivalence. -/
def mapEquivHypothesis (Γ : Ctx Atom) {A B : Proposition Atom} (e : T.equiv A B)
    (C : Proposition Atom) (D : T.Derivation ⟨insert A Γ, C⟩) : T.Derivation ⟨insert B Γ, C⟩ := by
  have : insert B Γ = {B} ∪ Γ := rfl
  exact this ▸ Theory.Derivation.cut e.2 D

theorem Theory.equiv_iff_equiv_hypothesis {A B : Proposition Atom} :
    A ≡[T] B ↔
      ∀ (Γ : Ctx Atom) (C : Proposition Atom), (insert A Γ) ⊢[T] C ↔ (insert B Γ) ⊢[T] C := by
  constructor
  · intro ⟨D,E⟩ Γ C
    constructor <;> intro ⟨F⟩
    · have : insert B Γ = {B} ∪ Γ := rfl
      exact ⟨this ▸ Theory.Derivation.cut E F⟩
    · have : insert A Γ = {A} ∪ Γ := rfl
      exact ⟨this ▸ Theory.Derivation.cut D F⟩
  · intro h
    rw [Theory.equiv_iff]
    constructor
    · exact (h ∅ B).mpr ⟨ass <| by grind⟩
    · exact (h ∅ A).mp ⟨ass <| by grind⟩

def reflEquiv (A : Proposition Atom) : T.equiv A A :=
  let D : Derivation ⟨{A},A⟩ := ass <| by grind;
  ⟨D,D⟩

def commEquiv {A B : Proposition Atom} (e : T.equiv A B) : T.equiv B A :=
  ⟨e.2, e.1⟩

def transEquiv {A B C : Proposition Atom} (eAB : T.equiv A B)
    (eBC : T.equiv B C) : T.equiv A C :=
  ⟨mapEquivConclusion _ eBC eAB.1, mapEquivConclusion _ (commEquiv eAB) eBC.2⟩

@[refl]
theorem equivalent_refl {T : Theory Atom} (A : Proposition Atom) : A ≡[T] A := by
  exact ⟨reflEquiv A⟩

theorem equivalent_comm {T : Theory Atom} {A B : Proposition Atom} :
    A ≡[T] B → B ≡[T] A
  | ⟨e⟩ => ⟨commEquiv e⟩

theorem equivalent_trans {T : Theory Atom} {A B C : Proposition Atom} :
    A ≡[T] B → B ≡[T] C → A ≡[T] C
  | ⟨e⟩, ⟨e'⟩ => ⟨transEquiv e e'⟩

/-- Equivalence is indeed an equivalence relation. -/
theorem Theory.equiv_equivalence (T : Theory Atom) : Equivalence (T.Equiv (Atom := Atom)) :=
  ⟨equivalent_refl, equivalent_comm, equivalent_trans⟩

protected def Theory.propositionSetoid (T : Theory Atom) : Setoid (Proposition Atom) :=
  ⟨T.Equiv, T.equiv_equivalence⟩


/-! ### Operations on theories

TODO: if we generalised the derivability relation to be a typeclass, these definitions and results
ought also to generalise.
-/

/-- A theory `T` is weaker than `T'` if all its axioms are `T'`-derivable. -/
def Theory.WeakerThan (T T' : Theory Atom) : Prop :=
  ∀ A ∈ T, T'.PDerivable A

instance instLETheory : LE (Theory Atom) where
  le := Theory.WeakerThan

/-- Replace appeals to axioms in `T` by `T'`-derivations. -/
noncomputable def Theory.Derivation.mapLE {T T' : Theory Atom} {S : Sequent Atom} (h : T ≤ T') :
    T.Derivation S → T'.Derivation S
  | ax hB => Classical.choice (h _ hB) |>.weak_ctx (by grind)
  | ass hB => ass hB
  | conjI D E => conjI (D.mapLE h) (E.mapLE h)
  | conjE₁ D => conjE₁ (D.mapLE h)
  | conjE₂ D => conjE₂ (D.mapLE h)
  | disjI₁ D => disjI₁ (D.mapLE h)
  | disjI₂ D => disjI₂ (D.mapLE h)
  | disjE D E E' => disjE (D.mapLE h) (E.mapLE h) (E'.mapLE h)
  | implI _ D => implI _ (D.mapLE h)
  | implE D E => implE (D.mapLE h) (E.mapLE h)

/-- Proof irrelevant substitution of `T`-axioms. -/
theorem Theory.Derivable.map_LE {T T' : Theory Atom} {S : Sequent Atom} (h : T ≤ T') :
    T.SDerivable S → T'.SDerivable S
  | ⟨D⟩ => ⟨D.mapLE h⟩

/-- `T ≤ T'` is in fact equivalent to the stronger condition in the conclusion of
`Theory.Derivation.mapLE`. -/
theorem Theory.LE_iff_map {T T' : Theory Atom} :
    T ≤ T' ↔ ∀ S : Sequent Atom, T.SDerivable S → T'.SDerivable S := by
  constructor
  · intro h _
    exact Theory.Derivable.map_LE h
  · intro h A hA
    exact h ⟨∅, A⟩ ⟨ax hA⟩

instance instPreorderTheory : Preorder (Theory Atom) where
  lt T T' := T.WeakerThan T' ∧ ¬ T'.WeakerThan T
  le_refl _ _ h := ⟨ax h⟩
  le_trans _ _ _ h h' A hA := Theory.Derivable.map_LE h' (h A hA)

/-- An extension `T'` of a theory `T` generalises `Theory.WeakerThan` to allow a change of the
atomic language. -/
structure Extension {Atom Atom' : Type u} [DecidableEq Atom] [DecidableEq Atom'] (T : Theory Atom)
    (T' : Theory Atom') where
  f : Atom → Atom'
  h : T.map f ≤ T'

/-- An extension of theories is conservative if it doesn't add any new theorems, when restricted
to the domain language `Atom`. -/
def IsConservative {Atom Atom' : Type u} [DecidableEq Atom] [DecidableEq Atom'] (T : Theory Atom)
    (T' : Theory Atom') : Extension T T' → Prop
  | ⟨f, _⟩ => ∀ (A : Proposition Atom), ⊢[T'] (A.map f) → ⊢[T] A

end PL
