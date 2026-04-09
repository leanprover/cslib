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

- `Sequent` : a triple of `Theory Atom`, `Ctx Atom`, `Proposition Atom`.
- `Derivation` : natural deduction derivation, done in "sequent style", ie with explicit
hypotheses at each step. Contexts are `Finset`'s of propositions, which avoids explicit contraction
and exchange, and the axiom rule derives `{A} ∪ Γ ⊢ A` for any context `Γ`, allowing weakening to
be a derived rule. The derivation may appeal to hypotheses from the `Theory T`. This defines an
instance of `InferenceSystem` for `Sequent`.
- `Theory.equiv` : `Type`-valued equivalence of propositions.
- `Theory.Equiv` : `Prop`-valued equivalence of propositions.

## Main results

- `Derivation.weak` : weakening as a derived rule.
- `Derivation.cut`, `Derivation.subs` : replace a hypothesis in a derivation — the two versions
differ in the construction of the relevant derivation.
- `Theory.equiv_equivalence` : equivalence of propositions is an equivalence relation.

## Notation

The sequent `⟨T, Γ, A⟩` is notated `Γ ⊢[T] A`, and `⊢[T] A` abbreviates `∅ ⊢[T] A`.

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

variable {Atom : Type u} [DecidableEq Atom]

/-- Contexts are finsets of propositions. -/
abbrev Ctx (Atom) := Finset (Proposition Atom)

/-- Map a context along a substitution. -/
def Ctx.subst {Atom Atom' : Type u} [DecidableEq Atom'] (f : Atom → Proposition Atom') :
    Ctx Atom → Ctx Atom' := Finset.image (· >>= f)

/-- Sequents {A₁, ..., Aₙ} ⊢ B, considered within a theory `T`. -/
abbrev Sequent {Atom} := Theory Atom × Ctx Atom × Proposition Atom

@[inherit_doc Sequent]
scoped notation Γ:60 " ⊢[" T "] " A => (⟨T, Γ, A⟩ : Sequent)

/-- A sequent with empty context. -/
abbrev Sequent₁ {Atom} := Theory Atom × Proposition Atom

@[inherit_doc Sequent₁]
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

theorem Derivation.sequent₁_eq {A : Proposition Atom} : ⇓(⊢[T] A) = ⇓(∅ ⊢[T] A) := rfl

theorem Derivable.iff_derivable_empty {A : Proposition Atom} :
    Derivable (⊢[T] A) ↔ Derivable (∅ ⊢[T] A) := by rfl

/-- An equivalence between A and B is a derivation of B from A and vice-versa. -/
def Theory.equiv (A B : Proposition Atom) :=
  ⇓({A} ⊢[T] B) × ⇓({B} ⊢[T] A)

/-- Forward direction of an equivalence. -/
def Theory.equiv.mp {A B : Proposition Atom} (e : T.equiv A B) : (⇓({A} ⊢[T] B)) := e.1

/-- Reverse direction of an equivalence. -/
def Theory.equiv.mpr {A B : Proposition Atom} (e : T.equiv A B) : (⇓({B} ⊢[T] A)) := e.2

/-- `A` and `B` are T-equivalent if `T.equiv A B` is nonempty. -/
def Theory.Equiv (A B : Proposition Atom) := Nonempty (T.equiv A B)

@[inherit_doc]
scoped notation A " ≡[" T' "] " B:29 => Theory.Equiv (T := T') A B

lemma Theory.Equiv.mp {A B : Proposition Atom} (h : A ≡[T] B) : Derivable ({A} ⊢[T] B) :=
  ⟨h.some.1⟩

lemma Theory.Equiv.mpr {A B : Proposition Atom} (h : A ≡[T] B) : Derivable ({B} ⊢[T] A) :=
  ⟨h.some.2⟩

theorem Theory.equiv_iff {A B : Proposition Atom} :
  A ≡[T] B ↔ Derivable ({A} ⊢[T] B) ∧ Derivable ({B} ⊢[T] A) := by
  constructor
  · intro h
    exact ⟨h.mp, h.mpr⟩
  · intro ⟨⟨D⟩, ⟨E⟩⟩
    exact ⟨D, E⟩

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
theorem Theory.Derivable.cut_away {Γ Δ : Ctx Atom} {B : Proposition Atom}
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

/-- Substitution of a family of derivations `D` for hypotheses in the context `Γ` of `E`. -/
def Derivation.subs {Γ Γ' Δ : Ctx Atom} {B : Proposition Atom}
    (Ds : ∀ A ∈ Γ', Derivation (Δ ⊢[T] A)) :
      Derivation (Γ ⊢[T] B) → Derivation ((Γ \ Γ' ∪ Δ) ⊢[T] B)
  | ax hB => ax hB
  | @ass _ _ _ _ B hB => by
    by_cases B ∈ Γ'
    case pos h =>
      exact (Ds B h).weak_ctx <| by grind
    case neg h =>
      exact ass <| by grind
  | conjI E E' => conjI (E.subs Ds) (E'.subs Ds)
  | conjE₁ E => conjE₁ <| E.subs Ds
  | conjE₂ E => conjE₂ <| E.subs Ds
  | disjI₁ E => disjI₁ <| E.subs Ds
  | disjI₂ E => disjI₂ <| E.subs Ds
  | @disjE _ _ _ _ C C' _ E E' E'' .. => by
    apply disjE (E.subs Ds)
    · rw [show insert C (Γ \ Γ' ∪ Δ) = (insert C Γ \ Γ') ∪ insert C Δ by grind]
      exact E'.subs Ds |>.weak_ctx (by grind)
    · rw [show insert C' (Γ \ Γ' ∪ Δ) = (insert C' Γ \ Γ') ∪ insert C' Δ by grind]
      exact E''.subs Ds |>.weak_ctx (by grind)
  | @implI _ _ _ A' _ _ E .. => by
    apply implI
    rw [show insert A' (Γ \ Γ' ∪ Δ) = (insert A' Γ \ Γ') ∪ insert A' Δ by grind]
    exact E.subs Ds |>.weak_ctx (by grind)
  | implE E E' => implE (E.subs Ds) (E'.subs Ds)

/-- Transport a derivation along a substitution of atoms. -/
def Derivation.substAtom {Atom Atom' : Type u} [DecidableEq Atom] [DecidableEq Atom']
    {T : Theory Atom} (f : Atom → Proposition Atom') {Γ : Ctx Atom} {B : Proposition Atom} :
    Derivation (Γ ⊢[T] B) → Derivation (Γ.subst f ⊢[T.subst f] B >>= f)
  | ax h => ax <| Set.mem_image_of_mem (· >>= f) h
  | ass h => ass <| Finset.mem_image_of_mem (· >>= f) h
  | conjI D E => conjI (D.substAtom f) (E.substAtom f)
  | conjE₁ D => conjE₁ (D.substAtom f)
  | conjE₂ D => conjE₂ (D.substAtom f)
  | disjI₁ D => disjI₁ (D.substAtom f)
  | disjI₂ D => disjI₂ (D.substAtom f)
  | disjE D E E' => disjE (D.substAtom f)
    ((Finset.image_insert (· >>= f) _ _) ▸ E.substAtom f)
    ((Finset.image_insert (· >>= f) _ _) ▸ E'.substAtom f)
  | implI _ D => implI _ <| (Finset.image_insert (· >>= f) _ _) ▸ (D.substAtom f)
  | implE D E => implE (D.substAtom f) (E.substAtom f)

theorem Theory.Derivable.substAtom {Atom Atom' : Type u} [DecidableEq Atom] [DecidableEq Atom']
    {T : Theory Atom}
    (f : Atom → Proposition Atom') {Γ : Ctx Atom} {B : Proposition Atom} :
    Derivable (Γ ⊢[T] B) → Derivable ((Γ.subst f) ⊢[T.subst f] (B >>= f))
  | ⟨D⟩ => ⟨D.substAtom f⟩

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

/-- Replace a hypothesis along an equivalence. -/
def mapEquivHypothesis (Γ : Ctx Atom) {A B : Proposition Atom} (e : T.equiv A B)
    (C : Proposition Atom) (D : ⇓(insert A Γ ⊢[T] C)) : ⇓(insert B Γ ⊢[T] C) := by
  have : insert B Γ = {B} ∪ Γ := rfl
  exact this ▸ Derivation.cut e.2 D

/-- An equivalence of a proposition with itself. -/
def Theory.equiv.refl (A : Proposition Atom) : T.equiv A A :=
  let D : ⇓({A} ⊢[T] A) := ass <| by grind;
  ⟨D, D⟩

/-- Reverse an equivalence. -/
def Theory.equiv.symm {A B : Proposition Atom} (e : T.equiv A B) : T.equiv B A :=
  ⟨e.2, e.1⟩

/-- Compose two equivalences. -/
def Theory.equiv.trans {A B C : Proposition Atom} (eAB : T.equiv A B)
    (eBC : T.equiv B C) : T.equiv A C :=
  ⟨mapEquivConclusion _ eBC eAB.1, mapEquivConclusion _ eAB.symm eBC.2⟩

/-- `A` and `B` are equivalent (in `T`) iff they are provable from the same contexts. -/
theorem Theory.equiv_iff_equiv_derivable {A B : Proposition Atom} :
    A ≡[T] B ↔ ∀ Γ : Ctx Atom, Derivable (Γ ⊢[T] A) ↔ Derivable (Γ ⊢[T] B) := by
  constructor
  · intro ⟨e⟩ Γ
    exact ⟨fun D => mapEquivConclusion Γ e D.some, fun D => mapEquivConclusion Γ e.symm D.some⟩
  · intro h
    rw [Theory.equiv_iff]
    constructor
    · exact (h {A}).mp ⟨ass <| by grind⟩
    · exact (h {B}).mpr ⟨ass <| by grind⟩

/-- `A` and `B` are equivalent (in `T`) iff they have the same strength as hypotheses. -/
theorem Theory.equiv_iff_equiv_derivable_hypothesis {A B : Proposition Atom} :
    A ≡[T] B ↔
      ∀ (Γ : Ctx Atom) (C : Proposition Atom),
      Derivable ((insert A Γ) ⊢[T] C) ↔ Derivable ((insert B Γ) ⊢[T] C) := by
  constructor
  · intro ⟨e⟩ Γ C
    exact ⟨fun D => mapEquivHypothesis Γ e C D.some, fun E => mapEquivHypothesis Γ e.symm C E.some⟩
  · intro h
    rw [Theory.equiv_iff]
    constructor
    · exact (h ∅ B).mpr ⟨ass <| by grind⟩
    · exact (h ∅ A).mp ⟨ass <| by grind⟩

@[refl]
theorem Theory.Equiv.refl {T : Theory Atom} (A : Proposition Atom) : A ≡[T] A := by
  exact ⟨Theory.equiv.refl A⟩

theorem Theory.Equiv.symm {T : Theory Atom} {A B : Proposition Atom} :
    (A ≡[T] B) → B ≡[T] A
  | ⟨e⟩ => ⟨e.symm⟩

theorem Theory.Equiv.trans {T : Theory Atom} {A B C : Proposition Atom} :
    (A ≡[T] B) → (B ≡[T] C) → A ≡[T] C
  | ⟨e⟩, ⟨e'⟩ => ⟨e.trans e'⟩

/-- Equivalence is indeed an equivalence relation. -/
theorem Theory.equiv_equivalence (T : Theory Atom) : Equivalence (T.Equiv (Atom := Atom)) :=
  ⟨Equiv.refl, Equiv.symm, Equiv.trans⟩

/-- The setoid of propositions under equivalence. -/
protected def Theory.propositionSetoid (T : Theory Atom) : Setoid (Proposition Atom) :=
  ⟨T.Equiv, T.equiv_equivalence⟩

end Cslib.Logic.PL
