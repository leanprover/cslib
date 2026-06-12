/-
Copyright (c) 2025 Thomas Waring, 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring, Benjamin Brast-McKie
-/
module

public import Cslib.Logics.Propositional.Defs
public import Cslib.Foundations.Logic.InferenceSystem
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Finset.SDiff
public import Mathlib.Data.Finset.Image

/-! # Natural deduction for propositional logic

We define, for minimal logic, deduction trees (a `Type`) and derivability (a `Prop`) relative to a
`Theory` (set of propositions).

## Main definitions

- `Sequent` : a pair of a context and conclusion.
- `Derivation` : natural deduction derivation, done in "sequent style", ie with explicit
hypotheses at each step. Contexts are `Finset`'s of propositions, which avoids explicit contraction
and exchange, and the axiom rule derives `Γ ⊢ A` for any context `Γ` with `A ∈ Γ`, allowing
weakening to be a derived rule. The derivation may appeal to hypotheses from the `Theory T`. This
defines an instance of `InferenceSystem T Sequent`.
- `Theory.equiv` : `Type`-valued equivalence of propositions.
- `Theory.Equiv` : `Prop`-valued equivalence of propositions.

## Main results

- `Derivation.weak` : weakening as a derived rule.
- `Derivation.cut`, `Derivation.subs` : replace a hypothesis in a derivation — the two versions
differ in the construction of the relevant derivation.
- `Theory.equiv_equivalence` : equivalence of propositions is an equivalence relation.

## Notation

The sequent `⟨Γ, A⟩` is notated `Γ ⊢ A`, so that a derivation using axioms from a theory `T` is
noted `T⇓(Γ ⊢ A)`. We define also an `InferenceSystem T (Proposition Atom)`, so that `T⇓A`
abbreviates a derivation of `A` in the empty context: `T⇓(∅ ⊢ A)`.

## Implementation notes

The primitive inference rules are: axiom (from theory), assumption (from context),
implication introduction and elimination, and ex falso quodlibet (bottom elimination).
Conjunction and disjunction rules are derivable from these primitives together with
the definitions of `∧` and `∨` in terms of `→` and `⊥`, so they need not be postulated.

## References

* [D. Prawitz, *Natural Deduction: A Proof-Theoretical Study*][Prawitz1965]
* [A. S. Troelstra, D. van Dalen,
  *Constructivism in Mathematics: An Introduction*][TroelstraVanDalen1988], Section 10.4
* [G. Gentzen,
  *Untersuchungen über das logische Schließen*][Gentzen1935]
-/

@[expose] public section

universe u

namespace Cslib.Logic.PL

open Proposition Theory InferenceSystem DerivableIn

variable {Atom : Type u} [DecidableEq Atom]

/-- Contexts are finsets of propositions. -/
abbrev Ctx (Atom) := Finset (Proposition Atom)

/-- Map a context along a substitution. -/
def Ctx.subst {Atom Atom' : Type u} [DecidableEq Atom'] (f : Atom → Proposition Atom') :
    Ctx Atom → Ctx Atom' := Finset.image (· >>= f)

/-- Sequents {A₁, ..., Aₙ} ⊢ B. -/
abbrev Sequent {Atom} := Ctx Atom × Proposition Atom

@[inherit_doc Sequent]
scoped notation Γ:60 " ⊢ " A => (⟨Γ, A⟩ : Sequent)

/-- A `T`-derivation of {A₁, ..., Aₙ} ⊢ B demonstrates B using (undischarged) assumptions among Aᵢ,
possibly appealing to axioms from `T`. Primitives: axiom, assumption, implication intro/elim,
and ex falso quodlibet (bottom elimination). -/
inductive Theory.Derivation {T : Theory Atom} : Ctx Atom → Proposition Atom → Type u where
  /-- Axiom -/
  | ax {Γ : Ctx Atom} {A : Proposition Atom} (_ : A ∈ T) : Derivation Γ A
  /-- Assumption -/
  | ass {Γ : Ctx Atom} {A : Proposition Atom} (_ : A ∈ Γ) : Derivation Γ A
  /-- Implication introduction -/
  | impI {A B : Proposition Atom} (Γ : Ctx Atom) :
      Derivation (insert A Γ) B → Derivation Γ (A → B)
  /-- Implication elimination (modus ponens) -/
  | impE {Γ : Ctx Atom} {A B : Proposition Atom} :
      Derivation Γ (A → B) → Derivation Γ A → Derivation Γ B
  /-- Ex falso quodlibet (bottom elimination) -/
  | botE {Γ : Ctx Atom} {A : Proposition Atom} :
      Derivation Γ ⊥ → Derivation Γ A

/-- Inference system for derivations under the theory `T`. -/
instance (T : Theory Atom) : InferenceSystem T (Sequent (Atom := Atom)) where
  derivation S := T.Derivation S.1 S.2

/-- Inference system for propositions (using the empty context). -/
instance (T : Theory Atom) : InferenceSystem T (Proposition Atom) where
  derivation A := T.Derivation ∅ A

variable {T : Theory Atom}

theorem Theory.Derivation.emptySequent_eq {A : Proposition Atom} : T⇓A = T⇓(∅ ⊢ A) := rfl

theorem DerivableIn.iff_derivableIn_empty {A : Proposition Atom} :
    DerivableIn T A ↔ DerivableIn T (∅ ⊢ A) := by rfl

/-- An equivalence between A and B is a derivation of B from A and vice-versa. -/
def Theory.equiv (A B : Proposition Atom) :=
  T⇓({A} ⊢ B) × T⇓({B} ⊢ A)

/-- Forward direction of an equivalence. -/
def Theory.equiv.mp {A B : Proposition Atom} (e : T.equiv A B) : T⇓({A} ⊢ B) := e.1

/-- Reverse direction of an equivalence. -/
def Theory.equiv.mpr {A B : Proposition Atom} (e : T.equiv A B) : T⇓({B} ⊢ A) := e.2

/-- `A` and `B` are T-equivalent if `T.equiv A B` is nonempty. -/
def Theory.Equiv (A B : Proposition Atom) := Nonempty (T.equiv A B)

@[inherit_doc]
scoped notation A " ≡[" T' "] " B:29 => Theory.Equiv (T := T') A B

lemma Theory.Equiv.mp {A B : Proposition Atom} (h : A ≡[T] B) : DerivableIn T ({A} ⊢ B) :=
  ⟨h.some.mp⟩

lemma Theory.Equiv.mpr {A B : Proposition Atom} (h : A ≡[T] B) : DerivableIn T ({B} ⊢ A) :=
  ⟨h.some.mpr⟩

theorem Theory.equiv_iff {A B : Proposition Atom} :
  A ≡[T] B ↔ DerivableIn T ({A} ⊢ B) ∧ DerivableIn T ({B} ⊢ A) := by
  constructor
  · intro h
    exact ⟨h.mp, h.mpr⟩
  · intro ⟨⟨D⟩, ⟨E⟩⟩
    exact ⟨D, E⟩

/-- Minimally equivalent propositions. -/
abbrev Equiv : Proposition Atom → Proposition Atom → Prop := MPL.Equiv

@[inherit_doc]
scoped infix:29 " ≡ " => Equiv

open Derivation DerivableIn

/-! ### Operations on derivations -/

/-- Weakening is a derived rule. -/
def Theory.Derivation.weak {T T' : Theory Atom} {Γ Δ : Ctx Atom} {A : Proposition Atom}
    (hTheory : T ⊆ T') (hCtx : Γ ⊆ Δ) : T.Derivation Γ A → T'.Derivation Δ A
  | ax hA => ax <| hTheory hA
  | ass hA => ass <| hCtx hA
  | @impI _ _ _ A B Γ D => impI (Δ) <| D.weak hTheory <| Finset.insert_subset_insert _ hCtx
  | impE D D' => impE (D.weak hTheory hCtx) (D'.weak hTheory hCtx)
  | botE D => botE <| D.weak hTheory hCtx

/-- Weakening the theory only. -/
def Theory.Derivation.weakTheory {T T' : Theory Atom} {Γ : Ctx Atom} {A : Proposition Atom}
    (hTheory : T ⊆ T') : T⇓(Γ ⊢ A) → T'⇓(Γ ⊢ A):=
  Derivation.weak hTheory Finset.Subset.rfl

/-- Weakening the context only. -/
def Theory.Derivation.weakCtx {T : Theory Atom} {Γ Δ : Ctx Atom} {A : Proposition Atom}
    (hCtx : Γ ⊆ Δ) : T⇓(Γ ⊢ A) → T⇓(Δ ⊢ A) :=
  Derivation.weak Set.Subset.rfl hCtx

/-- Proof irrelevant weakening. -/
theorem DerivableIn.weak {T T' : Theory Atom} {Γ Δ : Ctx Atom} {A : Proposition Atom}
    (hTheory : T ⊆ T') (hCtx : Γ ⊆ Δ) : DerivableIn T (Γ ⊢ A) → DerivableIn T' (Δ ⊢ A)
  | ⟨D⟩ => ⟨D.weak hTheory hCtx⟩

/-- Proof irrelevant weakening of the theory. -/
theorem DerivableIn.weakTheory {T T' : Theory Atom} {Γ : Ctx Atom} {A : Proposition Atom}
    (hTheory : T ⊆ T') : DerivableIn T (Γ ⊢ A) → DerivableIn T' (Γ ⊢ A)
  | ⟨D⟩ => ⟨D.weakTheory hTheory⟩

/-- Proof irrelevant weakening of the context. -/
theorem DerivableIn.weakCtx {T : Theory Atom} {Γ Δ : Ctx Atom} {A : Proposition Atom}
    (hCtx : Γ ⊆ Δ) : DerivableIn T (Γ ⊢ A) → DerivableIn T (Δ ⊢ A)
  | ⟨D⟩ => ⟨D.weakCtx hCtx⟩

/--
Implement the cut rule, removing a hypothesis `A` from `E` using a derivation `D`. This is *not*
substitution, which would replace appeals to `A` in `E` by the whole derivation `D`.
-/
def Theory.Derivation.cut {Γ Δ : Ctx Atom} {A B : Proposition Atom}
    (D : T⇓(Γ ⊢ A)) (E : T⇓(insert A Δ ⊢ B)) : T⇓((Γ ∪ Δ) ⊢ B) := by
  refine impE (A := A) ?_ (D.weakCtx Finset.subset_union_left)
  have : insert A Δ ⊆ insert A (Γ ∪ Δ) := by grind
  exact impI (Γ ∪ Δ) <| E.weakCtx this

/-- Proof irrelevant cut rule. -/
theorem DerivableIn.cut {Γ Δ : Ctx Atom} {A B : Proposition Atom} :
    DerivableIn T (Γ ⊢ A) → DerivableIn T ((insert A Δ) ⊢ B) → DerivableIn T ((Γ ∪ Δ) ⊢ B)
  | ⟨D⟩, ⟨E⟩ => ⟨D.cut E⟩

/-- Remove unnecessary hypotheses. This can't be computable because it requires picking an order
on the finset `Δ`. -/
theorem DerivableIn.cut_away {Γ Γ' : Ctx Atom} {B : Proposition Atom}
    (hΔ : ∀ A ∈ Γ', DerivableIn T (Γ ⊢ A)) (hDer : DerivableIn T ((Γ ∪ Γ') ⊢ B)) :
    DerivableIn T (Γ ⊢ B) := by
  induction Γ' using Finset.induction with
  | empty => exact DerivableIn.weakCtx (by grind) hDer
  | insert A Δ hA ih =>
    apply ih
    · intro A' hA'
      exact hΔ A' <| Finset.mem_insert_of_mem hA'
    · apply Finset.union_left_idem Γ Δ ▸ DerivableIn.cut (Δ := Γ ∪ Δ)
      · exact hΔ A <| Finset.mem_insert_self A Δ
      · rwa [← Finset.union_insert A Γ Δ]

/-- Substitution of a family of derivations `D` for hypotheses in the context `Γ` of `E`. TODO:
this implementation is not capture avoiding. -/
def Theory.Derivation.subs {Γ Γ' Δ : Ctx Atom} {B : Proposition Atom}
    (Ds : ∀ A ∈ Γ', T⇓(Δ ⊢ A)) :
      T.Derivation Γ B → T.Derivation (Γ \ Γ' ∪ Δ) B
  | ax hB => ax hB
  | @ass _ _ _ _ B hB => by
    by_cases B ∈ Γ'
    case pos h =>
      exact (Ds B h).weakCtx <| by grind
    case neg h =>
      exact ass <| by grind
  | @impI _ _ _ A' _ _ E .. => by
    apply impI
    rw [show insert A' (Γ \ Γ' ∪ Δ) = (insert A' Γ \ Γ') ∪ insert A' Δ by grind]
    exact E.subs Ds |>.weakCtx (by grind)
  | impE E E' => impE (E.subs Ds) (E'.subs Ds)
  | botE E => botE <| E.subs Ds

/-- Transport a derivation along a substitution of atoms. -/
def Theory.Derivation.substAtom {Atom Atom' : Type u} [DecidableEq Atom] [DecidableEq Atom']
    {T : Theory Atom} (f : Atom → Proposition Atom') {Γ : Ctx Atom} {B : Proposition Atom} :
    T.Derivation Γ B → (T.subst f).Derivation (Γ.subst f) (B >>= f)
  | ax h => ax <| Set.mem_image_of_mem (· >>= f) h
  | ass h => ass <| Finset.mem_image_of_mem (· >>= f) h
  | impI _ D => impI _ <| (Finset.image_insert (· >>= f) _ _) ▸ (D.substAtom f)
  | impE D E => impE (D.substAtom f) (E.substAtom f)
  | botE D => botE (D.substAtom f)

theorem DerivableIn.substAtom {Atom Atom' : Type u} [DecidableEq Atom] [DecidableEq Atom']
    {T : Theory Atom}
    (f : Atom → Proposition Atom') {Γ : Ctx Atom} {B : Proposition Atom} :
    DerivableIn T (Γ ⊢ B) → DerivableIn (T.subst f) ((Γ.subst f) ⊢ (B >>= f))
  | ⟨D⟩ => ⟨D.substAtom f⟩

/-! ### Properties of equivalence -/

/-- A derivation of the canonical tautology. -/
def Theory.derivationTop : T⇓(⊤ : Proposition Atom) :=
  impI ∅ <| ass <| by grind

theorem derivableIn_top : DerivableIn T (⊤ : Proposition Atom) := ⟨derivationTop⟩

theorem derivable_iff_equiv_top (A : Proposition Atom) :
    DerivableIn T A ↔ A ≡[T] ⊤ := by
  constructor <;> intro h
  · refine ⟨derivationTop.weakCtx <| by grind, ?_⟩
    let D := Classical.choice h
    exact D.weakCtx <| by grind
  · have := DerivableIn.cut (derivableIn_top (T := T)) (B := A) (Δ := ∅)
    rw [←show (∅ : Ctx Atom) = ∅ ∪ ∅ by rfl] at this
    exact this h.mpr

namespace Theory

/-- Change the conclusion along an equivalence. -/
def mapEquivConclusion (Γ : Ctx Atom) {A B : Proposition Atom} (e : T.equiv A B)
    (D : T⇓(Γ ⊢ A)) : T⇓(Γ ⊢ B) :=
  Γ.union_empty ▸ Derivation.cut (Δ := ∅) D e.1

/-- Replace a hypothesis along an equivalence. -/
def mapEquivHypothesis (Γ : Ctx Atom) {A B : Proposition Atom} (e : T.equiv A B)
    (C : Proposition Atom) (D : T⇓(insert A Γ ⊢ C)) : T⇓(insert B Γ ⊢ C) := by
  have : insert B Γ = {B} ∪ Γ := rfl
  exact this ▸ Derivation.cut e.2 D

/-- An equivalence of a proposition with itself. -/
def equiv.refl (A : Proposition Atom) : T.equiv A A :=
  let D : T⇓({A} ⊢ A) := ass <| Finset.mem_singleton_self A;
  ⟨D, D⟩

/-- Reverse an equivalence. -/
def equiv.symm {A B : Proposition Atom} (e : T.equiv A B) : T.equiv B A :=
  ⟨e.mpr, e.mp⟩

/-- Compose two equivalences. -/
def equiv.trans {A B C : Proposition Atom} (eAB : T.equiv A B)
    (eBC : T.equiv B C) : T.equiv A C :=
  ⟨mapEquivConclusion _ eBC eAB.mp, mapEquivConclusion _ eAB.symm eBC.mpr⟩

/-- `A` and `B` are equivalent (in `T`) iff they are provable from the same contexts. -/
theorem equiv_iff_equiv_derivableIn {A B : Proposition Atom} :
    A ≡[T] B ↔ ∀ Γ : Ctx Atom, DerivableIn T (Γ ⊢ A) ↔ DerivableIn T (Γ ⊢ B) := by
  constructor
  · intro ⟨e⟩ Γ
    exact ⟨fun D => mapEquivConclusion Γ e D.some, fun D => mapEquivConclusion Γ e.symm D.some⟩
  · intro h
    rw [equiv_iff]
    constructor
    · exact (h {A}).mp ⟨ass <| by grind⟩
    · exact (h {B}).mpr ⟨ass <| by grind⟩

/-- `A` and `B` are equivalent (in `T`) iff they have the same strength as hypotheses. -/
theorem equiv_iff_equiv_derivableIn_hypothesis {A B : Proposition Atom} :
    A ≡[T] B ↔
      ∀ (Γ : Ctx Atom) (C : Proposition Atom),
      DerivableIn T ((insert A Γ) ⊢ C) ↔ DerivableIn T ((insert B Γ) ⊢ C) := by
  constructor
  · intro ⟨e⟩ Γ C
    exact ⟨fun D => mapEquivHypothesis Γ e C D.some, fun E => mapEquivHypothesis Γ e.symm C E.some⟩
  · intro h
    rw [equiv_iff]
    constructor
    · exact (h ∅ B).mpr ⟨ass <| by grind⟩
    · exact (h ∅ A).mp ⟨ass <| by grind⟩

@[refl]
theorem Equiv.refl {T : Theory Atom} (A : Proposition Atom) : A ≡[T] A := by
  exact ⟨equiv.refl A⟩

theorem Equiv.symm {T : Theory Atom} {A B : Proposition Atom} :
    (A ≡[T] B) → B ≡[T] A
  | ⟨e⟩ => ⟨e.symm⟩

theorem Equiv.trans {T : Theory Atom} {A B C : Proposition Atom} :
    (A ≡[T] B) → (B ≡[T] C) → A ≡[T] C
  | ⟨e⟩, ⟨e'⟩ => ⟨e.trans e'⟩

/-- Equivalence is indeed an equivalence relation. -/
theorem equiv_equivalence (T : Theory Atom) : Equivalence (T.Equiv (Atom := Atom)) :=
  ⟨Equiv.refl, Equiv.symm, Equiv.trans⟩

/-- The setoid of propositions under equivalence. -/
protected def propositionSetoid (T : Theory Atom) : Setoid (Proposition Atom) :=
  ⟨T.Equiv, T.equiv_equivalence⟩

end Cslib.Logic.PL.Theory
