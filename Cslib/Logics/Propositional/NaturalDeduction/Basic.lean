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

/-! # Natural deduction for propositional logic

We define, for intuitionistic logic, deduction trees (a `Type`) and derivability (a `Prop`)
relative to a set of axioms.

## Main definitions

- `Sequent` : a pair of a context and conclusion.
- `Derivation` : natural deduction derivation, done in "sequent style", ie with explicit
hypotheses at each step. Contexts are `Finset`'s of propositions, which avoids explicit contraction
and exchange, and the axiom rule derives `Γ ⊢ A` for any context `Γ` with `A ∈ Γ`, allowing
weakening to be a derived rule. The derivation may appeal to hypotheses from the
`T : Set (Proposition Atom)`.
- `ND T`, `ND₁ T` : two inference systems, on `Sequent Atom` and `Proposition Atom` respectively,
corresponding to `Derivation T` and `Derivation T ∅`.
- `equiv` : `Type`-valued equivalence of propositions.
- `Equiv` : `Prop`-valued equivalence of propositions.

## Main results

- `Derivation.weak` : weakening as a derived rule.
- `Derivation.cut`, `Derivation.subs` : replace a hypothesis in a derivation — the two versions
differ in the construction of the relevant derivation.
- `equiv_equivalence` : equivalence of propositions is an equivalence relation.

## Notation

The sequent `⟨Γ, A⟩` is notated `Γ ⊢ A`, so that a derivation using axioms from a set `T` is
noted `(ND T)⇓(Γ ⊢ A)`. We define also an `InferenceSystem (ND₁ T) (Proposition Atom)`, so that
`(ND₁ T)⇓A` abbreviates a derivation of `A` in the empty context: `(ND T)⇓(∅ ⊢ A)`.

## Implementation notes

We formalise here a single type of derivations, meaning there is a single collection of inference
rules (those for intuitionistic logic). The extension to classical logic (indeed any extension of
intuitionistic logic) is modelled by adding *axioms* --- in this case, classical derivations can
appeal to axioms of the form `¬¬A → A`, for any proposition `A`. This differs from many on-paper
presentations, which might, for instance, add instead an inference rule corresponding to proof by
contraduction. Discussion on the proper way to capture such developments in cslib is ongoing, see
the following
[zulip discussion](https://leanprover.zulipchat.com/#narrow/channel/513188-CSLib/topic/Logic/with/585843520).

## References

- [J. Avigad, *Mathematical Logic and Computation*][Avigad2022]
- [D. Prawitz, *Natural Deduction: A Proof-Theoretical Study*][Prawitz1965]
- The sequent-style natural deduction presented here doesn't seem to be common, but it is tersely
presented in §10.4 of
[A. S. Troelstra, D. van Dalen, *Constructivism in Mathematics*][TroelstraVanDalen1988], and
in §2.2 of
[M. H. Sorensen, P. Urzyczyn's *Lectures on the Curry-Howard Isomorphism*][SorensenUrzyczyn2006].
-/

@[expose] public section

universe u

namespace Cslib.Logic.PL

open Proposition InferenceSystem DerivableIn

namespace NaturalDeduction

variable {Atom : Type u} [DecidableEq Atom]

/-- Contexts are finsets of propositions. -/
abbrev Ctx (Atom) := Finset (Proposition Atom)

/-- Map a context along a substitution. -/
def Ctx.subst {Atom Atom' : Type*} [DecidableEq Atom'] (f : Atom → Proposition Atom') :
    Ctx Atom → Ctx Atom' := Finset.image (·.subst f)

/-- Sequents \{A₁, ..., Aₙ\} ⊢ B. -/
abbrev Sequent {Atom} := Ctx Atom × Proposition Atom

@[inherit_doc Sequent]
scoped notation Γ:60 " ⊢ " A => (⟨Γ, A⟩ : Sequent)

/-- A `T`-derivation of \{A₁, ..., Aₙ\} ⊢ B demonstrates B using (undischarged) assumptions
among Aᵢ, possibly appealing to axioms from `T`. -/
inductive Derivation (T : Set (Proposition Atom)) : Ctx Atom → Proposition Atom → Type u where
  /-- Axiom -/
  | ax {Γ : Ctx Atom} {A : Proposition Atom} (_ : A ∈ T) : Derivation T Γ A
  /-- Assumption -/
  | ass {Γ : Ctx Atom} {A : Proposition Atom} (_ : A ∈ Γ) : Derivation T Γ A
  /-- Ex falso quodlibet. -/
  | efq {Γ : Ctx Atom} (A : Proposition Atom) : Derivation T Γ ⊥ → Derivation T Γ A
  /-- Conjunction introduction -/
  | andI {Γ : Ctx Atom} {A B : Proposition Atom} :
      Derivation T Γ A → Derivation T Γ B → Derivation T Γ (A ∧ B)
  /-- Conjunction elimination left -/
  | andE₁ {Γ : Ctx Atom} {A B : Proposition Atom} : Derivation T Γ (A ∧ B) → Derivation T Γ A
  /-- Conjunction elimination right -/
  | andE₂ {Γ : Ctx Atom} {A B : Proposition Atom} : Derivation T Γ (A ∧ B) → Derivation T Γ B
  /-- Disjunction introduction left -/
  | orI₁ {Γ : Ctx Atom} {A B : Proposition Atom} : Derivation T Γ A → Derivation T Γ (A ∨ B)
  /-- Disjunction introduction right -/
  | orI₂ {Γ : Ctx Atom} {A B : Proposition Atom} : Derivation T Γ B → Derivation T Γ (A ∨ B)
  /-- Disjunction elimination -/
  | orE {Γ : Ctx Atom} {A B C : Proposition Atom} : Derivation T Γ (A ∨ B) →
      Derivation T (insert A Γ) C → Derivation T (insert B Γ) C → Derivation T Γ C
  /-- Implication introduction -/
  | impI {A B : Proposition Atom} (Γ : Ctx Atom) :
      Derivation T (insert A Γ) B → Derivation T Γ (A → B)
  /-- Implication elimination -/
  | impE {Γ : Ctx Atom} {A B : Proposition Atom} :
      Derivation T Γ (A → B) → Derivation T Γ A → Derivation T Γ B

/-- Type tag for natural deduction derivations from axioms `T`. -/
opaque ND (T : Set (Proposition Atom)) : Type := Empty

/-- Inference system for derivations under the theory `T`. -/
instance (T : Set (Proposition Atom)) : InferenceSystem (ND T) (Sequent (Atom := Atom)) where
  derivation S := Derivation T S.1 S.2

/-- Type tag for natural deduction derivations of single propositions from axioms `T`. -/
opaque ND₁ (T : Set (Proposition Atom)) : Type := Empty

/-- Inference system for propositions (using the empty context). -/
instance (T : Set (Proposition Atom)) : InferenceSystem (ND₁ T) (Proposition Atom) where
  derivation A := Derivation T ∅ A

variable {T : Set (Proposition Atom)}

theorem Derivation.emptySequent_eq {A : Proposition Atom} : (ND₁ T)⇓A = (ND T)⇓(∅ ⊢ A) := rfl

theorem _root_.Cslib.Logic.InferenceSystem.DerivableIn.nd₁_iff_derivableIn_nd_empty
  {A : Proposition Atom} : DerivableIn (ND₁ T) A ↔ DerivableIn (ND T) (∅ ⊢ A) := by rfl

/-- An equivalence between A and B is a derivation of B from A and vice-versa. -/
structure equiv (T : Set (Proposition Atom)) (A B : Proposition Atom) where
  /-- The forward direction of the equivalence. -/
  mp : (ND T)⇓({A} ⊢ B)
  /-- The reverse direction of the equivalence. -/
  mpr : (ND T)⇓({B} ⊢ A)

/-- `A` and `B` are T-equivalent if `T.equiv A B` is nonempty. -/
def Equiv (T : Set (Proposition Atom)) (A B : Proposition Atom) := Nonempty (equiv T A B)

@[inherit_doc]
scoped notation A " ≡[" T' "] " B:29 => Equiv T' A B

lemma Equiv.mp {A B : Proposition Atom} (h : A ≡[T] B) : DerivableIn (ND T) ({A} ⊢ B) :=
  ⟨h.some.mp⟩

lemma Equiv.mpr {A B : Proposition Atom} (h : A ≡[T] B) : DerivableIn (ND T) ({B} ⊢ A) :=
  ⟨h.some.mpr⟩

theorem equiv_iff {A B : Proposition Atom} :
  A ≡[T] B ↔ DerivableIn (ND T) ({A} ⊢ B) ∧ DerivableIn (ND T) ({B} ⊢ A) := by
  constructor
  · intro h
    exact ⟨h.mp, h.mpr⟩
  · intro ⟨⟨D⟩, ⟨E⟩⟩
    exact ⟨D, E⟩

open Derivation DerivableIn

/-! ### Operations on derivations -/

/-- Weakening is a derived rule. -/
def Derivation.weak {T T' : Set (Proposition Atom)} {Γ Δ : Ctx Atom} {A : Proposition Atom}
    (hTheory : T ⊆ T') (hCtx : Γ ⊆ Δ) : Derivation T Γ A → Derivation T' Δ A
  | ax hA => ax <| hTheory hA
  | ass hA => ass <| hCtx hA
  | efq A D => efq A (D.weak hTheory hCtx)
  | andI D D' => andI (D.weak hTheory hCtx) (D'.weak hTheory hCtx)
  | andE₁ D => andE₁ <| D.weak hTheory hCtx
  | andE₂ D => andE₂ <| D.weak hTheory hCtx
  | orI₁ D => orI₁ <| D.weak hTheory hCtx
  | orI₂ D => orI₂ <| D.weak hTheory hCtx
  | orE D D' D'' =>
    orE (D.weak hTheory hCtx)
      (D'.weak hTheory <| Finset.insert_subset_insert _ hCtx)
      (D''.weak hTheory <| Finset.insert_subset_insert _ hCtx)
  | @impI _ _ _ A B Γ D => impI (Δ) <| D.weak hTheory <| Finset.insert_subset_insert _ hCtx
  | impE D D' => impE (D.weak hTheory hCtx) (D'.weak hTheory hCtx)

/-- Weakening the axioms only. -/
def Derivation.weakTheory {T T' : Set (Proposition Atom)} {Γ : Ctx Atom} {A : Proposition Atom}
    (hTheory : T ⊆ T') : (ND T)⇓(Γ ⊢ A) → (ND T')⇓(Γ ⊢ A):=
  Derivation.weak hTheory Finset.Subset.rfl

/-- Weakening the context only. -/
def Derivation.weakCtx {T : Set (Proposition Atom)} {Γ Δ : Ctx Atom} {A : Proposition Atom}
    (hCtx : Γ ⊆ Δ) : (ND T)⇓(Γ ⊢ A) → (ND T)⇓(Δ ⊢ A) :=
  Derivation.weak Set.Subset.rfl hCtx

/-- Proof irrelevant weakening. -/
theorem _root_.Cslib.Logic.InferenceSystem.DerivableIn.weak {T T' : Set (Proposition Atom)}
    {Γ Δ : Ctx Atom} {A : Proposition Atom} (hTheory : T ⊆ T') (hCtx : Γ ⊆ Δ) :
    DerivableIn (ND T) (Γ ⊢ A) → DerivableIn (ND T') (Δ ⊢ A)
  | ⟨D⟩ => ⟨D.weak hTheory hCtx⟩

/-- Proof irrelevant weakening of the axiom set. -/
theorem _root_.Cslib.Logic.InferenceSystem.DerivableIn.weakTheory {T T' : Set (Proposition Atom)}
    {Γ : Ctx Atom} {A : Proposition Atom} (hTheory : T ⊆ T') (h : DerivableIn (ND T) (Γ ⊢ A)) :
    DerivableIn (ND T') (Γ ⊢ A) := h.weak hTheory Finset.Subset.rfl

/-- Proof irrelevant weakening of the context. -/
theorem _root_.Cslib.Logic.InferenceSystem.DerivableIn.weakCtx {T : Set (Proposition Atom)}
    {Γ Δ : Ctx Atom} {A : Proposition Atom} (hCtx : Γ ⊆ Δ) (h : DerivableIn (ND T) (Γ ⊢ A)) :
    DerivableIn (ND T) (Δ ⊢ A) :=
  h.weak Set.Subset.rfl hCtx

/--
Implement the cut rule, removing a hypothesis `A` from `E` using a derivation `D`. This is *not*
substitution, which would replace appeals to `A` in `E` by the whole derivation `D`.
-/
def Derivation.cut {Γ Δ : Ctx Atom} {A B : Proposition Atom}
    (D : (ND T)⇓(Γ ⊢ A)) (E : (ND T)⇓(insert A Δ ⊢ B)) : (ND T)⇓((Γ ∪ Δ) ⊢ B) := by
  refine impE (A := A) ?_ (D.weakCtx Finset.subset_union_left)
  have : insert A Δ ⊆ insert A (Γ ∪ Δ) := by grind
  exact impI (Γ ∪ Δ) <| E.weakCtx this

/-- Proof irrelevant cut rule. -/
theorem _root_.Cslib.Logic.InferenceSystem.DerivableIn.cut {Γ Δ : Ctx Atom}
    {A B : Proposition Atom} :
    DerivableIn (ND T) (Γ ⊢ A) → DerivableIn (ND T) ((insert A Δ) ⊢ B) →
      DerivableIn (ND T) ((Γ ∪ Δ) ⊢ B)
  | ⟨D⟩, ⟨E⟩ => ⟨D.cut E⟩

/-- Remove unnecessary hypotheses. This can't be computable because it requires picking an order
on the finset `Δ`. -/
theorem _root_.Cslib.Logic.InferenceSystem.DerivableIn.cut_away {Γ Γ' : Ctx Atom}
    {B : Proposition Atom} (hΔ : ∀ A ∈ Γ', DerivableIn (ND T) (Γ ⊢ A))
    (hDer : DerivableIn (ND T) ((Γ ∪ Γ') ⊢ B)) : DerivableIn (ND T) (Γ ⊢ B) := by
  induction Γ' using Finset.induction with
  | empty => exact hDer.weakCtx (by grind)
  | insert A Δ hA ih =>
    apply ih
    · intro A' hA'
      exact hΔ A' <| Finset.mem_insert_of_mem hA'
    · apply Finset.union_left_idem Γ Δ ▸ DerivableIn.cut (Δ := Γ ∪ Δ)
      · exact hΔ A <| Finset.mem_insert_self A Δ
      · rwa [← Finset.union_insert A Γ Δ]

/-- Substitution of a family of derivations `D` for hypotheses in the context `Γ` of `E`. TODO:
this implementation is not capture avoiding. -/
def Derivation.subs {Γ Γ' Δ : Ctx Atom} {B : Proposition Atom}
    (Ds : ∀ A ∈ Γ', (ND T)⇓(Δ ⊢ A)) :
      Derivation T Γ B → Derivation T (Γ \ Γ' ∪ Δ) B
  | ax hB => ax hB
  | @ass _ _ _ _ B hB => by
    by_cases B ∈ Γ'
    case pos h =>
      exact (Ds B h).weakCtx <| by grind
    case neg h =>
      exact ass <| by grind
  | efq A D => efq A (D.subs Ds)
  | andI E E' => andI (E.subs Ds) (E'.subs Ds)
  | andE₁ E => andE₁ <| E.subs Ds
  | andE₂ E => andE₂ <| E.subs Ds
  | orI₁ E => orI₁ <| E.subs Ds
  | orI₂ E => orI₂ <| E.subs Ds
  | @orE _ _ _ _ C C' _ E E' E'' .. => by
    apply orE (E.subs Ds)
    · rw [show insert C (Γ \ Γ' ∪ Δ) = (insert C Γ \ Γ') ∪ insert C Δ by grind]
      exact E'.subs Ds |>.weakCtx (by grind)
    · rw [show insert C' (Γ \ Γ' ∪ Δ) = (insert C' Γ \ Γ') ∪ insert C' Δ by grind]
      exact E''.subs Ds |>.weakCtx (by grind)
  | @impI _ _ _ A' _ _ E .. => by
    apply impI
    rw [show insert A' (Γ \ Γ' ∪ Δ) = (insert A' Γ \ Γ') ∪ insert A' Δ by grind]
    exact E.subs Ds |>.weakCtx (by grind)
  | impE E E' => impE (E.subs Ds) (E'.subs Ds)

/-- Transport a derivation along a substitution of atoms. -/
def Derivation.substAtom {Atom Atom' : Type*} [DecidableEq Atom] [DecidableEq Atom']
    {T : Set (Proposition Atom)} (f : Atom → Proposition Atom') {Γ : Ctx Atom}
    {B : Proposition Atom} :
    Derivation T Γ B → Derivation ((·.subst f) '' T) (Γ.subst f) (B.subst f)
  | ax h => ax <| Set.mem_image_of_mem (·.subst f) h
  | ass h => ass <| Finset.mem_image_of_mem (·.subst f) h
  | efq _ D => efq _ (D.substAtom f)
  | andI D E => andI (D.substAtom f) (E.substAtom f)
  | andE₁ D => andE₁ (D.substAtom f)
  | andE₂ D => andE₂ (D.substAtom f)
  | orI₁ D => orI₁ (D.substAtom f)
  | orI₂ D => orI₂ (D.substAtom f)
  | @orE _ _ _ _ A B C D E E' => orE (D.substAtom f)
    ((Finset.image_insert (·.subst f) A Γ) ▸ E.substAtom f)
    ((Finset.image_insert (·.subst f) B Γ) ▸ E'.substAtom f)
  | @impI _ _ _ A _ Γ D => impI _ <| (Finset.image_insert (·.subst f) A Γ) ▸ (D.substAtom f)
  | impE D E => impE (D.substAtom f) (E.substAtom f)

theorem _root_.Cslib.Logic.InferenceSystem.DerivableIn.substAtom {Atom Atom' : Type u}
    [DecidableEq Atom] [DecidableEq Atom'] {T : Set (Proposition Atom)}
    (f : Atom → Proposition Atom') {Γ : Ctx Atom} {B : Proposition Atom} :
    DerivableIn (ND T) (Γ ⊢ B) → DerivableIn (ND <| (·.subst f) '' T) ((Γ.subst f) ⊢ (B >>= f))
  | ⟨D⟩ => ⟨D.substAtom f⟩

/-! ### Properties of equivalence -/

/-- A derivation of the canonical tautology. -/
def derivationTop : (ND₁ T)⇓(⊤ : Proposition Atom) :=
  impI ∅ <| ass <| by grind

theorem derivableIn_top : DerivableIn (ND₁ T) (⊤ : Proposition Atom) := ⟨derivationTop⟩

theorem derivable_iff_equiv_top (A : Proposition Atom) :
    DerivableIn (ND₁ T) A ↔ A ≡[T] ⊤ := by
  constructor <;> intro h
  · refine ⟨derivationTop.weakCtx <| by grind, ?_⟩
    let D := Classical.choice h
    exact D.weakCtx <| by grind
  · have := DerivableIn.cut (derivableIn_top (T := T)) (B := A) (Δ := ∅)
    rw [←show (∅ : Ctx Atom) = ∅ ∪ ∅ by rfl] at this
    exact this h.mpr

alias ⟨_root_.Cslib.Logic.InferenceSystem.DerivableIn.equiv_top, _⟩ := derivable_iff_equiv_top

/-- Change the conclusion along an equivalence. -/
def mapEquivConclusion (Γ : Ctx Atom) {A B : Proposition Atom} (e : equiv T A B)
    (D : (ND T)⇓(Γ ⊢ A)) : (ND T)⇓(Γ ⊢ B) :=
  Γ.union_empty ▸ Derivation.cut (Δ := ∅) D e.1

/-- Replace a hypothesis along an equivalence. -/
def mapEquivHypothesis (Γ : Ctx Atom) {A B : Proposition Atom} (e : equiv T A B)
    (C : Proposition Atom) (D : (ND T)⇓(insert A Γ ⊢ C)) : (ND T)⇓(insert B Γ ⊢ C) := by
  have : insert B Γ = {B} ∪ Γ := rfl
  exact this ▸ Derivation.cut e.2 D

/-- An equivalence of a proposition with itself. -/
def equiv.refl (A : Proposition Atom) : equiv T A A :=
  let D : (ND T)⇓({A} ⊢ A) := ass <| Finset.mem_singleton_self A;
  ⟨D, D⟩

/-- Reverse an equivalence. -/
def equiv.symm {A B : Proposition Atom} (e : equiv T A B) : equiv T B A :=
  ⟨e.mpr, e.mp⟩

/-- Compose two equivalences. -/
def equiv.trans {A B C : Proposition Atom} (eAB : equiv T A B)
    (eBC : equiv T B C) : equiv T A C :=
  ⟨mapEquivConclusion _ eBC eAB.mp, mapEquivConclusion _ eAB.symm eBC.mpr⟩

/-- `A` and `B` are equivalent (in `T`) iff they are provable from the same contexts. -/
theorem equiv_iff_equiv_derivableIn {A B : Proposition Atom} :
    A ≡[T] B ↔ ∀ Γ : Ctx Atom, DerivableIn (ND T) (Γ ⊢ A) ↔ DerivableIn (ND T) (Γ ⊢ B) := by
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
      DerivableIn (ND T) ((insert A Γ) ⊢ C) ↔ DerivableIn (ND T) ((insert B Γ) ⊢ C) := by
  constructor
  · intro ⟨e⟩ Γ C
    exact ⟨fun D => mapEquivHypothesis Γ e C D.some, fun E => mapEquivHypothesis Γ e.symm C E.some⟩
  · intro h
    rw [equiv_iff]
    constructor
    · exact (h ∅ B).mpr ⟨ass <| by grind⟩
    · exact (h ∅ A).mp ⟨ass <| by grind⟩

@[refl]
theorem Equiv.refl {T : Set (Proposition Atom)} (A : Proposition Atom) : A ≡[T] A := by
  exact ⟨equiv.refl A⟩

theorem Equiv.symm {T : Set (Proposition Atom)} {A B : Proposition Atom} :
    (A ≡[T] B) → B ≡[T] A
  | ⟨e⟩ => ⟨e.symm⟩

theorem Equiv.trans {T : Set (Proposition Atom)} {A B C : Proposition Atom} :
    (A ≡[T] B) → (B ≡[T] C) → A ≡[T] C
  | ⟨e⟩, ⟨e'⟩ => ⟨e.trans e'⟩

/-- Equivalence is indeed an equivalence relation. -/
theorem equiv_equivalence (T : Set (Proposition Atom)) : Equivalence (Equiv T (Atom := Atom)) :=
  ⟨Equiv.refl, Equiv.symm, Equiv.trans⟩

/-- The setoid of propositions under equivalence. -/
protected def propositionSetoid (T : Set (Proposition Atom)) : Setoid (Proposition Atom) :=
  ⟨Equiv T, equiv_equivalence T⟩

end Cslib.Logic.PL.NaturalDeduction
