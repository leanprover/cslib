/-
Copyright (c) 2025 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/
import Cslib.Logics.Propositional.Defs
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.SDiff

/-!
# Gentzen's NJ

Natural deduction for propositional logic. We define deduction trees (a `Type`) for minimal logic,
and derivability (a `Prop`) is relative to a *theory* (set of propositions). Intuitionistic and
classical derivability are obtained by adding (respectively) the principles of explosion and
double negation elimination to minimal logic.

## Main definitions

- `Proposition` : a type of propositions with atoms in a given type.
- `Derivation` :  natural deduction derivation, done in "sequent style", ie with explicit
hypotheses at each step. Contexts are `Finset`'s of propositions, which avoids explicit contraction
and exchange, and the axiom rule derives `{A} ∪ Γ ⊢ A` for any context `Γ`, allowing weakening to
be a derived rule.
- `Theory` : a theory is an arbitrary set of propositions.
- `Theory.Derivable` : a proposition `A` is derivable from a theory `T` if there is a derivation of
`Γ ⊢ A` for some context `Γ ⊆ T`.
- `Theory.SDerivable` : a sequent `Γ ⊢ A` is derivable from a theory `T` if there is a derivation
of `Γ' ⊢ A` for some context `Γ' ⊆ Γ ∪ T`.
- `Proposition.equiv` : `Type`-valued equivalence of propositions.
- `Theory.Equiv` : `Prop`-valued equivalence of propositions, conditional on a theory `T`.
- Unconditional versions of `Derivable`, `SDerivable` and `Equiv` are abbreviations for the relevant
concept relative to the empty theory.

## Main results

- `Derivation.weak` : weakening as a derived rule.
- `Derivation.subs` : substituting a derivation for a hypothesis.
- `Theory.equiv_equivalence` : equivalence of propositions is an equivalence.
- We also give deduction rules for derivability, and equivalent conditions for the unconditional
versions of `Derivable`, `SDerivable` and `Equiv`.

## Notation

We introduce notation for logical connectives `⊥ ⊤ ⋏ ⋎ ⟶ ~` for, respectively, falsum, verum,
conjunction, disjunction, implication and negation. For `T`-derivability, -sequent-derivability and
-equivalence we have `⊢[T] A`, `Γ ⊢[T] A` and `A ≡[T] B`, respectively.

## References

- Dag Prawitz, *Natural Deduction: a proof-theoretical study*.
- The sequent-style natural deduction I present here doesn't seem to be common, but it is tersely
presented in §10.4 of Troelstra & van Dalen's *Constructivism in Mathematics: an introduction*.
(Suggestions of better references welcome!)
-/

universe u

variable {Atom : Type u} [DecidableEq Atom]

namespace PL

namespace NJ

open Proposition

/-- Contexts are finsets of propositions. -/
abbrev Ctx (Atom) := Finset (Proposition Atom)

/-- Theories are abitrary sets of propositions. -/
abbrev Theory (Atom) := Set (Proposition Atom)

abbrev Theory.empty (Atom) : Theory (Atom) := ∅

def IPL [Bot Atom] : Theory Atom := Set.range (⊥ ⟶ ·)
def CPL [Bot Atom] : Theory Atom :=
  IPL ∪ Set.range (fun (A : Proposition Atom) ↦ ~~A ⟶ A)

class IsIntuitionistic [Bot Atom] (T : Theory Atom) where
  efq (A : Proposition Atom) : (⊥ ⟶ A) ∈ T

class IsClassical [Bot Atom] (T : Theory Atom) where
  efq (A : Proposition Atom) : (⊥ ⟶ A) ∈ T
  dne (A : Proposition Atom) : (~~A ⟶ A) ∈ T

instance instIsIntuitionisticIPL [Bot Atom] : IsIntuitionistic (Atom := Atom) IPL where
  efq A := Set.mem_range.mpr ⟨A, rfl⟩

instance instIsClassicalCPL [Bot Atom] : IsClassical (Atom := Atom) CPL where
  efq A := Set.mem_union_left _ <| Set.mem_range.mpr ⟨A, rfl⟩
  dne A := Set.mem_union_right _ <| Set.mem_range.mpr ⟨A, rfl⟩

omit [DecidableEq Atom] in
theorem instIsIntuitionisticExtention [Bot Atom] {T T' : Theory Atom} [IsIntuitionistic T]
    (h : T ⊆ T') : IsIntuitionistic T' := by grind [IsIntuitionistic]

omit [DecidableEq Atom] in
theorem instIsClassicalExtention [Bot Atom] {T T' : Theory Atom} [IsClassical T] (h : T ⊆ T') :
    IsClassical T' := by grind [IsClassical]

/-- Sequents {A₁, ..., Aₙ} ⊢ B. -/
abbrev Sequent (Atom) := Ctx Atom × Proposition Atom

/-- A derivation of {A₁, ..., Aₙ} ⊢ B demonstrates B using (undischarged) assumptions among Aᵢ. -/
inductive Derivation : Sequent Atom → Type _ where
  /-- Axiom (or assumption) -/
  | ax (Γ : Ctx Atom) (A : Proposition Atom) : Derivation ⟨insert A Γ, A⟩
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

/--
A proposition `A` is derivable from a theory `T` if `Γ ⊢ A` is derivable, for some context
`Γ ⊆ T`.
-/
inductive Theory.Derivable (T : Theory Atom) (A : Proposition Atom) : Prop
  | der (Γ : Ctx Atom) (hΓ : ↑Γ ⊆ T) (D : Derivation ⟨Γ, A⟩) : T.Derivable A

@[inherit_doc]
scoped notation "⊢[" T "]" => Theory.Derivable T

theorem Theory.Derivable.theory_weak (T T' : Theory Atom) (hT : T ⊆ T') (A : Proposition Atom) :
    ⊢[T] A → ⊢[T'] A
  | .der Γ hΓ D => ⟨Γ, fun ⦃_⦄ a_1 => hT (hΓ a_1), D⟩

/-- A sequent `Γ ⊢ A` is derivable from a theory `T` if there is a derivation of `Γ' ⊢ A` for some
`Γ' ⊆ Γ ∪ T`. -/
abbrev Theory.SDerivable (T : Theory Atom) (S : Sequent Atom) := ⊢[T ∪ ↑S.1] S.2

@[inherit_doc]
scoped notation Γ " ⊢[" T "] " A:90 => Theory.SDerivable T ⟨Γ, A⟩

theorem Theory.SDerivable.theory_weak (T T' : Theory Atom) (hT : T ⊆ T') (S : Sequent Atom) :
    T.SDerivable S → T'.SDerivable S
  | .der Γ hΓ D => ⟨Γ, by grind, D⟩

/-- A proposition is derivable if it has a derivation from the empty theory. -/
abbrev Derivable : Proposition Atom → Prop := Theory.empty Atom |>.Derivable

@[inherit_doc]
scoped notation "⊢" A:90 => Derivable A

/-- A sequent is derivable if it has a derivation from the empty theory. -/
abbrev SDerivable : Sequent Atom → Prop := Theory.empty Atom |>.SDerivable

@[inherit_doc]
scoped notation Γ " ⊢ " A:90 => SDerivable ⟨Γ,A⟩

/-- A proposition is derivable iff it has a derivation from the empty context. -/
theorem derivable_iff {A : Proposition Atom} : ⊢A ↔ Nonempty (Derivation ⟨∅, A⟩) := by
  constructor
  · intro ⟨Γ, hΓ, D⟩
    exact Finset.eq_empty_of_forall_notMem hΓ ▸ ⟨D⟩
  · intro ⟨D⟩
    refine ⟨∅, by simp, D⟩

/-- An equivalence between A and B is a derivation of B from A and vice-versa. -/
def Proposition.equiv (A B : Proposition Atom) := Derivation ⟨{A},B⟩ × Derivation ⟨{B},A⟩

/-- `A` and `B` are T-equivalent if `A.impl B` and `B.impl A` are T-derivable. -/
def Theory.Equiv (T : Theory Atom) (A B : Proposition Atom) :=
  ⊢[T] (A ⟶ B) ∧ ⊢[T] (B ⟶ A)

@[inherit_doc] scoped notation A " ≡[" T "] " B:29 => Theory.Equiv T A B

theorem Theory.Equiv.theory_weak (T T' : Theory Atom) (hT : T ⊆ T') (A B : Proposition Atom) :
    A ≡[T] B → A ≡[T'] B
  | ⟨hAB, hBA⟩ => ⟨hAB.theory_weak T T' hT, hBA.theory_weak T T' hT⟩

/-- Two propositions A and B are equivalent if B can be derived from A and vice-versa. -/
abbrev Equiv : Proposition Atom → Proposition Atom → Prop := Theory.empty Atom |>.Equiv

@[inherit_doc]
scoped infix:29 " ≡ " => Equiv

open Derivation

def derivationTop [Inhabited Atom] : Derivation (Atom := Atom) ⟨∅, ⊤⟩ :=
  implI ∅ <| ax (Atom := Atom) ∅ (atom default)

theorem Theory.top_derivable [Inhabited Atom] (T : Theory Atom) : ⊢[T] ⊤ := by
  refine ⟨∅, by simp, derivationTop⟩

theorem top_derivable [Inhabited Atom] : Derivable (Atom := Atom) ⊤ :=
  Theory.top_derivable (Theory.empty Atom)

/-! ### Common proof patterns -/

/-- A convenient reformulation of the axiom rule. -/
def Derivation.ax' {Γ : Ctx Atom} {A : Proposition Atom} (h : A ∈ Γ) : Derivation ⟨Γ,A⟩ := by
  have : Γ = insert A Γ := by grind
  rw [this]
  apply ax

/-- Weakening is a derived rule. -/
def Derivation.weak {Γ : Ctx Atom} {A : Proposition Atom} (Δ : Ctx Atom) :
    (D : Derivation ⟨Γ, A⟩) → Derivation ⟨Γ ∪ Δ, A⟩
  | ax Γ A => (Finset.insert_union A Γ Δ) ▸ ax (Γ ∪ Δ) A
  -- | botE A D => botE A <| D.weak Δ
  | conjI D D' => conjI (D.weak Δ) (D'.weak Δ)
  | conjE₁ D => conjE₁ <| D.weak Δ
  | conjE₂ D => conjE₂ <| D.weak Δ
  | disjI₁ D => disjI₁ <| D.weak Δ
  | disjI₂ D => disjI₂ <| D.weak Δ
  | @disjE _ _ _ A B _ D D' D'' =>
    disjE (D.weak Δ)
      ((Finset.insert_union A Γ Δ) ▸ D'.weak Δ)
      ((Finset.insert_union B Γ Δ) ▸ D''.weak Δ)
  | @implI _ _ A B Γ D => implI (Γ ∪ Δ) <| (Finset.insert_union A Γ Δ) ▸ D.weak Δ
  | implE D D' => implE (D.weak Δ) (D'.weak Δ)

def Derivation.weak' {Γ Δ : Ctx Atom} {A : Proposition Atom} (h : Γ ⊆ Δ) (D : Derivation ⟨Γ, A⟩) :
    Derivation ⟨Δ, A⟩ := Finset.union_sdiff_of_subset h ▸ D.weak (Δ \ Γ)

/-- A sequent is derivable iff it has a derivation. -/
theorem sDerivable_iff {S : Sequent Atom} : SDerivable S ↔ Nonempty (Derivation S) := by
  constructor
  · intro ⟨Γ, hΓ, D⟩
    refine ⟨D.weak' ?_⟩
    simpa using hΓ
  · intro ⟨D⟩
    refine ⟨S.1, by simp, D⟩

theorem Theory.SDerivable.sequent_weak (T : Theory Atom) {Γ Δ : Ctx Atom} {A : Proposition Atom} :
    Γ ⊢[T] A → (Γ ∪ Δ) ⊢[T] A
  | .der Γ' hΓ' D => by refine ⟨Γ' ∪ Δ, ?_, D.weak Δ⟩; trans T ∪ Γ ∪ Δ <;> grind

theorem Theory.SDerivable.sequent_weak' (T : Theory Atom) {Γ Δ : Ctx Atom} {A : Proposition Atom}
    (h_ext : Γ ⊆ Δ) : Γ ⊢[T] A → Δ ⊢[T] A
  | .der Γ' hΓ' D => by refine ⟨Γ' ∪ Δ, ?_, D.weak Δ⟩; trans T ∪ Γ ∪ Δ <;> grind

theorem SDerivable.weak {Γ Δ : Ctx Atom} {A : Proposition Atom} :
    Γ ⊢ A → (Γ ∪ Δ) ⊢ A := by
  apply Theory.SDerivable.sequent_weak

theorem SDerivable.weak' {Γ Δ : Ctx Atom} {A : Proposition Atom} (h_ext : Γ ⊆ Δ) :
    Γ ⊢ A → Δ ⊢ A := by
  apply Theory.SDerivable.sequent_weak'; assumption

/-- Substitution of a derivation `E` for one of the hypotheses in the context `Γ` of `D`. -/
def Derivation.subs {Γ Δ : Ctx Atom} {A B : Proposition Atom}
    (D : Derivation ⟨Γ, B⟩) (E : Derivation ⟨Δ, A⟩) : Derivation ⟨(Γ \ {A}) ∪ Δ, B⟩ := by
  match D with
  | ax _ _ =>
    by_cases B = A
    case pos h =>
      rw [h, Finset.union_comm]
      exact E.weak _
    case neg h =>
      rw [Finset.insert_sdiff_of_notMem (h := Finset.notMem_singleton.mpr h)]
      exact (ax _ B).weak _
  -- | botE _ D => exact botE B <| D.subs E
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

theorem Theory.SDerivable.subs {T : Theory Atom} {Γ Δ : Ctx Atom} {A B : Proposition Atom} :
    Γ ⊢[T] B → Δ ⊢[T] A → ((Γ \ {A}) ∪ Δ) ⊢[T] B
  | .der Γ' hΓ' D, .der Δ' hΔ' E =>
    ⟨Γ' \ {A} ∪ Δ', by grind [Finset.coe_union, Finset.coe_sdiff], D.subs E⟩

def Derivation.subs' {Γ : Ctx Atom} {A B : Proposition Atom}
    (D : Derivation ⟨{A}, B⟩) (E : Derivation ⟨Γ, A⟩) : Derivation ⟨Γ, B⟩ := by
  have : Γ = ({A} \ {A}) ∪ Γ := by grind
  rw [this]
  exact D.subs E

theorem Theory.SDerivable.subs' {T : Theory Atom} {Γ : Ctx Atom} {A B : Proposition Atom} :
    ⊢[T] (A ⟶ B) → Γ ⊢[T] A → Γ ⊢[T] B
  | ⟨Δ, hΔ, E⟩, ⟨Γ', hΓ', D⟩ => by
    refine ⟨Δ ∪ Γ', by grind, ?_⟩
    apply implE (A := A)
    · exact E.weak' (by grind)
    · exact D.weak' (by grind)

theorem SDerivable.subs {Γ Δ : Ctx Atom} {A B : Proposition Atom} :
    Γ ⊢ B → Δ ⊢ A → ((Γ \ {A}) ∪ Δ) ⊢ B := Theory.SDerivable.subs

theorem SDerivable.subs' {Γ : Ctx Atom} {A B : Proposition Atom} :
    ⊢ (A ⟶ B) → Γ ⊢ A → Γ ⊢ B :=
  Theory.SDerivable.subs'

/-! ### Inference rules for derivability -/

/--
The **Deduction theorem**, an implication `A ⟶ B` is derivable iff the sequent `A ⊢ B` is
derivable.
-/
theorem Theory.impl_derivable_iff {T : Theory Atom} {A B : Proposition Atom} :
    ⊢[T] (A ⟶ B) ↔ {A} ⊢[T] B := by
  constructor <;> intro ⟨Γ, h, D⟩
  · refine ⟨insert A Γ, by grind, ?_⟩
    apply Derivation.implE (A := A)
    · exact D.weak' (by grind)
    · exact ax ..
  · refine ⟨Γ \ {A}, by grind [Finset.coe_sdiff], ?_⟩
    apply Derivation.implI
    exact D.weak' (by grind)

theorem Theory.Derivable.ax' {T : Theory Atom} {A : Proposition Atom} (h : A ∈ T) :
  ⊢[T] A := ⟨{A}, by grind, Derivation.ax ∅ A⟩

theorem Theory.Derivable.botE [Bot Atom] {T : Theory Atom} [IsIntuitionistic T]
    (A : Proposition Atom) : ⊢[T] ⊥ → ⊢[T] A
  | ⟨Γ, h, D⟩ => by
    refine ⟨insert (⊥ ⟶ A) Γ, by grind [IsIntuitionistic], ?_⟩
    apply implE (A := ⊥)
    · exact ax ..
    · exact D.weak' (by grind)

theorem Theory.Derivable.dne [Bot Atom] {T : Theory Atom} [IsClassical T] (A : Proposition Atom) :
    ⊢[T] (~~A) → ⊢[T] A
  | ⟨Γ, h, D⟩ => by
    refine ⟨insert (~~A ⟶ A) Γ, by grind [IsClassical], ?_⟩
    apply implE (A := ~~A)
    · exact ax ..
    · exact D.weak' (by grind)

theorem Theory.Derivable.conjI {T : Theory Atom} {A B : Proposition Atom} :
    ⊢[T] A → ⊢[T] B → ⊢[T] (A ⋏ B)
  | ⟨Γ, h, D⟩, ⟨Γ', h', D'⟩ =>
    ⟨Γ ∪ Γ', by grind, Derivation.conjI (D.weak' (by grind)) (D'.weak' (by grind))⟩

theorem Theory.Derivable.conjE₁ {T : Theory Atom} {A B : Proposition Atom} :
    ⊢[T] (A ⋏ B) → ⊢[T] A
  | ⟨Γ, h, D⟩ => ⟨Γ, h, D.conjE₁⟩

theorem Theory.Derivable.conjE₂ {T : Theory Atom} {A B : Proposition Atom} :
    ⊢[T] (A ⋏ B) → ⊢[T] B
  | ⟨Γ, h, D⟩ => ⟨Γ, h, D.conjE₂⟩

theorem Theory.Derivable.disjI₁ {T : Theory Atom} {A B : Proposition Atom} :
    ⊢[T] A → ⊢[T] (A ⋎ B)
  | ⟨Γ, h, D⟩ => ⟨Γ, h, D.disjI₁⟩

theorem Theory.Derivable.disjI₂ {T : Theory Atom} {A B : Proposition Atom} :
    ⊢[T] B → ⊢[T] (A ⋎ B)
  | ⟨Γ, h, D⟩ => ⟨Γ, h, D.disjI₂⟩

theorem Theory.Derivable.disjE {T : Theory Atom} {A B C : Proposition Atom} :
    ⊢[T] (A ⋎ B) → ⊢[T] (A ⟶ C) → ⊢[T] (B ⟶ C) → ⊢[T] C
  | ⟨Γ, h, D⟩, ⟨Δ₁, h₁, E₁⟩, ⟨Δ₂, h₂, E₂⟩ => by
    refine ⟨Γ ∪ Δ₁ ∪ Δ₂, by grind, ?_⟩
    apply Derivation.disjE (A := A) (B := B)
    · exact D.weak' (by grind)
    · apply Derivation.implE (A := A)
      · exact E₁.weak' (by grind)
      · exact Derivation.ax' (by grind)
    · apply Derivation.implE (A := B)
      · exact E₂.weak' (by grind)
      · exact Derivation.ax' (by grind)

theorem Theory.Derivable.implE {T : Theory Atom} {A B : Proposition Atom} :
    ⊢[T] (A ⟶ B) → ⊢[T] A → ⊢[T] B
  | ⟨Γ₁, h₁, D₁⟩, ⟨Γ₂, h₂, D₂⟩ => by
    refine ⟨Γ₁ ∪ Γ₂, by grind, ?_⟩
    exact Derivation.implE (A := A) (D₁.weak' (by grind)) (D₂.weak' (by grind))

theorem Theory.Derivable.trans {T : Theory Atom} {A B C : Proposition Atom} :
    ⊢[T] (A ⟶ B) → ⊢[T] (B ⟶ C) → ⊢[T] (A ⟶ C)
  | ⟨Γ₁, h₁, D₁⟩, ⟨Γ₂, h₂, D₂⟩ => by
    refine ⟨Γ₁ ∪ Γ₂, by grind, ?_⟩
    apply implI
    apply Derivation.implE (A := B)
    · exact D₂.weak' (by grind)
    · apply Derivation.implE (A := A)
      · exact D₁.weak' (by grind)
      · exact Derivation.ax' (by grind)

/-! ### Properties of NJ-equivalence -/

theorem equiv_iff {A B : Proposition Atom} : A ≡ B ↔ Nonempty (Proposition.equiv A B) := by
  constructor
  · intro ⟨hAB, hBA⟩
    let ⟨DAB⟩ := derivable_iff.mp hAB
    let ⟨DBA⟩ := derivable_iff.mp hBA
    refine ⟨?_,?_⟩
    · refine Derivation.implE (DAB.weak' (by grind)) (ax' <| by grind)
    · refine Derivation.implE (DBA.weak' (by grind)) (ax' <| by grind)
  · intro ⟨DAB, DBA⟩
    refine ⟨?_,?_⟩
    all_goals apply derivable_iff.mpr; constructor; apply implI; assumption

theorem Proposition.derivable_iff_equiv_top [Inhabited Atom] (T : Theory Atom)
    (A : Proposition Atom) : ⊢[T] A ↔ A ≡[T] ⊤ := by
  constructor <;> intro h
  · constructor
    · refine ⟨∅, by grind, ?_⟩
      exact implI (A := A) (B := ⊤) ∅ <| derivationTop.weak' (by grind)
    · let ⟨Γ, hΓ, D⟩ := h
      refine ⟨Γ, by grind, ?_⟩
      refine implI Γ <| D.weak' (by grind)
  · let ⟨Γ, hΓ, D⟩ := h.2
    refine ⟨Γ, by grind, ?_⟩
    exact implE (A := ⊤) D <| derivationTop.weak' (by grind)

/-- Change the conclusion along an equivalence. -/
def mapEquivConclusion (Γ : Ctx Atom) {A B : Proposition Atom} (e : Proposition.equiv A B) :
    Derivation ⟨Γ, A⟩ → Derivation ⟨Γ, B⟩ := e.1.subs'

theorem Theory.equivalent_derivable {T : Theory Atom} {A B : Proposition Atom} (h : A ≡[T] B) :
    ⊢[T] A ↔ ⊢[T] B := by
  let ⟨⟨Γ₁, hΓ₁, D₁⟩, ⟨Γ₂, hΓ₂, D₂⟩⟩ := h
  constructor
  · intro ⟨Γ, h, D⟩
    refine ⟨Γ ∪ Γ₁, by grind, ?_⟩
    apply implE (A := A)
    · exact D₁.weak' (by grind)
    · exact D.weak' (by grind)
  · intro ⟨Γ, h, D⟩
    refine ⟨Γ ∪ Γ₂, by grind, ?_⟩
    apply implE (A := B)
    · exact D₂.weak' (by grind)
    · exact D.weak' (by grind)

theorem Theory.equivalent_sDerivable_conclusion {T : Theory Atom} (Γ : Ctx Atom)
    {A B : Proposition Atom} (h : A ≡[T] B) : Γ ⊢[T] A ↔ Γ ⊢[T] B := by
  let ⟨⟨Γ₁, hΓ₁, D₁⟩, ⟨Γ₂, hΓ₂, D₂⟩⟩ := h
  constructor <;> intro ⟨Γ', hΓ, D⟩
  · refine ⟨Γ₁ ∪ Γ', by grind, ?_⟩
    apply implE (A := A)
    · exact D₁.weak' (by grind)
    · exact D.weak' (by grind)
  · refine ⟨Γ₂ ∪ Γ', by grind, ?_⟩
    apply implE (A := B)
    · exact D₂.weak' (by grind)
    · exact D.weak' (by grind)

theorem equivalent_sDerivable_conclusion (Γ : Ctx Atom) {A B : Proposition Atom} (h : A ≡ B) :
    Γ ⊢ A ↔ Γ ⊢ B :=
  (Theory.empty Atom).equivalent_sDerivable_conclusion Γ h

/-- Replace a hypothesis along an equivalence. -/
def mapEquivHypothesis (Γ : Ctx Atom) {A B : Proposition Atom} (e : Proposition.equiv A B)
    (C : Proposition Atom) (D : Derivation ⟨insert A Γ, C⟩) : Derivation ⟨insert B Γ, C⟩ := by
  have : insert B Γ = (insert A Γ \ {A}) ∪ (insert B Γ) := by grind
  rw [this]
  refine D.subs ?_
  exact e.2.weak' (by grind)

theorem equivalent_hypotheses {T : Theory Atom} (Γ : Ctx Atom) {A B : Proposition Atom}
    (h : A ≡[T] B) (C : Proposition Atom) :
    (insert A Γ) ⊢[T] C ↔ (insert B Γ) ⊢[T] C := by
  let ⟨⟨Γ₁, hΓ₁, D₁⟩, ⟨Γ₂, hΓ₂, D₂⟩⟩ := h
  constructor <;> intro h'
  · have : insert B Γ = (insert A Γ \ {A}) ∪ (insert B Γ) := by grind
    rw [this]
    apply h'.subs
    refine ⟨insert B Γ₁ ∪ Γ₂, by grind, ?_⟩
    apply implE (A := B)
    · exact D₂.weak' (by grind)
    · exact ax' (by grind)
  · have : insert A Γ = (insert B Γ \ {B}) ∪ (insert A Γ) := by grind
    rw [this]
    apply h'.subs
    refine ⟨insert A Γ₂ ∪ Γ₁, by grind, ?_⟩
    apply implE (A := A)
    · exact D₁.weak' (by grind)
    · exact ax' (by grind)

def reflEquiv (A : Proposition Atom) : Proposition.equiv A A :=
  let D : Derivation ⟨{A},A⟩ := ax' <| by grind;
  ⟨D,D⟩

def commEquiv {A B : Proposition Atom} (e : Proposition.equiv A B) : Proposition.equiv B A :=
  ⟨e.2, e.1⟩

def transEquiv {A B C : Proposition Atom} (eAB : Proposition.equiv A B)
    (eBC : Proposition.equiv B C) : Proposition.equiv A C :=
  ⟨mapEquivConclusion _ eBC eAB.1, mapEquivConclusion _ (commEquiv eAB) eBC.2⟩

theorem equivalent_refl {T : Theory Atom} (A : Proposition Atom) : A ≡[T] A := by
  have : T.Derivable (A ⟶ A) := by refine ⟨∅, by grind, ?_⟩; apply implI; exact ax' (by grind)
  grind [Theory.Equiv]

theorem equivalent_comm {T : Theory Atom} {A B : Proposition Atom} :
    A ≡[T] B → B ≡[T] A := by grind [Theory.Equiv]

theorem equivalent_trans {T : Theory Atom} {A B C : Proposition Atom} :
    A ≡[T] B → B ≡[T] C → A ≡[T] C
  | ⟨AB, BA⟩, ⟨BC, CB⟩ => ⟨AB.trans BC, CB.trans BA⟩

/-- Equivalence is indeed an equivalence relation. -/
theorem Theory.equiv_equivalence (T : Theory Atom) : Equivalence (T.Equiv (Atom := Atom)) :=
  ⟨equivalent_refl, equivalent_comm, equivalent_trans⟩

protected def Theory.propositionSetoid (T : Theory Atom) : Setoid (Proposition Atom) :=
  ⟨T.Equiv, T.equiv_equivalence⟩

end NJ

end PL
