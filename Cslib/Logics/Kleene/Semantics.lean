/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

module

public import Cslib.Logics.Kleene.Basic
public import Cslib.Logics.Propositional.NaturalDeduction.Basic
public import Cslib.Foundations.Logic.InferenceSystem.Basic
public import Cslib.Foundations.Logic.Consequence

/-! # Kleene semantics for propositional logic

Propositions of CSLib's propositional logic (`PL.Proposition`) are evaluated in `Kleene.Value` by
the strong truth tables of Kleene's three-valued logic (K3) [Kleene1952]: the falsum `⊥` is
`false`, conjunction is the meet `⊓`, disjunction is the join `⊔`, and `A → B` has the value
`aᶜ ⊔ b`, where `a` and `b` are the values of `A` and `B`. Negation is the defined connective
`¬A := A → ⊥`, and since `aᶜ ⊔ false = aᶜ` it is evaluated as the complement.

## Main definitions

- `Kleene.Valuation`: valuations of atoms in `Kleene.Value`.
- `Kleene.Valuation.eval`: evaluation of a proposition under a valuation.
- `Kleene.Satisfies`, with the notation `⇓K3[v ⊨ A]`: satisfaction.
- `Kleene.Entails`: consequence, the generic notion over all valuations.
- `Kleene.IsBotFree`: the propositions in which `⊥` does not occur.
- `Kleene.K3`: the consequences of no premises, as an inference system on propositions.
- `Kleene.Valuation.IsTwoValued` and `Kleene.ClassicalEntails`: the two-valued valuations, and
  consequence over them.

## Main results

- `Kleene.Valuation.eval_not`: `¬A` evaluates to the complement of the value of `A`.
- `Kleene.Satisfies.and_iff_and` and friends: satisfaction of compound propositions in terms of
  their components.
- `Kleene.entails_of_mem_of_mem_not`: explosion, from `A` and `¬A` together.
- `Kleene.not_entails_of_isBotFree` and `Kleene.entails_bot_imp`: no `⊥`-free proposition follows
  from no premises, while `⊥ → A` does for every `A`.
- `Kleene.not_deduction_theorem`: `A` entails `A`, but `A → A` does not follow from no premises
  for `⊥`-free `A`.
- `IsIntuitionistic Kleene.K3` and `Kleene.not_k3_of_derivableIn_ipl`: explosion is derivable, but
  not every theorem of intuitionistic propositional logic is.
- `Kleene.Entails.classicalEntails` and `Kleene.not_entails_of_classicalEntails`: Kleene
  consequence is strictly sub-classical. Excluded middle separates the two: it holds classically
  for every proposition, and fails in Kleene for every `⊥`-free one.

## References

- [Kleene1952] S. C. Kleene, *Introduction to Metamathematics*, §64.
-/

@[expose] public section

universe u

namespace Cslib.Logic.Kleene

open scoped InferenceSystem Value

variable {Atom : Type u}

/-! ### Valuations and evaluation -/

/-- A valuation assigns a truth value to each atom. -/
abbrev Valuation (Atom : Type u) := Atom → Value

/-- Evaluation of a proposition under a valuation: the falsum as `false`, conjunction as meet,
disjunction as join, and `A → B` as the join of the complement of `A` with `B`. -/
def Valuation.eval (v : Valuation Atom) : PL.Proposition Atom → Value
  | .atom p => v p
  | .falsum => .false
  | .and A B => v.eval A ⊓ v.eval B
  | .or A B => v.eval A ⊔ v.eval B
  | .imp A B => (v.eval A)ᶜ ⊔ v.eval B

@[simp, scoped grind =]
theorem Valuation.eval_atom (v : Valuation Atom) (p : Atom) : v.eval (.atom p) = v p := rfl

@[simp, scoped grind =]
theorem Valuation.eval_bot (v : Valuation Atom) : v.eval ⊥ = .false := rfl

@[simp, scoped grind =]
theorem Valuation.eval_and (v : Valuation Atom) (A B : PL.Proposition Atom) :
    v.eval (A ∧ B) = v.eval A ⊓ v.eval B := rfl

@[simp, scoped grind =]
theorem Valuation.eval_or (v : Valuation Atom) (A B : PL.Proposition Atom) :
    v.eval (A ∨ B) = v.eval A ⊔ v.eval B := rfl

@[simp, scoped grind =]
theorem Valuation.eval_imp (v : Valuation Atom) (A B : PL.Proposition Atom) :
    v.eval (A → B) = (v.eval A)ᶜ ⊔ v.eval B := rfl

/-- The defined negation `¬A := A → ⊥` is evaluated as the complement. -/
@[simp, scoped grind =]
theorem Valuation.eval_not (v : Valuation Atom) (A : PL.Proposition Atom) :
    v.eval (¬A) = (v.eval A)ᶜ := Value.sup_false _

/-! ### Satisfaction -/

/-- `Satisfies v A` means that `A` evaluates to `true` under the valuation `v`. -/
def Satisfies (v : Valuation Atom) (A : PL.Proposition Atom) : Prop := v.eval A = .true

/-- A judgement `K3[v ⊨ A]`, pairing a valuation with a proposition. -/
structure Judgement (Atom : Type u) where
  /-- The valuation. -/
  v : Valuation Atom
  /-- The proposition. -/
  A : PL.Proposition Atom

@[inherit_doc Judgement] scoped notation "K3[" v " ⊨ " A "]" => Judgement.mk v A

instance : HasInferenceSystem (Judgement Atom) := ⟨fun j => Satisfies j.v j.A⟩

@[scoped grind =]
theorem Satisfies.eval_eq_true_iff {v : Valuation Atom} {A : PL.Proposition Atom} :
    ⇓K3[v ⊨ A] ↔ v.eval A = .true := Iff.rfl

@[simp, scoped grind =]
theorem Satisfies.atom_iff {v : Valuation Atom} {p : Atom} :
    ⇓K3[v ⊨ .atom p] ↔ v p = .true := Iff.rfl

@[scoped grind =]
theorem Satisfies.and_iff_and {v : Valuation Atom} {A B : PL.Proposition Atom} :
    ⇓K3[v ⊨ A ∧ B] ↔ ⇓K3[v ⊨ A] ∧ ⇓K3[v ⊨ B] := Value.inf_eq_true_iff

@[scoped grind =]
theorem Satisfies.or_iff_or {v : Valuation Atom} {A B : PL.Proposition Atom} :
    ⇓K3[v ⊨ A ∨ B] ↔ ⇓K3[v ⊨ A] ∨ ⇓K3[v ⊨ B] := Value.sup_eq_true_iff

@[scoped grind =]
theorem Satisfies.imp_iff {v : Valuation Atom} {A B : PL.Proposition Atom} :
    ⇓K3[v ⊨ A → B] ↔ v.eval A = .false ∨ ⇓K3[v ⊨ B] := by
  simp [Satisfies.eval_eq_true_iff]

@[scoped grind =]
theorem Satisfies.not_iff_eval_eq_false {v : Valuation Atom} {A : PL.Proposition Atom} :
    ⇓K3[v ⊨ ¬A] ↔ v.eval A = .false := by
  rw [Satisfies.eval_eq_true_iff, Valuation.eval_not, Value.compl_eq_true_iff]

/-- The converse fails, since `A` may be `unknown`. -/
theorem Satisfies.not_satisfies_of_not {v : Valuation Atom} {A : PL.Proposition Atom}
    (h : ⇓K3[v ⊨ ¬A]) : ¬⇓K3[v ⊨ A] := by
  grind

/-! ### Judgemental contexts -/

/-- A judgemental context is a valuation: the judgement `K3[v ⊨ A]` with the proposition
missing. -/
instance : HasHContext (Judgement Atom) (PL.Proposition Atom) :=
  ⟨fun (v : Valuation Atom) A => K3[v ⊨ A]⟩

@[simp, scoped grind =]
theorem Judgement.fill_def {v : Valuation Atom} {A : PL.Proposition Atom} :
    HasHContext.fill (α := Judgement Atom) v A = K3[v ⊨ A] := rfl

/-! ### Consequence -/

/-- Consequence: every valuation satisfying all the premises satisfies the conclusion. -/
abbrev Entails (Γ : Set (PL.Proposition Atom)) (A : PL.Proposition Atom) : Prop :=
  Cslib.Logic.Entails (Judgement Atom) InferenceSystem.Default Γ A

/-- Explosion: `A` and `¬A` together entail everything, since no valuation satisfies both. -/
theorem entails_of_mem_of_mem_not {Γ : Set (PL.Proposition Atom)} {A : PL.Proposition Atom}
    (h₁ : A ∈ Γ) (h₂ : (¬A) ∈ Γ) (B : PL.Proposition Atom) : Entails Γ B :=
  entailsWithin_of_incompatible h₁ h₂
    (fun _ _ hA hnA => Satisfies.not_satisfies_of_not hnA hA) B

/-! ### Consequence from no premises -/

/-- A proposition is `⊥`-free if the falsum `⊥` does not occur in it. Since `¬A := A → ⊥`, no
negation is `⊥`-free. -/
inductive IsBotFree : PL.Proposition Atom → Prop
  /-- An atom. -/
  | atom (p : Atom) : IsBotFree (.atom p)
  /-- Conjunction. -/
  | and {A B : PL.Proposition Atom} (hA : IsBotFree A) (hB : IsBotFree B) : IsBotFree (A ∧ B)
  /-- Disjunction. -/
  | or {A B : PL.Proposition Atom} (hA : IsBotFree A) (hB : IsBotFree B) : IsBotFree (A ∨ B)
  /-- Implication. -/
  | imp {A B : PL.Proposition Atom} (hA : IsBotFree A) (hB : IsBotFree B) : IsBotFree (A → B)

/-- The valuation sending every atom to `unknown`. -/
def Valuation.unknown : Valuation Atom := fun _ => .unknown

theorem Valuation.eval_unknown {A : PL.Proposition Atom} (h : IsBotFree A) :
    Valuation.unknown.eval A = .unknown := by
  induction h <;> simp [Valuation.unknown, *]

/-- A proposition that is not `true` under `Valuation.unknown` does not follow from no
premises. -/
theorem not_entails_of_eval_unknown_ne_true {A : PL.Proposition Atom}
    (h : Valuation.unknown.eval A ≠ .true) : ¬Entails ∅ A :=
  fun hA => h (hA _ trivial (by simp))

/-- No `⊥`-free proposition follows from no premises: all are `unknown` under
`Valuation.unknown`. -/
theorem not_entails_of_isBotFree {A : PL.Proposition Atom} (h : IsBotFree A) : ¬Entails ∅ A :=
  not_entails_of_eval_unknown_ne_true (by simp [Valuation.eval_unknown h])

/-- By contrast, `⊥ → A` follows from no premises, since `⊥` evaluates to `false`. -/
theorem entails_bot_imp (A : PL.Proposition Atom) : Entails ∅ (⊥ → A) := fun _ _ _ => by
  simp [Satisfies.eval_eq_true_iff]

/-- Excluded middle fails for `⊥`-free `A`. -/
theorem not_entails_or_not {A : PL.Proposition Atom} (h : IsBotFree A) : ¬Entails ∅ (A ∨ ¬A) :=
  not_entails_of_eval_unknown_ne_true (by simp [Valuation.eval_unknown h])

/-- The deduction theorem fails: `A` entails `A`, but `A → A` does not follow from no premises
for `⊥`-free `A`, since `unknownᶜ ⊔ unknown = unknown`. -/
theorem not_deduction_theorem {A : PL.Proposition Atom} (h : IsBotFree A) :
    Entails {A} A ∧ ¬Entails ∅ (A → A) :=
  ⟨entailsWithin_of_mem (Set.mem_singleton _), not_entails_of_isBotFree (.imp h h)⟩

/-! ### Comparison with intuitionistic logic -/

/-- A tag for the inference system on propositions whose derivable propositions are the Kleene
consequences of no premises. It is defined semantically: no proof system for Kleene's logic is
given here. -/
inductive K3

instance : InferenceSystem K3 (PL.Proposition Atom) := ⟨fun A => Entails ∅ A⟩

theorem derivation_k3_iff {A : PL.Proposition Atom} : K3⇓A ↔ Entails ∅ A := Iff.rfl

/-- Explosion is derivable, which is all that `IsIntuitionistic` asks for. -/
instance : InferenceSystem.IsIntuitionistic K3 (PL.Proposition Atom) := ⟨entails_bot_imp⟩

open PL.NaturalDeduction in
/-- Not every theorem of intuitionistic propositional logic (`IPL`) follows from no premises:
`p → p` is derivable by natural deduction but is `unknown` when `p` is. -/
theorem not_k3_of_derivableIn_ipl [DecidableEq Atom] [Nonempty Atom] :
    ¬∀ A : PL.Proposition Atom, InferenceSystem.DerivableIn (ND₁ (PL.IPL Atom)) A → K3⇓A := by
  obtain ⟨p⟩ := ‹Nonempty Atom›
  exact fun h => not_entails_of_isBotFree (.imp (.atom p) (.atom p)) (h _ ⟨.impI ∅ .ass⟩)

/-! ### Comparison with classical consequence -/

/-- A valuation is two-valued if it never takes the value `unknown`. -/
def Valuation.IsTwoValued (v : Valuation Atom) : Prop := ∃ b : Atom → Bool, v = Value.ofBool ∘ b

/-- Consequence over two-valued valuations. This is truth-table consequence, since `Value.ofBool`
commutes with the operations. -/
abbrev ClassicalEntails (Γ : Set (PL.Proposition Atom)) (A : PL.Proposition Atom) : Prop :=
  EntailsWithin (Judgement Atom) InferenceSystem.Default {v : Valuation Atom | v.IsTwoValued} Γ A

/-- Kleene consequence is sub-classical: whatever follows in Kleene follows classically. -/
theorem Entails.classicalEntails {Γ : Set (PL.Proposition Atom)} {A : PL.Proposition Atom}
    (h : Entails Γ A) : ClassicalEntails Γ A :=
  h.anti (Set.subset_univ _)

/-- Under a two-valued valuation, every proposition evaluates to a classical truth value. -/
theorem Valuation.exists_eval_ofBool_eq (b : Atom → Bool) (A : PL.Proposition Atom) :
    ∃ c : Bool, Valuation.eval (Value.ofBool ∘ b) A = Value.ofBool c := by
  induction A with
  | atom p => exact ⟨b p, rfl⟩
  | falsum => exact ⟨false, rfl⟩
  | _ _ _ ih₁ ih₂ =>
    obtain ⟨c₁, hc₁⟩ := ih₁
    obtain ⟨c₂, hc₂⟩ := ih₂
    cases c₁ <;> cases c₂ <;> simp [Valuation.eval, hc₁, hc₂, Bool.exists_bool]

/-- Excluded middle holds classically, for every proposition. -/
theorem classicalEntails_or_not (A : PL.Proposition Atom) : ClassicalEntails ∅ (A ∨ ¬A) := by
  rintro v ⟨b, rfl⟩ _
  obtain ⟨c, hc⟩ := Valuation.exists_eval_ofBool_eq b A
  cases c <;> simp [Satisfies.eval_eq_true_iff, hc]

/-- Kleene consequence is strictly sub-classical. Some atom is needed, since otherwise every
proposition has a fixed, definite value. -/
theorem not_entails_of_classicalEntails [Nonempty Atom] :
    ¬∀ (Γ : Set (PL.Proposition Atom)) (A : PL.Proposition Atom),
      ClassicalEntails Γ A → Entails Γ A := by
  obtain ⟨p⟩ := ‹Nonempty Atom›
  exact fun h => not_entails_or_not (IsBotFree.atom p) (h ∅ _ (classicalEntails_or_not _))

end Cslib.Logic.Kleene
