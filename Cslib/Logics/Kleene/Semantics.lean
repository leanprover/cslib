/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

module

public import Cslib.Logics.Kleene.Basic
public import Cslib.Logics.Propositional.Defs
public import Cslib.Foundations.Logic.InferenceSystem

/-! # Kleene semantics for propositional logic

Propositions of CSLib's propositional logic (`PL.Proposition`) are evaluated in `Kleene.Value` by
the strong truth tables of Kleene's three-valued logic (K3) [Kleene1952]. The falsum `⊥` is an atom,
and negation is the defined connective `¬A := A → ⊥`. Since Kleene's implication satisfies
`a → false = ¬a`, negation is Kleene negation under valuations sending `⊥` to `false`. This is a
condition on valuations (`Valuation.respectsBot`), not built into the type of valuations.

## Main definitions

- `Kleene.Valuation`: valuations of atoms in `Kleene.Value`.
- `Kleene.Valuation.eval`: evaluation of a proposition under a valuation.
- `Kleene.Valuation.respectsBot`: the valuations sending `⊥` to `false`.
- `Kleene.Satisfies`, with the notation `⇓K3[v ⊨ A]`: satisfaction.

## Main results

- `Kleene.Valuation.eval_not`: under a falsum-respecting valuation, `¬A` evaluates to the Kleene
  negation of the value of `A`.
- `Kleene.Satisfies.and_iff_and` and friends: satisfaction of compound propositions in terms of
  their components. `¬A` is satisfied iff `A` evaluates to `false`; unlike classically, this is
  stronger than `A` not being satisfied, since `A` may be `unknown`.

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

/-- Evaluation of a proposition under a valuation, by the truth tables of `Value`. -/
def Valuation.eval (v : Valuation Atom) : PL.Proposition Atom → Value
  | .atom p => v p
  | .and A B => v.eval A ∧ v.eval B
  | .or A B => v.eval A ∨ v.eval B
  | .imp A B => v.eval A → v.eval B

@[simp, scoped grind =]
theorem Valuation.eval_atom (v : Valuation Atom) (p : Atom) : v.eval (.atom p) = v p := rfl

@[simp, scoped grind =]
theorem Valuation.eval_and (v : Valuation Atom) (A B : PL.Proposition Atom) :
    v.eval (A ∧ B) = (v.eval A ∧ v.eval B) := rfl

@[simp, scoped grind =]
theorem Valuation.eval_or (v : Valuation Atom) (A B : PL.Proposition Atom) :
    v.eval (A ∨ B) = (v.eval A ∨ v.eval B) := rfl

@[simp, scoped grind =]
theorem Valuation.eval_imp (v : Valuation Atom) (A B : PL.Proposition Atom) :
    v.eval (A → B) = (v.eval A → v.eval B) := rfl

@[simp, scoped grind =]
theorem Valuation.eval_bot [Bot Atom] (v : Valuation Atom) : v.eval ⊥ = v ⊥ := rfl

/-- Under a valuation sending `⊥` to `false`, the defined negation `¬A := A → ⊥` is Kleene
negation. -/
theorem Valuation.eval_not [Bot Atom] {v : Valuation Atom} (hv : v ⊥ = .false)
    (A : PL.Proposition Atom) : v.eval (¬A) = ¬v.eval A := by
  simp [← PL.not_eq, hv]

/-- The valuations sending `⊥` to `false`. -/
def Valuation.respectsBot [Bot Atom] : Set (Valuation Atom) := {v | v ⊥ = .false}

theorem Valuation.mem_respectsBot [Bot Atom] {v : Valuation Atom} :
    v ∈ Valuation.respectsBot ↔ v ⊥ = .false := Iff.rfl

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
theorem derivation_def {v : Valuation Atom} {A : PL.Proposition Atom} :
    Satisfies v A = ⇓K3[v ⊨ A] := rfl

@[scoped grind =]
theorem Satisfies.eval_eq_true_iff {v : Valuation Atom} {A : PL.Proposition Atom} :
    ⇓K3[v ⊨ A] ↔ v.eval A = .true := Iff.rfl

@[simp, scoped grind =]
theorem Satisfies.atom_iff {v : Valuation Atom} {p : Atom} :
    ⇓K3[v ⊨ .atom p] ↔ v p = .true := Iff.rfl

@[scoped grind =]
theorem Satisfies.and_iff_and {v : Valuation Atom} {A B : PL.Proposition Atom} :
    ⇓K3[v ⊨ A ∧ B] ↔ ⇓K3[v ⊨ A] ∧ ⇓K3[v ⊨ B] := Value.and_eq_true_iff

@[scoped grind =]
theorem Satisfies.or_iff_or {v : Valuation Atom} {A B : PL.Proposition Atom} :
    ⇓K3[v ⊨ A ∨ B] ↔ ⇓K3[v ⊨ A] ∨ ⇓K3[v ⊨ B] := Value.or_eq_true_iff

@[scoped grind =]
theorem Satisfies.imp_iff {v : Valuation Atom} {A B : PL.Proposition Atom} :
    ⇓K3[v ⊨ A → B] ↔ v.eval A = .false ∨ ⇓K3[v ⊨ B] := by
  simp [Satisfies.eval_eq_true_iff, Value.imp_eq_not_or]

@[scoped grind =]
theorem Satisfies.not_iff_eval_eq_false [Bot Atom] {v : Valuation Atom} (hv : v ⊥ = .false)
    {A : PL.Proposition Atom} : ⇓K3[v ⊨ ¬A] ↔ v.eval A = .false := by
  rw [Satisfies.eval_eq_true_iff, Valuation.eval_not hv, Value.not_eq_true_iff]

/-- The converse fails, since `A` may evaluate to `unknown`. -/
theorem Satisfies.not_satisfies_of_not [Bot Atom] {v : Valuation Atom} (hv : v ⊥ = .false)
    {A : PL.Proposition Atom} (h : ⇓K3[v ⊨ ¬A]) : ¬⇓K3[v ⊨ A] := by
  grind [Satisfies.not_iff_eval_eq_false hv]

end Cslib.Logic.Kleene
