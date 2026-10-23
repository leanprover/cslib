/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

module

public import Cslib.Logics.Kleene.Basic
public import Cslib.Logics.Propositional.Defs
public import Cslib.Foundations.Logic.InferenceSystem
public import Cslib.Foundations.Logic.Consequence

/-! # Kleene semantics for propositional logic

Propositions of CSLib's propositional logic (`PL.Proposition`) are evaluated in `Kleene.Value` by
the strong truth tables of Kleene's three-valued logic (K3) [Kleene1952]. The falsum `⊥` is an atom,
and negation is the defined connective `¬A := A → ⊥`. Since Kleene's implication satisfies
`a → false = ¬a`, negation is Kleene negation under valuations sending `⊥` to `false`
(`Valuation.respectsBot`).

## Main definitions

- `Kleene.Valuation`: valuations of atoms in `Kleene.Value`.
- `Kleene.Valuation.eval`: evaluation of a proposition under a valuation.
- `Kleene.Valuation.respectsBot`: the valuations sending `⊥` to `false`.
- `Kleene.Satisfies`, with the notation `⇓K3[v ⊨ A]`: satisfaction.
- `Kleene.Valid`: validity, that is, satisfaction under every falsum-respecting valuation.
- `Kleene.IsBotFree`: the propositions in which `⊥` does not occur.
- `Kleene.Entails`: consequence, the generic notion over `Valuation.respectsBot`.

## Main results

- `Kleene.Valuation.eval_not`: under a falsum-respecting valuation, `¬A` evaluates to the Kleene
  negation of the value of `A`.
- `Kleene.Satisfies.and_iff_and` and friends: satisfaction of compound propositions in terms of
  their components.
- `Kleene.not_valid_of_isBotFree` and `Kleene.valid_bot_imp`: no `⊥`-free proposition is valid,
  while `⊥ → A` is valid for every `A`.
- `Kleene.Valuation.eval_infoLE`: evaluation is monotone in the information order `⊑` on
  `Kleene.Value`.
- `Kleene.not_deduction_theorem`: `A` entails `A`, but `A → A` is not valid for `⊥`-free `A`.
- `Kleene.entails_of_mem_of_mem_not`: explosion, from `A` and `¬A` together.

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

/-- The converse fails, since `A` may be `unknown`. -/
theorem Satisfies.not_satisfies_of_not [Bot Atom] {v : Valuation Atom} (hv : v ⊥ = .false)
    {A : PL.Proposition Atom} (h : ⇓K3[v ⊨ ¬A]) : ¬⇓K3[v ⊨ A] := by
  grind [Satisfies.not_iff_eval_eq_false hv]

/-! ### Judgemental contexts -/

/-- A judgemental context is a valuation: the judgement `K3[v ⊨ A]` with the proposition missing. -/
instance : HasHContext (Judgement Atom) (PL.Proposition Atom) :=
  ⟨fun (v : Valuation Atom) A => K3[v ⊨ A]⟩

@[simp, scoped grind =]
theorem Judgement.fill_def {v : Valuation Atom} {A : PL.Proposition Atom} :
    HasHContext.fill (α := Judgement Atom) v A = K3[v ⊨ A] := rfl

/-! ### Validity -/

/-- A proposition is valid if it is satisfied under every falsum-respecting valuation. -/
abbrev Valid [Bot Atom] (A : PL.Proposition Atom) : Prop :=
  ValidWithin (Judgement Atom) InferenceSystem.Default Valuation.respectsBot A

/-- A proposition is `⊥`-free if the atom `⊥` does not occur in it. Since `¬A := A → ⊥`, no
negation is `⊥`-free. -/
inductive IsBotFree [Bot Atom] : PL.Proposition Atom → Prop
  /-- An atom other than `⊥`. -/
  | atom {p : Atom} (h : p ≠ ⊥) : IsBotFree (.atom p)
  /-- Conjunction. -/
  | and {A B : PL.Proposition Atom} (hA : IsBotFree A) (hB : IsBotFree B) : IsBotFree (A ∧ B)
  /-- Disjunction. -/
  | or {A B : PL.Proposition Atom} (hA : IsBotFree A) (hB : IsBotFree B) : IsBotFree (A ∨ B)
  /-- Implication. -/
  | imp {A B : PL.Proposition Atom} (hA : IsBotFree A) (hB : IsBotFree B) : IsBotFree (A → B)

open Classical in
/-- The valuation sending `⊥` to `false` and every other atom to `unknown`. -/
noncomputable def Valuation.unknownExceptBot [Bot Atom] : Valuation Atom :=
  fun p => if p = ⊥ then .false else .unknown

theorem Valuation.unknownExceptBot_mem_respectsBot [Bot Atom] :
    (Valuation.unknownExceptBot : Valuation Atom) ∈ Valuation.respectsBot := by
  simp [Valuation.mem_respectsBot, Valuation.unknownExceptBot]

theorem Valuation.eval_unknownExceptBot [Bot Atom] {A : PL.Proposition Atom} (h : IsBotFree A) :
    Valuation.unknownExceptBot.eval A = .unknown := by
  induction h <;> simp [Valuation.unknownExceptBot, *]

theorem Valid.eval_unknownExceptBot [Bot Atom] {A : PL.Proposition Atom} (h : Valid A) :
    Valuation.unknownExceptBot.eval A = .true :=
  h _ Valuation.unknownExceptBot_mem_respectsBot

/-- No `⊥`-free proposition is valid: all are `unknown` under `Valuation.unknownExceptBot`. -/
theorem not_valid_of_isBotFree [Bot Atom] {A : PL.Proposition Atom} (h : IsBotFree A) :
    ¬Valid A := fun hv => by
  simpa [Valuation.eval_unknownExceptBot h] using hv.eval_unknownExceptBot

/-- By contrast, explosion is valid, since `⊥` evaluates to `false`. -/
theorem valid_bot_imp [Bot Atom] (A : PL.Proposition Atom) : Valid (⊥ → A) := fun _ hv => by
  simp [Satisfies.eval_eq_true_iff, Valuation.mem_respectsBot.mp hv]

/-- Excluded middle fails for `⊥`-free `A`. -/
theorem not_valid_or_not [Bot Atom] {A : PL.Proposition Atom} (h : IsBotFree A) :
    ¬Valid (A ∨ ¬A) := fun hv => by
  simpa [Valuation.eval_not Valuation.unknownExceptBot_mem_respectsBot,
    Valuation.eval_unknownExceptBot h] using hv.eval_unknownExceptBot

/-- Even `A → A` fails for `⊥`-free `A`, since `unknown → unknown = unknown`. -/
theorem not_valid_imp_self [Bot Atom] {A : PL.Proposition Atom} (h : IsBotFree A) :
    ¬Valid (A → A) := fun hv => by
  simpa [Valuation.eval_unknownExceptBot h] using hv.eval_unknownExceptBot

/-! ### Monotonicity in the information order -/

/-- Evaluation is monotone in the information order: refining the values of the atoms refines
the value of every proposition. -/
theorem Valuation.eval_infoLE {v v' : Valuation Atom} (h : ∀ p, v p ⊑ v' p)
    (A : PL.Proposition Atom) : v.eval A ⊑ v'.eval A := by
  induction A with
  | atom p => exact h p
  | and _ _ ih₁ ih₂ => exact ih₁.and ih₂
  | or _ _ ih₁ ih₂ => exact ih₁.or ih₂
  | imp _ _ ih₁ ih₂ => exact ih₁.imp ih₂

/-! ### Consequence -/

/-- Consequence over falsum-respecting valuations: every such valuation satisfying all the premises
satisfies the conclusion. The structural lemmas are the generic `EntailsWithin.mono` (weakening)
and `EntailsWithin.trans` (cut). -/
abbrev Entails [Bot Atom] (Γ : Set (PL.Proposition Atom)) (A : PL.Proposition Atom) : Prop :=
  EntailsWithin (Judgement Atom) InferenceSystem.Default Valuation.respectsBot Γ A

/-- Explosion: `A` and `¬A` together entail everything, since no falsum-respecting valuation
satisfies both. -/
theorem entails_of_mem_of_mem_not [Bot Atom] {Γ : Set (PL.Proposition Atom)}
    {A : PL.Proposition Atom} (h₁ : A ∈ Γ) (h₂ : (¬A) ∈ Γ) (B : PL.Proposition Atom) :
    Entails Γ B :=
  entailsWithin_of_incompatible h₁ h₂
    (fun _ hv hA hnA => Satisfies.not_satisfies_of_not hv hnA hA) B

/-- The deduction theorem fails: `A` entails `A`, but `A → A` is not valid for `⊥`-free `A`. -/
theorem not_deduction_theorem [Bot Atom] {A : PL.Proposition Atom} (h : IsBotFree A) :
    Entails {A} A ∧ ¬Valid (A → A) :=
  ⟨entailsWithin_of_mem (Set.mem_singleton _), not_valid_imp_self h⟩

end Cslib.Logic.Kleene
