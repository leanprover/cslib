
import Cslib.Init
import Cslib.Foundations.Semantics.LTS.Basic

/-! # Hennessy–Milner Logic

Hennessy–Milner logic (HML) is a modal logic used for reasoning about the behaviour of
Labelled Transition Systems (LTS). It was introduced by Matthew Hennessy and Robin Milner
to capture notion of observational equivalence in concurrent systems.

## Main definitions

- `Formula` defines the inductive syntax of HML formulas over an alphabet Σ
- `satisfies` provides the semantics for evaluating formulas on LTS states
- Scoped notation for modal operators (⟨a⟩ and ¬)

## References

* [M. Hennessy and R. Milner,
*Algebraic Laws for Non-Determinism and Concurrency*][HennessyMilner1985]
* [B. Bisping, D. N. Jansen, and U. Nestmann,
*Deciding All Behavioral Equivalences at Once:
A Game for Linear-Time–Branching-Time Spectroscopy*][BispingEtAl2022]

-/

namespace Cslib

universe u v

variable {State : Type u} {Label : Type v}

namespace HennessyMilner

/--
Hennessy–Milner logic formulas over an alphabet Σ (Label type).

(Hennessy–Milner logic): Given an alphabet Σ, the syntax of
Hennessy-Milner logic formulas, HML[Σ], is inductively defined as follows:
1. **Observations:** If φ ∈ HML[Σ] and a ∈ Σ, then ⟨a⟩φ ∈ HML[Σ]
2. **Conjunctions:** If φ_i ∈ HML[Σ] for all i from an index set I, then ⋀_{i∈I} φ_i ∈ HML[Σ]
3. **Negations:** If φ ∈ HML[Σ], then ¬φ ∈ HML[Σ]
-/
inductive Formula (Label : Type v) : Type v where
  /-- The constant truth formula. -/
  | true : Formula Label
  /-- The constant false formula. -/
  | false : Formula Label
  /-- Modal observation operator: ⟨a⟩φ means
  "there exists an a-transition to a state satisfying φ". -/
  | modal (a : Label) (φ : Formula Label) : Formula Label
  /-- Conjunction of a finite list of formulas. -/
  | conj (φs : List (Formula Label)) : Formula Label
  /-- Negation operator: ¬φ means "not φ". -/
  | neg (φ : Formula Label) : Formula Label

/-- Disjunction of a finite list of formulas (derived connective). -/
def Formula.disj (φs : List (Formula Label)) : Formula Label :=
  Formula.neg (Formula.conj (φs.map Formula.neg))

/-- Implication φ ⊃ ψ (derived connective). -/
def Formula.impl (φ ψ : Formula Label) : Formula Label :=
  Formula.disj [Formula.neg φ, ψ]

/-- Semantic satisfaction relation for HML formulas on LTS states. -/
def satisfies (lts : LTS State Label) (s : State) : Formula Label → Prop
  | .true => True
  | .false => False
  | .modal a φ => ∃ s', lts.Tr s a s' ∧ satisfies lts s' φ
  | .conj φs => ∀ φ ∈ φs, satisfies lts s φ
  | .neg φ => ¬satisfies lts s φ

/-- Shorthand for the satisfaction relation. -/
scoped infix:50 " ⊨ " => satisfies

/-- A state satisfies a formula if there exists some transition leading
to a state that satisfies it. -/
theorem satisfies_modal_intro (lts : LTS State Label) (s : State) (a : Label) (φ : Formula Label) :
  ∀ s', lts.Tr s a s' → satisfies lts s' φ → satisfies lts s (Formula.modal a φ) := by
  intro s' htr hφ
  simp only [satisfies]
  exists s'



/-- A state satisfies a conjunction if and only if it satisfies all conjuncts. -/
theorem satisfies_conj (lts : LTS State Label) (s : State) (φs : List (Formula Label)) :
  satisfies lts s (Formula.conj φs) ↔ ∀ φ ∈ φs, satisfies lts s φ := by
  simp only [satisfies]


/-- Double negation elimination for HML. -/
theorem satisfies_double_neg (lts : LTS State Label) (s : State) (φ : Formula Label) :
  satisfies lts s (Formula.neg (Formula.neg φ)) ↔ satisfies lts s φ := by
  simp only [satisfies, not_not]



end HennessyMilner

end Cslib
