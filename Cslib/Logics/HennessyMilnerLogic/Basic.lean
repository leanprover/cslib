
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


/-- Size of a formula (for well-founded recursion) -/
def Formula.size : Formula Label → Nat
  | .true => 1
  | .false => 1
  | .modal _ φ => 1 + φ.size
  | .conj φs => 1 + φs.foldr (fun φ acc => φ.size + acc) 0
  | .neg φ => 1 + φ.size


#print Formula.rec


/-- induction on formula structure -/
theorem Formula.ind_on {Label : Type v} {P : Formula Label → Prop}
  (φ : Formula Label)
  (h_true : P .true)
  (h_false : P .false)
  (h_modal : ∀ a ψ, P ψ → P (.modal a ψ))
  (h_conj : ∀ φs, (∀ φ ∈ φs, P φ) → P (.conj φs))
  (h_neg : ∀ ψ, P ψ → P (.neg ψ))
  : P φ := by
  apply Formula.rec
    (motive_1 := P)
    (motive_2 := fun φs => ∀ φ ∈ φs, P φ)
  · -- true case
    exact h_true
  · -- false case
    exact h_false
  · -- modal case
    exact h_modal
  · -- conj case
    intro φs h_all
    exact h_conj φs h_all
  · -- neg case
    exact h_neg
  · -- nil case (empty list)
    intros φ h_mem
    cases h_mem
  · -- cons case
    intros head tail h_head h_tail φ h_mem
    cases h_mem with
    | head h_eq => exact h_head
    | tail h_in =>
      apply h_tail
      trivial

/-- If two LTS have the same transition relation, then they satisfy the same formulas -/
theorem satisfies_independent_of_lts_structure
  {State : Type u} {Label : Type v}
  (lts1 lts2 : LTS State Label)
  (h_same_tr : ∀ s a s', lts1.Tr s a s' ↔ lts2.Tr s a s')
  (s : State) (φ : Formula Label) :
  satisfies lts1 s φ ↔ satisfies lts2 s φ := by
  induction φ using Formula.ind_on generalizing s with
  | h_true =>
    -- True case: both are True
    simp [satisfies]
  | h_false =>
    -- False case: both are False
    simp [satisfies]
  | h_modal a ψ ih =>
    -- Modal case: ⟨a⟩ψ
    simp only [satisfies]
    constructor
    · intro ⟨s', ⟨h_tr1, h_sat1⟩⟩
      use s'
      constructor
      · rw [← h_same_tr]
        exact h_tr1
      · rw [← ih s']
        exact h_sat1
    · intro ⟨s', ⟨h_tr2, h_sat2⟩⟩
      use s'
      constructor
      · rw [h_same_tr]
        exact h_tr2
      · rw [ih s']
        exact h_sat2
  | h_conj φs ih_list =>
    -- Conjunction case: ⋀ᵢ φᵢ
    simp only [satisfies]
    constructor
    · intro h_all φ h_mem
      rw [← ih_list φ h_mem s]
      exact h_all φ h_mem
    · intro h_all φ h_mem
      rw [ih_list φ h_mem s]
      exact h_all φ h_mem
  | h_neg ψ ih =>
    -- Negation case: ¬ψ
    simp only [satisfies]
    rw [ih s]

end HennessyMilner

end Cslib
