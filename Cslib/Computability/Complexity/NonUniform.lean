/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Circuits.Circuit.Basic
public import Cslib.Computability.Complexity.Classes

@[expose] public section

/-! # Non-Uniform Complexity Classes

This file defines non-uniform complexity classes based on circuit families and
polynomial advice.

## Main definitions

* `SIZE s` — languages decidable by circuit families of size at most `s(n)`
* `PPoly` — **P/poly** (circuit-based): languages decidable by polynomial-size circuits
* `PPolyAdvice` — **P/poly** (advice-based): poly-time TM with poly-length advice

## Main results

* `SIZE_mono` — `SIZE` is monotone: if `s ≤ s'` pointwise then `SIZE s ⊆ SIZE s'`
* `SIZE_subset_PPoly` — `SIZE s ⊆ PPoly` when `s` is bounded by a polynomial
* `ComplexityP_subset_PPolyAdvice` — **P ⊆ P/poly** (advice-based)

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraB2009]
-/

open Cslib.Circuits Polynomial Turing SingleTapeTM

variable {Op : Type*} [Basis Op]
variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]

/-- `SIZE s` is the class of languages decidable by circuit families whose circuit
at input size `n` has at most `s n` gates. -/
def SIZE (s : ℕ → ℕ) : Set (Set (List Bool)) :=
  { L | ∃ C : CircuitFamily Op,
    C.Decides L ∧ (∀ n, (C n).GatesWellFormed) ∧ ∀ n, (C n).size ≤ s n }

/-- **P/poly** (circuit-based): the class of languages decidable by polynomial-size
circuit families. A language is in P/poly if there exists a circuit family and a
polynomial `p` such that the family decides the language and every circuit has at
most `p(n)` gates. -/
def PPoly : Set (Set (List Bool)) :=
  { L | ∃ C : CircuitFamily Op, ∃ p : Polynomial ℕ,
    C.Decides L ∧ (∀ n, (C n).GatesWellFormed) ∧ ∀ n, (C n).size ≤ p.eval n }

/-- **P/poly** (advice-based): the class of languages decidable by a polynomial-time
Turing machine augmented with polynomial-length advice strings. The advice string
depends only on the input length, not the input itself. -/
def PPolyAdvice : Set (Set (List Symbol)) :=
  { L | ∃ (f : List Symbol → List Symbol) (advice : ℕ → List Symbol) (p : Polynomial ℕ),
    Nonempty (PolyTimeComputable f) ∧
    (∀ n, (advice n).length ≤ p.eval n) ∧
    (∀ x, x ∈ L ↔ f (x ++ advice x.length) ≠ []) }

end

open Cslib.Circuits Cslib.Complexity Polynomial Turing SingleTapeTM

/-! ### Monotonicity and containment -/

/-- `SIZE` is monotone: if `s ≤ s'` pointwise then `SIZE s ⊆ SIZE s'`. -/
theorem SIZE_mono {Op : Type*} [Basis Op] {s s' : ℕ → ℕ} (h : ∀ n, s n ≤ s' n) :
    SIZE (Op := Op) s ⊆ SIZE (Op := Op) s' := by
  intro L ⟨C, hDecides, hWF, hSize⟩
  exact ⟨C, hDecides, hWF, fun n => Nat.le_trans (hSize n) (h n)⟩

/-- If `s` is bounded by a polynomial then `SIZE s ⊆ PPoly`. -/
theorem SIZE_subset_PPoly {Op : Type*} [Basis Op] {s : ℕ → ℕ}
    {p : Polynomial ℕ} (h : ∀ n, s n ≤ p.eval n) :
    SIZE (Op := Op) s ⊆ PPoly (Op := Op) := by
  intro L ⟨C, hDecides, hWF, hSize⟩
  exact ⟨C, p, hDecides, hWF, fun n => Nat.le_trans (hSize n) (h n)⟩

/-- **P ⊆ P/poly** (advice-based): Every language in P is in P/poly.

*Proof sketch*: Given a polytime decider `f` for `L`, use `f` with empty advice
`fun _ => []` and advice polynomial `0`. Since the advice is always empty,
`f (x ++ []) = f x`, so the decider works unchanged. -/
theorem ComplexityP_subset_PPolyAdvice {Symbol : Type} :
    P (Symbol := Symbol) ⊆ PPolyAdvice := by
  intro L ⟨f, hf, hDecides⟩
  refine ⟨f, fun _ => [], 0, hf, fun _ => ?_, fun x => ?_⟩
  · simp
  · rw [List.append_nil]
    exact hDecides x

