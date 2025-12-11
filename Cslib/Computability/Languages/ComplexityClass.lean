
import Cslib.Foundations.Data.Encoding
import Cslib.Computability.Automata.Acceptor
import Mathlib.Computability.TMComputable

/-!
# Complexity Classes

This file contains the definition of `ComplexityClass`es over bitstring decision problems,
as well as several standard complexity classes such as P, NP, and the polynomial time hierarchy.

## TODO

- Define other complexity classes such as BPP, RP, coRP, ZPP, PSPACE.
- Prove basic inclusions between these classes.
-/

open Computability Turing

namespace ComplexityTheory


/--
The type of decision problems on bitstrings.

We define these as functions from lists of booleans to booleans,
implictly assuming the usual encodings.

TODO: An Decision Problem type over arbitrary types.
-/
abbrev BitstringDecisionProblem := List Bool → Bool

/--
The type of complexity classes over bitstrings.
We define these as sets of `BitstringDecisionProblem`s.
-/
abbrev ComplexityClass := Set BitstringDecisionProblem

/--
A simple definition to abstract the notion of a poly-time Turing machine into a predicate.
-/
def IsComputableInPolyTime {α β : Type} (ea : FinEncoding α) (eb : FinEncoding β) (f : α → β) :=
  Nonempty (TM2ComputableInPolyTime ea eb f)

/--
The class P is the set of decision problems
decidable in polynomial time by a deterministic Turing machine.
-/
def P : ComplexityClass :=
  { L | IsComputableInPolyTime finEncodingListBool finEncodingBoolBool L }

/--
The list of all bitstrings of exactly length `n`, in lexicographic order.
-/
def bitstringsOfLength : ℕ → List (List Bool)
  | 0     => [[]]
  | n + 1 => (bitstringsOfLength n) >>= fun bs ↦ [bs ++ [false], bs ++ [true]]

/--
The list of all bitstrings of length `n` or less.

Ordered first by length, then lexicographically.
-/
def bitstringsUpToLength (n : ℕ) : List (List Bool) :=
  (List.range (n + 1)) >>= bitstringsOfLength

/--
Given a polynomial `p` and a bitstring decision problem `L` that operates on pairs of bitstrings,
defines a new decision problem to determine, for an input string `x`,
whether all strings `w` of length at most `p (|x|)` satisfy `L (x, w)`.

Reference:
- https://en.wikipedia.org/wiki/Polynomial_hierarchy#Quantified_Boolean_formulae_definition
-/
def BitstringDecisionProblem.universallyQuantifyOverPolynomial
    (p : Polynomial ℕ) (L : BitstringDecisionProblem) :
    BitstringDecisionProblem :=
  fun x ↦
    List.all (bitstringsUpToLength (p.eval x.length)) fun w ↦
      L (encode_list_bool_prod_list_bool (x, w))

/--
Given a polynomial `p` and a bitstring decision problem `L` that operates on pairs of bitstrings,
defines a new decision problem to determine, for an input string `x`,
whether there exists a string `w` of length at most `p (|x|)` such that `L (x, w)` holds.

Reference:
- https://en.wikipedia.org/wiki/Polynomial_hierarchy#Quantified_Boolean_formulae_definition
-/
def BitstringDecisionProblem.existentiallyQuantifyOverPolynomial
    (p : Polynomial ℕ) (L : BitstringDecisionProblem) :
    BitstringDecisionProblem :=
  fun x ↦ List.any (bitstringsUpToLength (p.eval x.length)) fun w ↦
    L (encode_list_bool_prod_list_bool (x, w))


def ComplexityClass.polyUniversallyQuantify (C : ComplexityClass) :
    ComplexityClass :=
  { L | ∃ p : Polynomial ℕ, ∃ L' ∈ C,
      L = BitstringDecisionProblem.universallyQuantifyOverPolynomial p L' }

notation "∀ᴾ " C => ComplexityClass.polyUniversallyQuantify C

def ComplexityClass.polyExistentiallyQuantify (C : ComplexityClass) :
    ComplexityClass :=
  { L | ∃ p : Polynomial ℕ, ∃ L' ∈ C,
      L = BitstringDecisionProblem.existentiallyQuantifyOverPolynomial p L' }

notation "∃ᴾ " C => ComplexityClass.polyExistentiallyQuantify C


-- /--
-- The polynomial time hierarchy is defined by mutual induction as follows:

-- Σᴾ 0 = Πᴾ 0 = P
-- Σᴾ n+1 = ∃ᵖ Πᴾ n
-- Πᴾ n+1 = ∀ᵖ Σᴾ n
-- -/
mutual
  def SigmaPolyTimeHierarchy : ℕ → ComplexityClass
    | 0     => P
    | n + 1 => (PiPolyTimeHierarchy n).polyExistentiallyQuantify

  def PiPolyTimeHierarchy : ℕ → ComplexityClass
    | 0     => P
    | n + 1 => (SigmaPolyTimeHierarchy n).polyUniversallyQuantify
end

-- TODO bind more tightly
notation "Σᴾ " n => SigmaPolyTimeHierarchy n
notation "Πᴾ " n => PiPolyTimeHierarchy n

def PolyTimeHierarchy : ComplexityClass :=
  { L | ∃ n : ℕ, L ∈ Σᴾ n }

lemma SigmaPolyTimeHierarchy_succ
    (n : ℕ) : (Σᴾ (n + 1)) = (Πᴾ n).polyExistentiallyQuantify :=
  rfl

/--
Pi n contained in Sigma n+1
-/
lemma PiPolyTimeHierarchy_subset_SigmaPolyTimeHierarchy_succ
    (n : ℕ) : (Πᴾ n) ⊆ Σᴾ (n + 1) := by
  rw [SigmaPolyTimeHierarchy_succ]
  rw [Set.subset_def]
  intro L hL_mem
  simp? [ComplexityClass.polyExistentiallyQuantify]
  -- TODO if x ∈ Πᴾ n, then the language of pairs (x, ∅) is in Πᴾ n
  use 0
  sorry

/--
Pi n contained in Pi n+1
-/
lemma PiPolyTimeHierarchy_subset_PiPolyTimeHierarchy_succ
    (n : ℕ) : (Πᴾ n) ⊆ Πᴾ (n + 1) := by
  sorry

/--
Sigma n contained in Pi n+1
-/
lemma SigmaPolyTimeHierarchy_subset_PiPolyTimeHierarchy_succ
    (n : ℕ) : (Σᴾ n) ⊆ Πᴾ (n + 1) := by
  sorry

/--
Sigma n contained in Sigma n+1
-/
lemma SigmaPolyTimeHierarchy_subset_SigmaPolyTimeHierarchy_succ
    (n : ℕ) : (Σᴾ n) ⊆ Σᴾ (n + 1) := by
  sorry

lemma PolyTimeHierarchy_eq_union_sigma :
  PolyTimeHierarchy = ⋃ n : ℕ, Σᴾ n := by
  ext L
  simp [PolyTimeHierarchy]

lemma PolyTimeHierarchy_eq_union_pi :
  PolyTimeHierarchy = ⋃ n : ℕ, Πᴾ n := by
  sorry

/--
The class NP is the set of decision problems
such that there exists a polynomial `p` over ℕ and a poly-time Turing machine
where for all `x`, `L x = true` iff there exists a `w` of length at most `p (|x|)`
such that the Turing machine accepts the pair `(x,w)`.

See Definition 2.1 in Arora-Barak (2009).
-/
def NP : ComplexityClass := Σᴾ 1

/--
The class coNP is the set of decision problems
whose complements are in NP.
-/
def coNP : ComplexityClass := Πᴾ 1

end ComplexityTheory
