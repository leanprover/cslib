
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
implicitly assuming the usual encodings.

TODO: An Decision Problem type over arbitrary types.
-/
abbrev BitstringDecisionProblem : Type := List Bool → Bool

/--
A simple definition to abstract the notion of a poly-time Turing machine into a predicate.
-/
def IsComputableInPolyTime {α β : Type} (ea : FinEncoding α) (eb : FinEncoding β) (f : α → β) :=
  Nonempty (TM2ComputableInPolyTime ea eb f)

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

@[simp]
lemma bitstringsUpToLength_zero :
    bitstringsUpToLength 0 = [[]] := by
  rfl

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

@[simp]
lemma BitstringDecisionProblem.universallyQuantifyOverPolynomial_complement
    (p : Polynomial ℕ) (L : BitstringDecisionProblem) :
    (L.universallyQuantifyOverPolynomial p)ᶜ =
      (Lᶜ).existentiallyQuantifyOverPolynomial p := by
  unfold universallyQuantifyOverPolynomial
  unfold existentiallyQuantifyOverPolynomial
  ext x
  simp [List.not_any_eq_all_not] -- Add to push Bool.not

@[simp]
lemma BitstringDecisionProblem.existentiallyQuantifyOverPolynomial_complement
    (p : Polynomial ℕ) (L : BitstringDecisionProblem) :
    (L.existentiallyQuantifyOverPolynomial p)ᶜ =
      (Lᶜ).universallyQuantifyOverPolynomial p := by
  unfold universallyQuantifyOverPolynomial
  unfold existentiallyQuantifyOverPolynomial
  ext x
  simp [List.not_all_eq_any_not] -- Add to push Bool.not



/--
The type of complexity classes over bitstrings.
We define these as sets of `BitstringDecisionProblem`s.
-/
abbrev ComplexityClass : Type := Set BitstringDecisionProblem

namespace ComplexityClass

/--
The class P is the set of decision problems
decidable in polynomial time by a deterministic Turing machine.
-/
def P : ComplexityClass :=
  { L | IsComputableInPolyTime finEncodingListBool finEncodingBoolBool L }

/--
The complement of a complexity class `C` is the set of decision problems
whose complements are in `C`.

Note that this is distinct from the complement of `C` as a set, which would be
the set of decision problems not in `C`.
-/
def complement (C : ComplexityClass) : ComplexityClass :=
  { L | (Lᶜ ∈ C) }

@[simp]
lemma complement_complement (C : ComplexityClass) :
    C.complement.complement = C := by
  ext L
  simp [complement, Set.mem_setOf_eq, compl_compl]

@[simp]
lemma P_complement : P.complement = P := by
  ext L
  -- TODO requires showing that Bool.not is poly time,
  -- and composition of poly-time functions is poly-time
  sorry

def polyUniversallyQuantify (C : ComplexityClass) :
    ComplexityClass :=
  { L | ∃ p : Polynomial ℕ, ∃ L' ∈ C,
      L = BitstringDecisionProblem.universallyQuantifyOverPolynomial p L' }

notation "∀ᴾ " C => polyUniversallyQuantify C

def polyExistentiallyQuantify (C : ComplexityClass) :
    ComplexityClass :=
  { L | ∃ p : Polynomial ℕ, ∃ L' ∈ C,
      L = BitstringDecisionProblem.existentiallyQuantifyOverPolynomial p L' }

notation "∃ᴾ " C => polyExistentiallyQuantify C

/--
The class NP is the set of decision problems
such that there exists a polynomial `p` over ℕ and a poly-time Turing machine
where for all `x`, `L x = true` iff there exists a `w` of length at most `p (|x|)`
such that the Turing machine accepts the pair `(x,w)`.

See Definition 2.1 in Arora-Barak (2009).
-/
def NP : ComplexityClass := ∃ᴾ P

/--
The class coNP is the set of decision problems
whose complements are in NP.
-/
def coNP : ComplexityClass := ∀ᴾ P

@[simp]
lemma polyUniversallyQuantify_complement
    (C : ComplexityClass) :
    (∀ᴾ C).complement = ∃ᴾ (C.complement) := by
  unfold complement polyExistentiallyQuantify polyUniversallyQuantify
  ext L
  simp only [Set.mem_setOf_eq]
  refine exists_congr ?_
  intro p
  constructor
  · intro ⟨L', hL', h_eq⟩
    replace h_eq : Lᶜᶜ = BitstringDecisionProblem.existentiallyQuantifyOverPolynomial p L'ᶜ := by
      rw [h_eq]
      simp
    use L'ᶜ
    simp only [compl_compl] at *
    exact And.symm ⟨h_eq, hL'⟩
  · intro ⟨L', hL', h_eq⟩
    replace h_eq : Lᶜ = BitstringDecisionProblem.universallyQuantifyOverPolynomial p L'ᶜ := by
      rw [h_eq]
      simp
    use L'ᶜ

@[simp]
lemma polyExistentiallyQuantify_complement
    (C : ComplexityClass) :
    (∃ᴾ C).complement = ∀ᴾ (C.complement) := by
  unfold complement polyExistentiallyQuantify polyUniversallyQuantify
  ext L
  simp only [Set.mem_setOf_eq]
  refine exists_congr ?_
  intro p
  constructor
  · intro ⟨L', hL', h_eq⟩
    replace h_eq : Lᶜᶜ = BitstringDecisionProblem.universallyQuantifyOverPolynomial p L'ᶜ := by
      rw [h_eq]
      simp
    use L'ᶜ
    simp only [compl_compl] at *
    exact And.symm ⟨h_eq, hL'⟩
  · intro ⟨L', hL', h_eq⟩
    replace h_eq : Lᶜ = BitstringDecisionProblem.existentiallyQuantifyOverPolynomial p L'ᶜ := by
      rw [h_eq]
      simp
    use L'ᶜ

lemma complement_mono
    {C D : ComplexityClass} (h : C ⊆ D) :
    C.complement ⊆ D.complement := by
  unfold complement
  simp only [Set.subset_def]
  intro L hL
  simp only [Set.mem_setOf_eq] at hL ⊢
  exact h hL

lemma complement_mono_iff
    {C D : ComplexityClass} :
    C ⊆ D ↔ C.complement ⊆ D.complement := by
  constructor
  · exact complement_mono
  · intro h
    have h' := complement_mono h
    rw [complement_complement C, complement_complement D] at h'
    exact h'

lemma polyUniversallyQuantify_mono
    {C D : ComplexityClass} (h : C ⊆ D) :
    (∀ᴾ C) ⊆ (∀ᴾ D) := by
  unfold polyUniversallyQuantify
  simp only [Set.subset_def]
  intro L hL
  rcases hL with ⟨p, L', hL', h_eq⟩
  use p
  use L'
  exact ⟨h hL', h_eq⟩

lemma polyExistentiallyQuantify_mono
    {C D : ComplexityClass} (h : C ⊆ D) :
    (∃ᴾ C) ⊆ (∃ᴾ D) := by
  unfold polyExistentiallyQuantify
  simp only [Set.subset_def]
  intro L hL
  rcases hL with ⟨p, L', hL', h_eq⟩
  use p
  use L'
  exact ⟨h hL', h_eq⟩


lemma P_subset_NP : P ⊆ NP := by
  unfold NP
  unfold polyExistentiallyQuantify
  intro L hL
  simp only [Set.mem_setOf_eq]
  use 0
  -- TODO requires proving that pairing operations are poly-time
  sorry

lemma P_subset_coNP : P ⊆ coNP := by
  unfold coNP
  rw [complement_mono_iff]
  simp only [P_complement, polyUniversallyQuantify_complement]
  exact P_subset_NP

/--
The Sigma levels of the polynomial time hierarchy.

Σᴾ 0 = P
Σᴾ n+1 = ∃ᴾ (Σᴾ n).complement
-/
def SigmaPolyTimeHierarchy : ℕ → ComplexityClass
  | 0     => P
  | n + 1 => (SigmaPolyTimeHierarchy n).complement.polyExistentiallyQuantify

/--
The Pi levels of the polynomial time hierarchy, defined as the complement of the Sigma levels.

Πᴾ n = (Σᴾ n).complement
-/
def PiPolyTimeHierarchy (n : ℕ) : ComplexityClass :=
  (SigmaPolyTimeHierarchy n).complement

-- TODO bind more tightly
scoped notation "Σᴾ" => SigmaPolyTimeHierarchy
scoped notation "Πᴾ" => PiPolyTimeHierarchy

def PolyTimeHierarchy : ComplexityClass :=
  { L | ∃ n : ℕ, L ∈ Σᴾ n }

@[simp]
lemma SigmaPolyTimeHierarchy_zero : Σᴾ 0 = P := rfl

@[simp]
lemma PiPolyTimeHierarchy_zero : Πᴾ 0 = P.complement := rfl

@[simp]
lemma SigmaPolyTimeHierarchy_one : Σᴾ 1 = NP := by
  simp [SigmaPolyTimeHierarchy, NP]

@[simp]
lemma PiPolyTimeHierarchy_one : Πᴾ 1 = coNP := by
  simp [PiPolyTimeHierarchy, coNP, NP]

lemma SigmaPolyTimeHierarchy_succ
    (n : ℕ) : Σᴾ (n + 1) = ∃ᴾ (Πᴾ n) := by
  simp only [SigmaPolyTimeHierarchy, PiPolyTimeHierarchy]

lemma PiPolyTimeHierarchy_succ
    (n : ℕ) : Πᴾ (n + 1) = ∀ᴾ (Σᴾ n) := by
  simp only [PiPolyTimeHierarchy, SigmaPolyTimeHierarchy,
    complement_complement,
    polyExistentiallyQuantify_complement]

@[simp]
lemma PiPolyTimeHierarchy_complement
    (n : ℕ) : (Πᴾ n).complement = Σᴾ n := by
  simp [PiPolyTimeHierarchy, complement_complement]

@[simp]
lemma SigmaPolyTimeHierarchy_complement
    (n : ℕ) : (Σᴾ n).complement = Πᴾ n := by
  simp [PiPolyTimeHierarchy]

private lemma PolyTimeHierarchy_subset_aux (n : ℕ) :
    (Πᴾ n) ⊆ (Πᴾ (n + 1)) ∧ (Σᴾ n) ⊆ Σᴾ (n + 1) := by
  induction n with
  | zero =>
    simp only [SigmaPolyTimeHierarchy_succ, PiPolyTimeHierarchy_succ]
    simp only [PiPolyTimeHierarchy_zero, P_complement, SigmaPolyTimeHierarchy_zero]
    constructor
    · exact P_subset_coNP
    · exact P_subset_NP
  | succ n ih =>
    simp only [SigmaPolyTimeHierarchy_succ, PiPolyTimeHierarchy_succ] at *
    obtain ⟨ih_pi, ih_sigma⟩ := ih
    constructor
    · apply polyUniversallyQuantify_mono
      exact ih_sigma
    · apply polyExistentiallyQuantify_mono
      exact ih_pi

/--
Pi n contained in Pi n+1
-/
lemma PiPolyTimeHierarchy_subset_PiPolyTimeHierarchy_succ
    (n : ℕ) : (Πᴾ n) ⊆ Πᴾ (n + 1) := by
  exact (PolyTimeHierarchy_subset_aux n).1

/--
Sigma n contained in Sigma n+1
-/
lemma SigmaPolyTimeHierarchy_subset_SigmaPolyTimeHierarchy_succ
    (n : ℕ) : (Σᴾ n) ⊆ Σᴾ (n + 1) := by
  exact (PolyTimeHierarchy_subset_aux n).2

lemma PolyTimeHierarchy_eq_union_sigma :
  PolyTimeHierarchy = ⋃ n : ℕ, Σᴾ n := by
  ext L
  simp [PolyTimeHierarchy]

end ComplexityClass

end ComplexityTheory
