/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Marco Peressotti, Alexandre Rademaker
-/

module

public import Cslib.Foundations.Semantics.LTS.Bisimulation

@[expose] public section

/-! # Hennessy-Milner Logic (HML)

Hennessy-Milner Logic (HML) is a logic for reasoning about the behaviour of nondeterministic and
concurrent systems.

## Implementation notes
There are two main versions of HML. The original [Hennessy1985], which includes a negation
connective, and a variation without negation, for example as in [Aceto1999].
We follow the latter, which is used in many recent papers. Negation is recovered as usual, by having
a `false` atomic proposition and a function that, given any proposition, returns its negated form
(see `Proposition.neg`).

## Main definitions

- `Proposition`: the language of propositions.
- `Satisfies lts s a`: in the LTS `lts`, the state `s` satisfies the proposition `a`.
- `denotation a`: the denotation of a proposition `a`, defined as the set of states that
satisfy `a`.
- `theory lts s`: the set of all propositions satisfied by state `s` in the LTS `lts`.

## Main statements

- `satisfies_mem_denotation`: the denotational semantics of HML is correct, in the sense that it
coincides with the notion of satisfiability.
- `not_theoryEq_satisfies`: if two states have different theories, then there exists a
distinguishing proposition that one state satisfies and the other does not.
- `theoryEq_eq_bisimilarity`: two states have the same theory iff they are bisimilar
(see `Bisimilarity`).

## References

* [M. Hennessy, R. Milner, *Algebraic Laws for Nondeterminism and Concurrency*][Hennessy1985]
* [L. Aceto, A. Ingólfsdóttir, *Testing Hennessy-Milner Logic with Recursion*][Aceto1999]

-/

namespace Cslib.Logic.HML

/-- Propositions. -/
inductive Proposition (Label : Type u) : Type u where
  | true
  | false
  | and (φ₁ φ₂ : Proposition Label)
  | or (φ₁ φ₂ : Proposition Label)
  | diamond (μ : Label) (φ : Proposition Label)
  | box (μ : Label) (φ : Proposition Label)

/-- Negation of a proposition. -/
@[simp, scoped grind =]
def Proposition.neg (a : Proposition Label) : Proposition Label :=
  match a with
  | .true => .false
  | .false => .true
  | and a b => or a.neg b.neg
  | or a b => and a.neg b.neg
  | diamond μ a => box μ a.neg
  | box μ a => diamond μ a.neg

/-- Finite conjunction of propositions. -/
@[simp, scoped grind =]
def Proposition.finiteAnd (as : List (Proposition Label)) : Proposition Label :=
  List.foldr .and .true as

/-- Finite disjunction of propositions. -/
@[simp, scoped grind =]
def Proposition.finiteOr (as : List (Proposition Label)) : Proposition Label :=
  List.foldr .or .false as

/-- Satisfaction relation. `Satisfies lts s a` means that, in the LTS `lts`, the state `s` satisfies
the proposition `a`. -/
@[scoped grind]
inductive Satisfies (lts : LTS State Label) : State → Proposition Label → Prop where
  | true {s : State} : Satisfies lts s .true
  | and {s : State} {a b : Proposition Label} :
    Satisfies lts s a → Satisfies lts s b →
    Satisfies lts s (.and a b)
  | or₁ {s : State} {a b : Proposition Label} :
    Satisfies lts s a → Satisfies lts s (.or a b)
  | or₂ {s : State} {a b : Proposition Label} :
    Satisfies lts s b → Satisfies lts s (.or a b)
  | diamond {s s' : State} {μ : Label} {a : Proposition Label}
    (htr : lts.Tr s μ s') (hs : Satisfies lts s' a) : Satisfies lts s (.diamond μ a)
  | box {s : State} {μ : Label} {a : Proposition Label}
    (h : ∀ s', lts.Tr s μ s' → Satisfies lts s' a) :
    Satisfies lts s (.box μ a)

/-- Denotation of a proposition. -/
@[simp, scoped grind =]
def Proposition.denotation (a : Proposition Label) (lts : LTS State Label)
    : Set State :=
  match a with
  | .true => Set.univ
  | .false => ∅
  | .and a b => a.denotation lts ∩ b.denotation lts
  | .or a b => a.denotation lts ∪ b.denotation lts
  | .diamond μ a => {s | ∃ s', lts.Tr s μ s' ∧ s' ∈ a.denotation lts}
  | .box μ a => {s | ∀ s', lts.Tr s μ s' → s' ∈ a.denotation lts}

/-- The theory of a state is the set of all propositions that it satifies. -/
abbrev theory (lts : LTS State Label) (s : State) : Set (Proposition Label) :=
  {a | Satisfies lts s a}

/-- Two states are theory-equivalent (for a specific LTS) if they have the same theory. -/
abbrev TheoryEq (lts : LTS State Label) (s1 s2 : State) :=
  theory lts s1 = theory lts s2

open Proposition LTS Bisimulation Simulation

/-- Characterisation theorem for the denotational semantics. -/
@[scoped grind =]
theorem satisfies_mem_denotation {lts : LTS State Label} :
    Satisfies lts s a ↔ s ∈ a.denotation lts := by
  induction a generalizing s <;> grind

/-- A state satisfies a proposition iff it does not satisfy the negation of the proposition. -/
@[simp, scoped grind =]
theorem neg_satisfies {lts : LTS State Label} :
    ¬Satisfies lts s a.neg ↔ Satisfies lts s a := by
  induction a generalizing s <;> grind

/-- A state is in the denotation of a proposition iff it is not in the denotation of the negation
of the proposition. -/
@[scoped grind =]
theorem neg_denotation {lts : LTS State Label} (a : Proposition Label) :
    s ∉ a.neg.denotation lts ↔ s ∈ a.denotation lts := by
  grind [_=_ satisfies_mem_denotation]

/-- A state satisfies a finite conjunction iff it satisfies all conjuncts. -/
@[scoped grind =]
theorem satisfies_finiteAnd {lts : LTS State Label} {s : State}
    {as : List (Proposition Label)} :
    Satisfies lts s (Proposition.finiteAnd as) ↔ ∀ a ∈ as, Satisfies lts s a := by
  induction as <;> grind

/-- A state satisfies a finite disjunction iff it satisfies some disjunct. -/
@[scoped grind =]
theorem satisfies_finiteOr {lts : LTS State Label} {s : State}
    {as : List (Proposition Label)} :
    Satisfies lts s (Proposition.finiteOr as) ↔ ∃ a ∈ as, Satisfies lts s a := by
  induction as <;> grind

@[scoped grind →]
theorem satisfies_theory (h : Satisfies lts s a) : a ∈ theory lts s := by
  grind

/-- Two states are theory-equivalent iff they are denotationally equivalent. -/
theorem theoryEq_denotation_eq {lts : LTS State Label} :
    TheoryEq lts s1 s2 ↔
    (∀ a : Proposition Label, s1 ∈ a.denotation lts ↔ s2 ∈ a.denotation lts) := by
  grind [_=_ satisfies_mem_denotation]

/-- If two states are not theory equivalent, there exists a distinguishing proposition. -/
lemma not_theoryEq_satisfies (h : ¬ TheoryEq lts s1 s2) :
    ∃ a, (Satisfies lts s1 a ∧ ¬Satisfies lts s2 a) := by
  grind [=_ neg_satisfies]

/-- If two states are theory equivalent and the former satisfies a proposition, the latter does as
well. -/
theorem theoryEq_satisfies {lts : LTS State Label} (h : TheoryEq lts s1 s2)
    (hs : Satisfies lts s1 a) : Satisfies lts s2 a := by
  unfold TheoryEq theory at h
  rw [Set.ext_iff] at h
  exact (h a).mp hs

section ImageToPropositions

variable {lts : LTS State Label} (stateMap : lts.image s μ → Proposition Label)
variable [finImage : Fintype (lts.image s μ)]

/-- The list of propositions over finite μ-derivatives. -/
noncomputable def propositions : List (Proposition Label) :=
  finImage.elems.toList.map stateMap

theorem propositions_complete (s' : lts.image s μ) : stateMap s' ∈ propositions stateMap := by
  apply List.mem_map.mpr
  use s', Finset.mem_toList.mpr (Fintype.complete s')

theorem propositions_satisfies_conjunction (htr : lts.Tr s1 μ s1')
  (hdist_spec : ∀ s2', Satisfies lts s1' (stateMap s2')) :
    Satisfies lts s1 (.diamond μ <| Proposition.finiteAnd (propositions stateMap)) := by
  apply Satisfies.diamond htr
  rw [satisfies_finiteAnd]
  intro a ha_mem
  grind [List.mem_map.mp ha_mem]

end ImageToPropositions

/-- Theory equivalence is a bisimulation. -/
@[scoped grind ⇒]
theorem theoryEq_isBisimulation (lts : LTS State Label)
    [image_finite : ∀ s μ, Finite (lts.image s μ)] :
    lts.IsBisimulation (TheoryEq lts) := by
  intro s1 s2 h μ
  let (s : State) := @Fintype.ofFinite (lts.image s μ) (image_finite s μ)
  constructor
  case left =>
    intro s1' htr
    by_contra
    have hdist : ∀ s2' : lts.image s2 μ, ∃ a, Satisfies lts s1' a ∧ ¬Satisfies lts s2'.val a := by
      intro ⟨s2', hs2'⟩
      apply not_theoryEq_satisfies
      grind
    choose dist_formula hdist_spec using hdist
    let conjunction := Proposition.finiteAnd (propositions dist_formula)
    have hs1_diamond : Satisfies lts s1 (.diamond μ conjunction) := by
      grind [propositions_satisfies_conjunction]
    cases (theoryEq_satisfies h hs1_diamond) with | @diamond _ s2'' _ _ htr2 hsat =>
    grind [propositions_complete dist_formula ⟨s2'', htr2⟩]
  case right =>
    -- Symmetric to left case
    intro s2' htr
    by_contra
    have hdist : ∀ s1' : lts.image s1 μ, ∃ a, Satisfies lts s2' a ∧ ¬Satisfies lts s1'.val a := by
      intro ⟨s1', hs1'⟩
      apply not_theoryEq_satisfies
      grind
    choose dist_formula hdist_spec using hdist
    let conjunction := Proposition.finiteAnd (propositions dist_formula)
    have hs2_diamond : Satisfies lts s2 (.diamond μ conjunction) := by
      grind [propositions_satisfies_conjunction]
    cases (theoryEq_satisfies h.symm hs2_diamond) with | @diamond _ s1'' _ _ htr1 hsat =>
    grind [propositions_complete dist_formula ⟨s1'', htr1⟩]

/-- If two states are in a bisimulation and the former satisfies a proposition, the latter does as
well. -/
@[scoped grind ⇒]
lemma bisimulation_satisfies {lts : LTS State Label}
    {hrb : lts.IsBisimulation r}
    (hr : r s1 s2) (a : Proposition Label) (hs : Satisfies lts s1 a) :
    Satisfies lts s2 a := by
  induction a generalizing s1 s2 with
  | diamond => cases hs with | diamond htr _ => grind [hrb.follow_fst hr htr]
  | _ => grind

lemma bisimulation_TheoryEq {lts : LTS State Label}
    {hrb : lts.IsBisimulation r}
    (hr : r s1 s2) :
    TheoryEq lts s1 s2 := by
  have : s2 ~[lts] s1 := by grind [Bisimilarity.symm]
  grind

/-- Theory equivalence and bisimilarity coincide for image-finite LTSs. -/
theorem theoryEq_eq_bisimilarity (lts : LTS State Label)
    [image_finite : ∀ s μ, Finite (lts.image s μ)] :
    TheoryEq lts = Bisimilarity lts := by
  ext s1 s2
  apply Iff.intro <;> intro h
  · exists TheoryEq lts
    grind
  · obtain ⟨r, hr, hrb⟩ := h
    apply bisimulation_TheoryEq hr
    exact hrb

end Cslib.Logic.HML
