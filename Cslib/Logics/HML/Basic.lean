/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Marco Peressotti, Alexandre Rademaker
-/

module

public import Cslib.Foundations.Semantics.LTS.Bisimulation
public import Cslib.Foundations.Logic.Operators
public import Cslib.Foundations.Logic.InferenceSystem

/-! # Hennessy-Milner Logic (HML)

Hennessy-Milner Logic (HML) is a logic for reasoning about the behaviour of nondeterministic and
concurrent systems.

## Implementation notes
There are two main versions of HML. The original [Hennessy1985], which includes a negation
connective, and a variation without negation, for example as in [Aceto1999].
We follow the former and focus on a minimal set of connectives, recovering the others as derived
constructs.

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

@[expose] public section

namespace Cslib.Logic.HML

/-- Propositions. -/
inductive Proposition (Label : Type u) : Type u where
  /-- Truth. -/
  | true
  /-- Conjunction. -/
  | and (φ₁ φ₂ : Proposition Label)
  /-- Negation. -/
  | not (φ : Proposition Label)
  /-- Possibility (dynamic diamond modality). -/
  | diamond (μ : Label) (φ : Proposition Label)

instance : Top (Proposition Label) := ⟨.true⟩
instance : HasAnd (Proposition Label) := ⟨.and⟩
instance : HasNot (Proposition Label) := ⟨.not⟩
instance : HasDynamicDiamond (Proposition Label) Label := ⟨.diamond⟩

/-- Falsity, derived from negation and truth. -/
@[match_pattern]
def Proposition.false : Proposition Label := ¬⊤

instance : Bot (Proposition Label) := ⟨.false⟩

/-- Disjunction, derived from negation and conjunction. -/
@[match_pattern]
def Proposition.or (φ₁ φ₂ : Proposition Label) : Proposition Label := ¬(¬φ₁ ∧ ¬φ₂)

instance : HasOr (Proposition Label) := ⟨Proposition.or⟩

/-- Implication. -/
@[match_pattern]
def Proposition.imp (φ₁ φ₂ : Proposition Label) : Proposition Label := ¬φ₁ ∨ φ₂

instance : HasImp (Proposition Label) := ⟨.imp⟩

/-- Bi-implication. -/
@[match_pattern]
def Proposition.iff (φ₁ φ₂ : Proposition Label) : Proposition Label := (φ₁ → φ₂) ∧ (φ₂ → φ₁)

instance : HasIff (Proposition Label) := ⟨.iff⟩

/-- Necessity (dynamic box modality), derived from dynamic diamond and negation. -/
@[match_pattern]
def Proposition.box (μ : Label) (φ : Proposition Label) : Proposition Label := ¬d⟨μ⟩¬φ

instance : HasDynamicBox (Proposition Label) Label := ⟨.box⟩

@[scoped grind =]
lemma Proposition.top_def : .true = ((⊤ : Proposition Label)) := rfl

@[scoped grind =]
lemma Proposition.bot_def : .false = ((⊥ : Proposition Label)) := rfl

@[scoped grind =]
lemma Proposition.and_def (φ₁ φ₂ : Proposition Label) : φ₁.and φ₂ = (φ₁ ∧ φ₂) := rfl

@[scoped grind =]
lemma Proposition.not_def (φ : Proposition Label) : φ.not = ¬φ := rfl

@[scoped grind =]
lemma Proposition.diamond_def (μ : Label) (φ : Proposition Label) :
  Proposition.diamond μ φ = d⟨μ⟩φ := rfl

@[scoped grind =]
lemma Proposition.or_def (φ₁ φ₂ : Proposition Label) : φ₁.or φ₂ = (φ₁ ∨ φ₂) := rfl

@[scoped grind =]
lemma Proposition.imp_def (φ₁ φ₂ : Proposition Label) : φ₁.imp φ₂ = (φ₁ → φ₂) := rfl

@[scoped grind =]
lemma Proposition.iff_def (φ₁ φ₂ : Proposition Label) :
    φ₁.iff φ₂ = (φ₁ ↔ φ₂) := rfl

@[scoped grind =]
lemma Proposition.box_def (μ : Label) (φ : Proposition Label) : Proposition.box μ φ = d[μ]φ := rfl

/-- Finite conjunction of propositions. -/
@[simp, scoped grind =]
def Proposition.finiteAnd (φs : List (Proposition Label)) : Proposition Label :=
  List.foldr (· ∧ ·) ⊤ φs

/-- Finite disjunction of propositions. -/
@[simp, scoped grind =]
def Proposition.finiteOr (φs : List (Proposition Label)) : Proposition Label :=
  List.foldr (· ∨ ·) ⊥ φs

/-- Satisfaction relation. `Satisfies lts s φ` means that, in the LTS `lts`, the state `s` satisfies
the proposition `φ`. -/
@[scoped grind]
def Satisfies (lts : LTS State Label) (s : State) : Proposition Label → Prop
  | .true => True
  | .and φ₁ φ₂ => Satisfies lts s φ₁ ∧ Satisfies lts s φ₂
  | .not φ => ¬Satisfies lts s φ
  | .diamond μ φ => ∃ s', lts.Tr s μ s' ∧ Satisfies lts s' φ

/-- Judgement, representing the conclusions one reaches in HML. -/
structure Judgement State Label where
  /-- Constructs a judgement. -/
  mk ::
  /-- LTS. -/
  lts : LTS State Label
  /-- The state satisfying the proposition `φ`. -/
  state : State
  /-- The proposition satisfied by the state `s`. -/
  φ : Proposition Label

@[inherit_doc] scoped notation "HML[" lts "," s " ⊨ " φ "]" => Judgement.mk lts s φ

/-- Satisfaction for judgements. This just refers to the unbundled `Satisfies`. -/
@[simp, scoped grind =]
def Satisfies.Bundled (j : Judgement State Label) : Prop := Satisfies j.lts j.state j.φ

instance : HasInferenceSystem (Judgement State Label) := ⟨Satisfies.Bundled⟩

open scoped InferenceSystem Proposition

@[scoped grind =]
theorem derivation_def : Satisfies lts s φ = ⇓HML[lts,s ⊨ φ] := rfl

@[scoped grind =]
theorem Satisfies.not_iff_not : ⇓HML[lts,s ⊨ ¬φ] ↔ ¬⇓HML[lts,s ⊨ φ] := by rfl

@[scoped grind .]
theorem Satisfies.top : ⇓HML[lts,s ⊨ ⊤] := by
  dsimp [Top.top]
  grind [=_ derivation_def]

@[scoped grind .]
theorem Satisfies.bot : ¬⇓HML[lts,s ⊨ ⊥] := by
  simp only [Bot.bot]
  grind [= Proposition.false]

@[scoped grind =]
theorem Satisfies.and_iff_and :
    ⇓HML[lts,s ⊨ φ₁ ∧ φ₂] ↔ ⇓HML[lts,s ⊨ φ₁] ∧ ⇓HML[lts,s ⊨ φ₂] := by rfl

@[scoped grind =]
theorem Satisfies.or_iff_or :
    ⇓HML[lts,s ⊨ φ₁ ∨ φ₂] ↔ ⇓HML[lts,s ⊨ φ₁] ∨ ⇓HML[lts,s ⊨ φ₂] := by
  grind [=_ Proposition.or_def, Proposition.or]

@[scoped grind =]
theorem Satisfies.diamond_iff_exists :
    ⇓HML[lts,s ⊨ d⟨μ⟩φ] ↔ ∃ s', lts.Tr s μ s' ∧ ⇓HML[lts,s' ⊨ φ] := by rfl

/-- Characterisation of the `→` connective.

Implication is defined in terms of the more primitive connectives given in `Proposition`.
This result proves that the definition is correct.
-/
@[scoped grind =]
theorem Satisfies.imp_iff_imp :
    ⇓HML[lts,s ⊨ φ₁ → φ₂] ↔ (⇓HML[lts,s ⊨ φ₁] → ⇓HML[lts,s ⊨ φ₂]) := by
  grind [=_ Proposition.imp_def, Proposition.imp]

/-- Characterisation of the `↔` connective.

Bi-implication is defined in terms of the more primitive connectives given in `Proposition`.
This result proves that the definition is correct. -/
@[scoped grind =]
theorem Satisfies.iff_iff_iff :
    ⇓HML[lts,s ⊨ φ₁ ↔ φ₂] ↔ (⇓HML[lts,s ⊨ φ₁] ↔ ⇓HML[lts,s ⊨ φ₂]) := by
  simp only [HasIff.iff, Proposition.iff]
  grind

@[scoped grind =]
theorem Satisfies.box_iff_forall :
    ⇓HML[lts,s ⊨ d[μ]φ] ↔ ∀ s', lts.Tr s μ s' → ⇓HML[lts,s' ⊨ φ] := by
  grind [=_ Proposition.box_def, Proposition.box]

/-- A state satisfies a finite conjunction iff it satisfies all conjuncts. -/
@[scoped grind =]
theorem Satisfies.finiteAnd_iff_forall :
    ⇓HML[lts,s ⊨ Proposition.finiteAnd φs] ↔ ∀ φ ∈ φs, ⇓HML[lts,s ⊨ φ] := by
  induction φs <;> grind

/-- A state satisfies a finite disjunction iff it satisfies some disjunct. -/
@[scoped grind =]
theorem Satisfies.finiteOr_iff_exists :
    ⇓HML[lts,s ⊨ Proposition.finiteOr φs] ↔ ∃ φ ∈ φs, ⇓HML[lts,s ⊨ φ] := by
  induction φs <;> grind

/-- Denotation of a proposition. -/
@[simp, scoped grind =]
def Proposition.denotation (lts : LTS State Label)
    : Proposition Label → Set State
  | .true => Set.univ
  | .and φ₁ φ₂ => φ₁.denotation lts ∩ φ₂.denotation lts
  | .not φ => (φ.denotation lts)ᶜ
  | .diamond μ φ => {s | ∃ s', lts.Tr s μ s' ∧ s' ∈ φ.denotation lts}

/-- The theory of a state is the set of all propositions that it satisfies. -/
abbrev theory (lts : LTS State Label) (s : State) : Set (Proposition Label) :=
  {φ | ⇓HML[lts,s ⊨ φ]}

/-- Two states are theory-equivalent (for a specific LTS) if they have the same theory. -/
abbrev TheoryEq (lts : LTS State Label) (s1 s2 : State) :=
  theory lts s1 = theory lts s2

open Proposition LTS

/-- Characterisation theorem for the denotational semantics. -/
@[scoped grind =]
theorem mem_denotation_iff_satisfies {φ : Proposition Label} :
    s ∈ φ.denotation lts ↔ ⇓HML[lts,s ⊨ φ] := by
  induction φ generalizing s <;> grind [=_ derivation_def]

@[scoped grind .]
theorem mem_theory_iff_satisfies : φ ∈ theory lts s ↔ ⇓HML[lts,s ⊨ φ] := by
  grind

/- A state satisfies a proposition iff it does not satisfy the negation of the proposition. -/
-- @[simp, scoped grind =]
-- theorem Satisfies.not_not_iff {lts : LTS State Label} :
--   ¬⇓HML[lts,s ⊨ ¬φ] ↔ ⇓HML[lts,s ⊨ φ] := by
--   grind

open scoped Satisfies

/-- A state is in the denotation of a proposition iff it is not in the denotation of the negation
of the proposition. -/
@[scoped grind =]
theorem not_denotation {lts : LTS State Label} (φ : Proposition Label) :
    s ∉ (¬φ).denotation lts ↔ s ∈ φ.denotation lts := by grind

/-- Two states are theory-equivalent iff they are denotationally equivalent. -/
theorem theoryEq_denotation_eq {lts : LTS State Label} :
    TheoryEq lts s1 s2 ↔
    (∀ φ : Proposition Label, s1 ∈ φ.denotation lts ↔ s2 ∈ φ.denotation lts) := by
  grind [=_ mem_theory_iff_satisfies, =_ mem_denotation_iff_satisfies]

/-- If two states are not theory equivalent, there exists a distinguishing proposition. -/
lemma not_theoryEq_satisfies (h : ¬TheoryEq lts s1 s2) :
    ∃ φ, (⇓HML[lts,s1 ⊨ φ] ∧ ¬⇓HML[lts,s2 ⊨ φ]) := by
  grind [=_ Satisfies.not_iff_not]

/-- If two states are theory equivalent and the former satisfies a proposition, the latter does as
well. -/
theorem theoryEq_satisfies (h : TheoryEq lts s1 s2)
    (hs : ⇓HML[lts,s1 ⊨ φ]) : ⇓HML[lts,s2 ⊨ φ] := by
  unfold TheoryEq theory at h
  rw [Set.ext_iff] at h
  exact (h φ).mp hs

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
    (hdist_spec : ∀ s2', ⇓HML[lts,s1' ⊨ (stateMap s2')]) :
    ⇓HML[lts,s1 ⊨ d⟨μ⟩finiteAnd (propositions stateMap)] := by
  rw [Satisfies.diamond_iff_exists]
  use s1', htr
  rw [Satisfies.finiteAnd_iff_forall]
  intro φ hφ_mem
  grind [List.mem_map.mp hφ_mem]

end ImageToPropositions

/-- Theory equivalence is a bisimulation. -/
@[scoped grind ⇒]
theorem theoryEq_isBisimulation (lts : LTS State Label)
    [image_finite : ∀ s μ, Finite (lts.image s μ)] :
    lts.IsHomBisimulation (TheoryEq lts) := by
  intro s1 s2 h μ
  let (s : State) := @Fintype.ofFinite (lts.image s μ) (image_finite s μ)
  constructor
  case left =>
    intro s1' htr
    by_contra
    have hdist : ∀ s2' : lts.image s2 μ, ∃ φ, ⇓HML[lts,s1' ⊨ φ] ∧ ¬⇓HML[lts,s2'.val ⊨ φ] := by
      intro ⟨s2', hs2'⟩
      apply not_theoryEq_satisfies
      grind
    choose dist_formula hdist_spec using hdist
    let conjunction := Proposition.finiteAnd (propositions dist_formula)
    have hs1_diamond : ⇓HML[lts,s1 ⊨ d⟨μ⟩conjunction] := by
      grind [propositions_satisfies_conjunction]
    obtain ⟨s2'', htr2, hsat⟩ := Satisfies.diamond_iff_exists.mp (theoryEq_satisfies h hs1_diamond)
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
    have hs2_diamond : ⇓HML[lts,s2 ⊨ d⟨μ⟩conjunction] := by
      grind [propositions_satisfies_conjunction]
    obtain ⟨s1'', htr1, hsat⟩ :=
      Satisfies.diamond_iff_exists.mp (theoryEq_satisfies h.symm hs2_diamond)
    grind [propositions_complete dist_formula ⟨s1'', htr1⟩]

/-- If two states are in a bisimulation, one satisfies a proposition iff the other does. -/
@[scoped grind ⇒]
lemma bisimulation_satisfies {hrb : lts.IsHomBisimulation r}
    (hr : r s1 s2) (φ : Proposition Label) : ⇓HML[lts,s1 ⊨ φ] ↔ ⇓HML[lts,s2 ⊨ φ] := by
  induction φ generalizing s1 s2 <;> grind [IsBisimulation]

lemma bisimulation_theoryEq {hrb : lts.IsHomBisimulation r} (hr : r s1 s2) :
    TheoryEq lts s1 s2 := by grind

/-- Theory equivalence and bisimilarity coincide for image-finite LTSs. -/
theorem theoryEq_eq_bisimilarity {lts : LTS State Label}
    [image_finite : ∀ s μ, Finite (lts.image s μ)] :
    TheoryEq lts = HomBisimilarity lts := by
  ext s1 s2
  apply Iff.intro <;> intro h
  · exists TheoryEq lts
    grind
  · grind

end Cslib.Logic.HML
