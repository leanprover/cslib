/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Marco Peressotti, Alexandre Rademaker
-/

module

public import Cslib.Foundations.Semantics.LTS.Bisimulation
public import Cslib.Foundations.Semantics.Frame.LTS
public import Cslib.Logics.Modal.Semantics
public import Cslib.Logics.Modal.Unary.LTS

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

namespace Cslib.Logic.Modal

open PFunctor

namespace HML

/-- Propositions. -/
abbrev Proposition (Label Atom : Type*) := Modal.Proposition (mkUnary Label) Atom

/-- Finite conjunction of propositions. -/
@[simp, scoped grind =]
def Proposition.finiteAnd (φs : List (Proposition Label Atom)) : Proposition Label Atom :=
  List.foldr (· ∧ ·) ⊤ φs

/-- Finite disjunction of propositions. -/
@[simp, scoped grind =]
def Proposition.finiteOr (φs : List (Proposition Label Atom)) : Proposition Label Atom :=
  List.foldr (· ∨ ·) ⊥ φs

end HML

open Model HML LTS
open scoped HML.Proposition Modal.Proposition InferenceSystem Satisfies Frame LTS

variable {lts : LTS State Label} {v : State → Atom → Prop}

/-- A state satisfies a finite conjunction iff it satisfies all conjuncts. -/
@[scoped grind =]
theorem Satisfies.finiteAnd_iff_forall :
    ⇓Modal[ofLTS lts v,s ⊨ Proposition.finiteAnd φs] ↔ ∀ φ ∈ φs, ⇓Modal[ofLTS lts v,s ⊨ φ] := by
  induction φs <;> grind

/-- A state satisfies a finite disjunction iff it satisfies some disjunct. -/
@[scoped grind =]
theorem Satisfies.finiteOr_iff_exists :
    ⇓Modal[ofLTS lts v,s ⊨ Proposition.finiteOr φs] ↔ ∃ φ ∈ φs, ⇓Modal[ofLTS lts v,s ⊨ φ] := by
  induction φs <;> grind

section ImageToPropositions

variable {s : State} {μ : Label} {lts : LTS State Label}
  (stateMap : lts.image s μ → HML.Proposition Label Atom)
  [finImage : Fintype (lts.image s μ)]

/-- The list of propositions over finite μ-derivatives. -/
noncomputable def propositions : List (HML.Proposition Label Atom) :=
  finImage.elems.toList.map stateMap

theorem propositions_complete (s' : lts.image s μ) : stateMap s' ∈ propositions stateMap := by
  apply List.mem_map.mpr
  use s', Finset.mem_toList.mpr (Fintype.complete s')

theorem propositions_satisfies_conjunction (htr : lts.Tr s1 μ s1')
    (hdist_spec : ∀ s2', ⇓Modal[ofLTS lts v,s1' ⊨ (stateMap s2')]) :
    ⇓Modal[ofLTS lts v,s1 ⊨ d⟨μ⟩(Proposition.finiteAnd (propositions stateMap))] := by
  rw [Satisfies.dynDiamond_iff_exists]
  use s1', htr
  rw [Satisfies.finiteAnd_iff_forall]
  intro φ hφ_mem
  grind [List.mem_map.mp hφ_mem]

end ImageToPropositions

/-- Theory equivalence is a bisimulation. -/
theorem theoryEq_isBisimulation
    [image_finite : ∀ s μ, Finite (lts.image s μ)] :
    lts.IsHomBisimulation (TheoryEq (ofLTS lts v)) := by
  intro s1 s2 h μ
  let (s : State) := @Fintype.ofFinite (lts.image s μ) (image_finite s μ)
  constructor
  case left =>
    intro s1' htr
    by_contra
    have hdist : ∀ s2' : lts.image s2 μ, ∃ φ, ⇓Modal[ofLTS lts v,s1' ⊨ φ] ∧
        ¬⇓Modal[ofLTS lts v,s2'.val ⊨ φ] := by
      intro ⟨s2', hs2'⟩
      apply not_theoryEq_satisfies
      grind
    choose dist_formula hdist_spec using hdist
    let conjunction := Proposition.finiteAnd (propositions dist_formula)
    have hs1_diamond : ⇓Modal[ofLTS lts v,s1 ⊨ d⟨μ⟩conjunction] := by
      grind [propositions_satisfies_conjunction]
    obtain ⟨s2'', htr2, hsat⟩ := Satisfies.dynDiamond_iff_exists.mp
      (theoryEq_satisfies h hs1_diamond)
    grind [propositions_complete dist_formula ⟨s2'', htr2⟩]
  case right =>
    -- Symmetric to left case
    intro s2' htr
    by_contra
    have hdist : ∀ s1' : lts.image s1 μ, ∃ a, ⇓Modal[ofLTS lts v, s2' ⊨ a] ∧
        ¬⇓Modal[ofLTS lts v, s1'.val ⊨ a] := by
      intro ⟨s1', hs1'⟩
      apply not_theoryEq_satisfies
      grind
    choose dist_formula hdist_spec using hdist
    let conjunction := Proposition.finiteAnd (propositions dist_formula)
    have hs2_diamond : ⇓Modal[ofLTS lts v,s2 ⊨ d⟨μ⟩conjunction] := by
      grind [propositions_satisfies_conjunction]
    obtain ⟨s1'', htr1, hsat⟩ :=
      Satisfies.dynDiamond_iff_exists.mp (theoryEq_satisfies h.symm hs2_diamond)
    grind [propositions_complete dist_formula ⟨s1'', htr1⟩]

/-- If two states are in a bisimulation, one satisfies a proposition iff the other does. -/
lemma bisimulation_satisfies {hrb : lts.IsHomBisimulation r}
    (hv : ∀ {s1 s2}, r s1 s2 → ∀ p, v s1 p ↔ v s2 p) (hr : r s1 s2)
    (φ : HML.Proposition Label Atom) :
    ⇓Modal[ofLTS lts v,s1 ⊨ φ] ↔ ⇓Modal[ofLTS lts v,s2 ⊨ φ] := by
  induction φ generalizing s1 s2 with
  | triangle =>
    rw [Proposition.triangle_def, Proposition.unary_triangle_eq_dynDiamond]
    grind only [IsBisimulation, Satisfies.ofLTS_dynDiamond_iff_exists]
  | _ => grind

lemma bisimulation_theoryEq {hrb : lts.IsHomBisimulation r}
    (hv : ∀ {s1 s2}, r s1 s2 → ∀ p, v s1 p ↔ v s2 p) (hr : r s1 s2) :
    TheoryEq (ofLTS lts v) s1 s2 := by grind [bisimulation_satisfies]

/-- Theory equivalence and bisimilarity coincide for image-finite LTSs. -/
theorem theoryEq_eq_bisimilarity
    [image_finite : ∀ s μ, Finite (lts.image s μ)]
    (hv : ∀ {s1 s2}, s1 ~[lts] s2 → ∀ p, v s1 p ↔ v s2 p := by grind) :
    TheoryEq (ofLTS lts v) = HomBisimilarity lts := by
  ext s1 s2
  apply Iff.intro <;> intro h
  · exact ⟨TheoryEq (ofLTS lts v), h, theoryEq_isBisimulation⟩
  · grind [bisimulation_satisfies]

end Cslib.Logic.Modal
