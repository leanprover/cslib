/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Marco Peressotti, Alexandre Rademaker
-/

module

public import Cslib.Foundations.Semantics.LTS.Bisimulation
public import Cslib.Foundations.Semantics.Frame.LTS
public import Cslib.Logics.Modal.Semantics
public import Cslib.Logics.Modal.Unary.Basic

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

/-- An HML model consists of an LTS and a valuation for its states. -/
structure Model State Label Atom where
  /-- The labelled transition system. -/
  lts : LTS State Label
  /-- Valuation of atoms at states. -/
  v : State → Atom → Prop

/-- Converts an HML into a unary modal model. -/
def Model.toModal (m : Model State Label Atom) := Modal.Model.mk m.lts.toFrame m.v

@[simp, scoped grind =, modal =]
theorem Model.toModal_toFrame (m : Model State Label Atom) :
    m.toModal.toFrame = m.lts.toFrame := rfl

/-- Shortcut for `Modal[HML.Model.toModal m,s ⊨ φ]`. -/
scoped notation "HML[" m "," s " ⊨ " φ "]" => Modal[HML.Model.toModal m,s ⊨ φ]

end HML

open Model HML LTS
open scoped HML.Model Modal.Proposition InferenceSystem Satisfies Frame LTS

variable {m : HML.Model State Label Atom}

@[scoped grind =, modal =]
theorem Satisfies.hml_atom_iff {p : Atom} : ⇓HML[m,s ⊨ p] ↔ m.v s p := by rfl

theorem Satisfies.hml_dynDiamond_iff_exists :
    ⇓HML[m,s ⊨ d⟨μ⟩φ] ↔ ∃ s', m.lts.Tr s μ s' ∧ ⇓HML[m,s' ⊨ φ] := by
  rw [Satisfies.dynDiamond_iff_exists]
  simp [HML.Model.toModal]

theorem Satisfies.hml_dynBox_iff_forall :
    ⇓HML[m,s ⊨ d[μ]φ] ↔ ∀ s', m.lts.Tr s μ s' → ⇓HML[m,s' ⊨ φ] := by
  rw [Satisfies.dynBox_iff_forall]
  simp [HML.Model.toModal]

@[modal ⇒]
theorem Satisfies.hml_dynDiamond_intro (htr : m.lts.Tr s μ s')
    (h : ⇓HML[m,s' ⊨ φ]) : ⇓HML[m,s ⊨ d⟨μ⟩φ] := by grind [modal]

@[modal ⇒]
theorem Satisfies.hml_dynBox_elim (hbox : ⇓HML[m,s ⊨ d[μ]φ])
    (htr : m.lts.Tr s μ s') : ⇓HML[m,s' ⊨ φ] := by grind [modal]

section ImageToPropositions

variable {s : State} {μ : Label} {m : HML.Model State Label Atom}
  (stateMap : m.lts.image s μ → HML.Proposition Label Atom)
  [finImage : Fintype (m.lts.image s μ)]

/-- The list of propositions over finite μ-derivatives. -/
noncomputable def propositions : List (HML.Proposition Label Atom) :=
  finImage.elems.toList.map stateMap

theorem propositions_complete (s' : m.lts.image s μ) : stateMap s' ∈ propositions stateMap := by
  apply List.mem_map.mpr
  use s', Finset.mem_toList.mpr (Fintype.complete s')

theorem propositions_satisfies_conjunction (htr : m.lts.Tr s1 μ s1')
    (hdist_spec : ∀ s2', ⇓HML[m,s1' ⊨ (stateMap s2')]) :
    ⇓HML[m,s1 ⊨ d⟨μ⟩(⋀(propositions stateMap))] := by
  rw [Satisfies.dynDiamond_iff_exists]
  use s1', htr
  rw [Satisfies.finiteAnd_iff_forall]
  intro φ hφ_mem
  grind [List.mem_map.mp hφ_mem]

end ImageToPropositions

/-- Theory equivalence is a bisimulation. -/
theorem theoryEq_isBisimulation
    [image_finite : ∀ s μ, Finite (m.lts.image s μ)] :
    m.lts.IsHomBisimulation (TheoryEq m.toModal) := by
  intro s1 s2 h μ
  let (s : State) := @Fintype.ofFinite (m.lts.image s μ) (image_finite s μ)
  constructor
  case left =>
    intro s1' htr
    by_contra
    have hdist : ∀ s2' : m.lts.image s2 μ, ∃ φ, ⇓HML[m,s1' ⊨ φ] ∧
        ¬⇓HML[m,s2'.val ⊨ φ] := by
      intro ⟨s2', hs2'⟩
      apply not_theoryEq_satisfies
      grind
    choose dist_formula hdist_spec using hdist
    let conjunction := ⋀(propositions dist_formula)
    have hs1_diamond : ⇓HML[m,s1 ⊨ d⟨μ⟩conjunction] := by
      grind [propositions_satisfies_conjunction]
    obtain ⟨s2'', htr2, hsat⟩ := Satisfies.dynDiamond_iff_exists.mp
      (theoryEq_satisfies h hs1_diamond)
    grind [propositions_complete dist_formula ⟨s2'', htr2⟩]
  case right =>
    -- Symmetric to left case
    intro s2' htr
    by_contra
    have hdist : ∀ s1' : m.lts.image s1 μ, ∃ a, ⇓HML[m, s2' ⊨ a] ∧
        ¬⇓HML[m, s1'.val ⊨ a] := by
      intro ⟨s1', hs1'⟩
      apply not_theoryEq_satisfies
      grind
    choose dist_formula hdist_spec using hdist
    let conjunction := ⋀(propositions dist_formula)
    have hs2_diamond : ⇓HML[m,s2 ⊨ d⟨μ⟩conjunction] := by
      grind [propositions_satisfies_conjunction]
    obtain ⟨s1'', htr1, hsat⟩ :=
      Satisfies.dynDiamond_iff_exists.mp (theoryEq_satisfies h.symm hs2_diamond)
    grind [propositions_complete dist_formula ⟨s1'', htr1⟩]

/-- If two states are in a bisimulation, one satisfies a proposition iff the other does. -/
lemma bisimulation_satisfies {hrb : m.lts.IsHomBisimulation r}
    (hv : ∀ {s1 s2}, r s1 s2 → ∀ p, m.v s1 p ↔ m.v s2 p) (hr : r s1 s2)
    (φ : HML.Proposition Label Atom) : ⇓HML[m,s1 ⊨ φ] ↔ ⇓HML[m,s2 ⊨ φ] := by
  induction φ generalizing s1 s2 with
  | triangle =>
    rw [Proposition.triangle_def, Proposition.unary_triangle_eq_dynDiamond]
    grind only [IsBisimulation, Satisfies.hml_dynDiamond_iff_exists]
  | _ => grind

lemma bisimulation_theoryEq {hrb : m.lts.IsHomBisimulation r}
    (hv : ∀ {s1 s2}, r s1 s2 → ∀ p, m.v s1 p ↔ m.v s2 p) (hr : r s1 s2) :
    TheoryEq m.toModal s1 s2 := by grind [bisimulation_satisfies]

/-- Theory equivalence and bisimilarity coincide for image-finite LTSs. -/
theorem theoryEq_eq_bisimilarity
    [image_finite : ∀ s μ, Finite (m.lts.image s μ)]
    (hv : ∀ {s1 s2}, s1 ~[m.lts] s2 → ∀ p, m.v s1 p ↔ m.v s2 p := by grind) :
    TheoryEq m.toModal = HomBisimilarity m.lts := by
  ext s1 s2
  apply Iff.intro <;> intro h
  · exact ⟨TheoryEq m.toModal, h, theoryEq_isBisimulation⟩
  · grind [bisimulation_satisfies]

end Cslib.Logic.Modal
