/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.FiniteEquation
public import Cslib.Foundations.RelationAlgebra.IntegralCycleCount

/-!
# Equations and random representability

Maddux's finite-equation theorem fixes a finite set of equations valid in every representable
relation algebra before taking the limit in the number of Boolean atoms. The Random
Representability Conjecture asks whether representable algebras themselves have density one.
Both statements give each isomorphism class equal weight.

## References

* Roger D. Maddux, *Finite integral relation algebras* (1985), Theorem 15, gives the
  finite-equation result for integral algebras. For the passage to all relation algebras see
  [James Koussas, *Finite Relation Algebras*](https://arxiv.org/abs/2202.01959),
  Proposition 13(2) and Corollary 23 of the preprint.
* Roger D. Maddux, *On the Future of RA* (2022), conjecture (2).
-/

@[expose] public section

namespace Cslib.RelationAlgebra

variable {α : Type*}

namespace IsoClass

/-- Satisfaction of an equation by an isomorphism class with `n` atoms. -/
def Satisfies {n : ℕ} (q : ofAtoms n) (e : Equation α) : Prop :=
  Quotient.liftOn q (fun S => e.Holds (ComplexAlgebra S.val)) fun _ _ ⟨f⟩ =>
    propext ⟨e.holds_of_injective f.symm.toHom f.symm.toHom_injective,
      e.holds_of_injective f.toHom f.toHom_injective⟩

@[simp]
theorem satisfies_ofAlgebra {A : Type*} [RelationAlgebra A] [Finite A] {n : ℕ}
    (h : Nat.card {a : A // IsAtom a} = n) (e : Equation α) :
    Satisfies (ofAlgebra h) e ↔ e.Holds A :=
  let iso := labelledEquiv h
  ⟨e.holds_of_injective iso.toHom iso.toHom_injective,
    e.holds_of_injective iso.symm.toHom iso.symm.toHom_injective⟩

/-- Representability of an isomorphism class with `n` atoms, allowing infinite bases. -/
def IsRepresentable {n : ℕ} (q : ofAtoms n) : Prop :=
  Quotient.liftOn q (fun S => Representable (ComplexAlgebra S.val)) fun _ _ ⟨f⟩ =>
    propext f.representable_iff

open Filter
open scoped Topology

/-- It suffices to verify the equations on symmetric tables with a fixed common-witness bound.
All classes in the resulting lower bound are counted without labellings. -/
theorem tendsto_satisfying_of_commonWitnesses (E : Finset (Equation α)) {k : ℕ} (hk : 2 ≤ k)
    (h : ∀ (d : ℕ) (_ : 0 < d) (T : SymmetricCycles.Table (Fin d))
      [LawfulAtomStructure (SymmetricCycles.atomStructure T)],
      SymmetricCycles.HasCommonWitnesses k T →
      ∀ e ∈ E, e.Holds (ComplexAlgebra (SymmetricCycles.atomStructure T))) :
    Tendsto (fun n => (Nat.card {q : ofAtoms n // ∀ e ∈ E, Satisfies q e} : ℝ) /
      Nat.card (ofAtoms n)) atTop (𝓝 1) := by
  apply (tendsto_add_atTop_iff_nat 1).mp
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (IntegralAtom.tendsto_witness_orbits_div_all k)
    tendsto_const_nhds
  · filter_upwards [eventually_gt_atTop 0] with d hd
    let X := {q : SymmetricCycles.UnlabelledTable (Fin d) // q.HasCommonWitnesses k}
    have hw (x : X) := SymmetricCycles.UnlabelledTable.hasCommonWitnesses_out.mpr x.prop
    let f (x : X) : {q : SymmetricCycles.UnlabelledTable (Fin d) // q.HasCommonWitnesses 2} :=
      ⟨x.val, SymmetricCycles.UnlabelledTable.hasCommonWitnesses_out.mp
        ((hw x).mono (by decide) hk)⟩
    have hs (x : X) (e : Equation α) (he : e ∈ E) :
        Satisfies (SymmetricCycles.UnlabelledTable.toIsoClass (f x)) e := by
      let _ := SymmetricCycles.lawful_of_hasWitnesses ((SymmetricCycles.hasCommonWitnesses_two_iff
        _).mp ((hw x).mono (by decide) hk))
      exact (satisfies_ofAlgebra _ e).mpr (h d hd x.val.out (hw x) e he)
    gcongr
    exact Nat.card_le_card_of_injective
      (fun x : X => (⟨SymmetricCycles.UnlabelledTable.toIsoClass (f x), hs x⟩ :
        {q : ofAtoms (d + 1) // ∀ e ∈ E, Satisfies q e}))
      (fun x y he => Subtype.ext (show (f x).val = (f y).val from congrArg Subtype.val
        (SymmetricCycles.UnlabelledTable.toIsoClass_injective d (congrArg Subtype.val he))))
  · filter_upwards with d
    exact (div_le_one (by exact_mod_cast card_ofAtoms_pos (d + 1))).mpr
      (Nat.cast_le.mpr (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective))

/-- For each fixed finite set of equations valid in RRA, the proportion of finite
relation-algebra isomorphism classes satisfying them all tends to one. -/
theorem tendsto_satisfying_div_all (E : Finset (Equation α)) (hE : ∀ e ∈ E, e.ValidInRRA) :
    Tendsto (fun n => (Nat.card {q : ofAtoms n // ∀ e ∈ E, Satisfies q e} : ℝ) /
      Nat.card (ofAtoms n)) atTop (𝓝 1) := by
  classical
  choose! k hk h using fun e he => Equation.exists_commonWitnesses_bound e (hE e he)
  apply tendsto_satisfying_of_commonWitnesses E (le_max_left 2 (E.sup k))
  intro d hd T _ hw e he
  have hle := (Finset.le_sup (f := k) he).trans (le_max_right 2 (E.sup k))
  exact h e he d hd T (hw.mono (by have := hk e he; omega) hle)

/-- Maddux's Random Representability Conjecture. The proportion of representable isomorphism
classes among all finite relation algebras with `n` Boolean atoms tends to one. -/
theorem_wanted random_representability_conjecture :
    Tendsto (fun n => (Nat.card {q : ofAtoms n // IsRepresentable q} : ℝ) /
      Nat.card (ofAtoms n)) atTop (𝓝 1)

end IsoClass

end Cslib.RelationAlgebra
