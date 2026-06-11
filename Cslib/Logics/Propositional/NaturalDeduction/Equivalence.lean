/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.NaturalDeduction.Basic
public import Cslib.Logics.Propositional.NaturalDeduction.FromHilbert

/-! # Equivalence between Hilbert and Natural Deduction Systems

This module proves the extensional equivalence between the Hilbert-style proof system
(`DerivationTree`, `Deriv`, `Derivable`) and the standalone natural deduction system
(`Theory.Derivation`, `DerivableIn`).

## Main Definitions

- `HilbertAxiomTheory` : The ND theory consisting of all Hilbert axiom schema instances.
- `hilbertToND` : Translation from Hilbert derivation trees to ND derivations.
- `ndToHilbert` : Translation from ND derivations to Hilbert derivation trees.
- `hilbert_iff_nd` : Extensional equivalence for closed derivability.

## Design

The two systems differ in context representation (List vs Finset) and axiom handling
(baked-in vs parameterized). The bridge uses `List.toFinset` / `Finset.toList` for
context conversion and wraps Hilbert axiom schemata into an ND `Theory`.

The `ndToHilbert` direction is `noncomputable` because it uses `deductionTheorem`,
which relies on `Classical.propDecidable`.

## References

* `Cslib/Logics/Propositional/ProofSystem/Derivation.lean` -- Hilbert system
* `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` -- ND system
* `Cslib/Logics/Propositional/Metalogic/DeductionTheorem.lean` -- deduction theorem
-/

@[expose] public section

namespace Cslib.Logic.PL

open Cslib.Logic
open InferenceSystem

/-! ## Theory Definition -/

/-- The ND theory corresponding to the Hilbert axiom schemata.
A proposition belongs to this theory iff it is an instance of one of the
four propositional axiom schemata (implyK, implyS, efq, peirce). -/
def HilbertAxiomTheory {Atom : Type*} : Theory Atom :=
  { φ | PropositionalAxiom φ }

/-- Membership in `HilbertAxiomTheory` is equivalent to being a propositional axiom. -/
@[simp]
theorem mem_hilbertAxiomTheory {Atom : Type*} {φ : PL.Proposition Atom} :
    φ ∈ (HilbertAxiomTheory : Theory Atom) ↔ PropositionalAxiom φ :=
  Iff.rfl

variable {Atom : Type*} [DecidableEq Atom]

/-! ## Context Membership Bridge Lemmas -/

/-- Elements of `(insert A Γ).toList` belong to `A :: Γ.toList`. -/
theorem finset_insert_toList_mem_cons (A : PL.Proposition Atom) (Γ : Ctx Atom)
    {x : PL.Proposition Atom} :
    x ∈ (Insert.insert A Γ : Ctx Atom).toList → x ∈ A :: Γ.toList := by
  simp [Finset.mem_toList, List.mem_cons]

/-- Elements of `A :: Γ.toList` belong to `(insert A Γ).toList`. -/
theorem list_cons_mem_finset_insert_toList (A : PL.Proposition Atom)
    (Γ : Ctx Atom) {x : PL.Proposition Atom} :
    x ∈ A :: Γ.toList → x ∈ (Insert.insert A Γ : Ctx Atom).toList := by
  simp [Finset.mem_toList, List.mem_cons]

/-! ## Hilbert to ND Translation -/

/-- Translate a Hilbert derivation tree into an ND derivation under `HilbertAxiomTheory`.

Each constructor maps to its ND counterpart:
- `ax`: axiom schema instance -> ND axiom rule
- `assumption`: context membership -> ND assumption (via `List.mem_toFinset`)
- `modus_ponens`: -> ND implication elimination
- `weakening`: -> ND context weakening (via `Finset` subset from `List` subset) -/
def hilbertToND {Γ : List (PL.Proposition Atom)} {φ : PL.Proposition Atom} :
    DerivationTree PropositionalAxiom Γ φ →
    @Theory.Derivation Atom _ (HilbertAxiomTheory : Theory Atom) Γ.toFinset φ
  | .ax _ _ h_ax =>
    Theory.Derivation.ax (mem_hilbertAxiomTheory.mpr h_ax)
  | .assumption _ _ h_mem =>
    Theory.Derivation.ass (List.mem_toFinset.mpr h_mem)
  | .modus_ponens _ _ _ d₁ d₂ =>
    Theory.Derivation.impE (hilbertToND d₁) (hilbertToND d₂)
  | .weakening _ _ _ d h_sub =>
    Theory.Derivation.weakCtx
      (fun x hx => List.mem_toFinset.mpr (h_sub x (List.mem_toFinset.mp hx)))
      (hilbertToND d)

/-- Prop-level wrapper: if `Γ ⊢ φ` in the Hilbert system, then `φ` is derivable
in ND under `HilbertAxiomTheory` with context `Γ.toFinset`. -/
theorem hilbert_to_nd_deriv {Γ : List (PL.Proposition Atom)} {φ : PL.Proposition Atom}
    (h : Deriv PropositionalAxiom Γ φ) :
    DerivableIn (HilbertAxiomTheory : Theory Atom)
      ((Γ.toFinset : Ctx Atom) ⊢ φ) := by
  obtain ⟨d⟩ := h
  exact ⟨hilbertToND d⟩

/-! ## ND to Hilbert Translation -/

/-- Translate an ND derivation under `HilbertAxiomTheory` into a Hilbert derivation tree.

Each constructor maps to its Hilbert counterpart:
- `ax`: theory membership -> Hilbert axiom rule
- `ass`: context membership -> Hilbert assumption (via `Finset.mem_toList`)
- `impE`: -> Hilbert modus ponens
- `botE`: -> EFQ axiom + modus ponens
- `impI`: -> deduction theorem (the key case, uses context bridge lemmas) -/
noncomputable def ndToHilbert {Γ : Ctx Atom} {φ : PL.Proposition Atom} :
    @Theory.Derivation Atom _ (HilbertAxiomTheory : Theory Atom) Γ φ →
    DerivationTree PropositionalAxiom Γ.toList φ
  | .ax h_mem =>
    .ax Γ.toList φ (mem_hilbertAxiomTheory.mp h_mem)
  | .ass h_mem =>
    .assumption Γ.toList φ (Finset.mem_toList.mpr h_mem)
  | .impE d₁ d₂ =>
    .modus_ponens Γ.toList _ φ (ndToHilbert d₁) (ndToHilbert d₂)
  | .botE d =>
    botE (ndToHilbert d)
  | @Theory.Derivation.impI _ _ _ A B Γ' d => by
    -- Recursive call gives: DerivationTree (insert A Γ').toList B
    have ih := ndToHilbert d
    -- Weaken to A :: Γ'.toList using the bridge lemma
    have ih' := DerivationTree.weakening _ (A :: Γ'.toList) B ih
      (fun x hx => finset_insert_toList_mem_cons A Γ' hx)
    -- Apply deduction theorem to get Γ'.toList ⊢ A → B
    exact deductionTheorem
      (fun φ ψ => .implyK φ ψ) (fun φ ψ χ => .implyS φ ψ χ)
      Γ'.toList A B ih'

/-- Prop-level wrapper: if `φ` is derivable in ND under `HilbertAxiomTheory` with
context `Γ`, then `Γ.toList ⊢ φ` in the Hilbert system. -/
theorem nd_to_hilbert_deriv {Γ : Ctx Atom} {φ : PL.Proposition Atom}
    (h : DerivableIn (HilbertAxiomTheory : Theory Atom) ((Γ : Ctx Atom) ⊢ φ)) :
    Deriv PropositionalAxiom Γ.toList φ := by
  obtain ⟨d⟩ := h
  exact ⟨ndToHilbert d⟩

/-! ## Top-Level Equivalence -/

/-- **Extensional equivalence**: A formula is derivable in the Hilbert system
(from the empty context) if and only if it is derivable in natural deduction
under `HilbertAxiomTheory` (from the empty context).

This bridges the two proof systems in the codebase, showing they have the
same deductive power for closed derivability. -/
theorem hilbert_iff_nd {φ : PL.Proposition Atom} :
    Derivable PropositionalAxiom φ ↔
    DerivableIn (HilbertAxiomTheory : Theory Atom)
      ((∅ : Ctx Atom) ⊢ φ) := by
  constructor
  · intro h
    have := hilbert_to_nd_deriv h
    rwa [List.toFinset_nil] at this
  · intro h
    have hd := nd_to_hilbert_deriv h
    exact weakening_deriv hd (fun x hx => by simp [Finset.mem_toList] at hx)

end Cslib.Logic.PL
