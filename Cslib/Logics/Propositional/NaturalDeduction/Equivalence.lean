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

The equivalence is parameterized over any axiom predicate `Axioms` that includes K, S,
and EFQ, with instantiated corollaries for intuitionistic and classical logic.

## Main Definitions

- `AxiomTheory` : Generic ND theory for any axiom predicate.
- `HilbertAxiomTheory` : Classical specialization (backward compatibility).
- `hilbertToND` : Translation from Hilbert derivation trees to ND derivations (structural).
- `ndToHilbert` : Translation from ND derivations to Hilbert derivation trees (needs K, S, EFQ).
- `hilbert_iff_nd` : Generic extensional equivalence for closed derivability.
- `hilbert_iff_nd_int` : Intuitionistic instantiation.
- `hilbert_iff_nd_cl` : Classical instantiation.

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

/-! ## Theory Definitions -/

/-- Generic ND theory for any axiom predicate.
A proposition belongs to `AxiomTheory Axioms` iff `Axioms φ` holds. -/
def AxiomTheory {Atom : Type*} (Axioms : PL.Proposition Atom → Prop) : Theory Atom :=
  { φ | Axioms φ }

/-- Membership in `AxiomTheory Axioms` is equivalent to the axiom predicate holding. -/
@[simp]
theorem mem_axiomTheory {Atom : Type*} {Axioms : PL.Proposition Atom → Prop}
    {φ : PL.Proposition Atom} :
    φ ∈ (AxiomTheory Axioms : Theory Atom) ↔ Axioms φ :=
  Iff.rfl

/-- The ND theory corresponding to the classical Hilbert axiom schemata.
Backward-compatible abbreviation for `AxiomTheory PropositionalAxiom`. -/
abbrev HilbertAxiomTheory {Atom : Type*} : Theory Atom :=
  AxiomTheory (@PropositionalAxiom Atom)

/-- Membership in `HilbertAxiomTheory` is equivalent to being a propositional axiom. -/
theorem mem_hilbertAxiomTheory {Atom : Type*} {φ : PL.Proposition Atom} :
    φ ∈ (HilbertAxiomTheory : Theory Atom) ↔ PropositionalAxiom φ :=
  mem_axiomTheory

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

/-- Translate a Hilbert derivation tree into an ND derivation under `AxiomTheory Axioms`.

This direction is purely structural (no axiom parameters needed).
Each constructor maps to its ND counterpart:
- `ax`: axiom schema instance -> ND axiom rule
- `assumption`: context membership -> ND assumption (via `List.mem_toFinset`)
- `modus_ponens`: -> ND implication elimination
- `weakening`: -> ND context weakening (via `Finset` subset from `List` subset) -/
def hilbertToND
    {Axioms : PL.Proposition Atom → Prop}
    {Γ : List (PL.Proposition Atom)} {φ : PL.Proposition Atom} :
    DerivationTree Axioms Γ φ →
    @Theory.Derivation Atom _ (AxiomTheory Axioms : Theory Atom) Γ.toFinset φ
  | .ax _ _ h_ax =>
    Theory.Derivation.ax (mem_axiomTheory.mpr h_ax)
  | .assumption _ _ h_mem =>
    Theory.Derivation.ass (List.mem_toFinset.mpr h_mem)
  | .modus_ponens _ _ _ d₁ d₂ =>
    Theory.Derivation.impE (hilbertToND d₁) (hilbertToND d₂)
  | .weakening _ _ _ d h_sub =>
    Theory.Derivation.weakCtx
      (fun x hx => List.mem_toFinset.mpr (h_sub x (List.mem_toFinset.mp hx)))
      (hilbertToND d)

/-- Prop-level wrapper: if `Γ ⊢ φ` in the Hilbert system, then `φ` is derivable
in ND under `AxiomTheory Axioms` with context `Γ.toFinset`. -/
theorem hilbert_to_nd_deriv
    {Axioms : PL.Proposition Atom → Prop}
    {Γ : List (PL.Proposition Atom)} {φ : PL.Proposition Atom}
    (h : Deriv Axioms Γ φ) :
    DerivableIn (AxiomTheory Axioms : Theory Atom)
      ((Γ.toFinset : Ctx Atom) ⊢ φ) := by
  obtain ⟨d⟩ := h
  exact ⟨hilbertToND d⟩

/-! ## ND to Hilbert Translation -/

/-- Translate an ND derivation under `AxiomTheory Axioms` into a Hilbert derivation tree.

Requires explicit K, S, and EFQ axiom witnesses.
Each constructor maps to its Hilbert counterpart:
- `ax`: theory membership -> Hilbert axiom rule
- `ass`: context membership -> Hilbert assumption (via `Finset.mem_toList`)
- `impE`: -> Hilbert modus ponens
- `botE`: -> EFQ axiom + modus ponens (uses `h_EFQ`)
- `impI`: -> deduction theorem (the key case, uses `h_K`, `h_S`, and context bridge lemmas) -/
noncomputable def ndToHilbert
    {Axioms : PL.Proposition Atom → Prop}
    (h_K : ∀ (φ ψ : PL.Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_S : ∀ (φ ψ χ : PL.Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_EFQ : ∀ (φ : PL.Proposition Atom), Axioms (Proposition.bot.imp φ))
    {Γ : Ctx Atom} {φ : PL.Proposition Atom} :
    @Theory.Derivation Atom _ (AxiomTheory Axioms : Theory Atom) Γ φ →
    DerivationTree Axioms Γ.toList φ
  | .ax h_mem =>
    .ax Γ.toList φ (mem_axiomTheory.mp h_mem)
  | .ass h_mem =>
    .assumption Γ.toList φ (Finset.mem_toList.mpr h_mem)
  | .impE d₁ d₂ =>
    .modus_ponens Γ.toList _ φ (ndToHilbert h_K h_S h_EFQ d₁) (ndToHilbert h_K h_S h_EFQ d₂)
  | .botE d =>
    botE h_EFQ (ndToHilbert h_K h_S h_EFQ d)
  | @Theory.Derivation.impI _ _ _ A B Γ' d => by
    -- Recursive call gives: DerivationTree (insert A Γ').toList B
    have ih := ndToHilbert h_K h_S h_EFQ d
    -- Weaken to A :: Γ'.toList using the bridge lemma
    have ih' := DerivationTree.weakening _ (A :: Γ'.toList) B ih
      (fun x hx => finset_insert_toList_mem_cons A Γ' hx)
    -- Apply deduction theorem to get Γ'.toList ⊢ A → B
    exact deductionTheorem h_K h_S Γ'.toList A B ih'

/-- Prop-level wrapper: if `φ` is derivable in ND under `AxiomTheory Axioms` with
context `Γ`, then `Γ.toList ⊢ φ` in the Hilbert system. -/
theorem nd_to_hilbert_deriv
    {Axioms : PL.Proposition Atom → Prop}
    (h_K : ∀ (φ ψ : PL.Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_S : ∀ (φ ψ χ : PL.Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_EFQ : ∀ (φ : PL.Proposition Atom), Axioms (Proposition.bot.imp φ))
    {Γ : Ctx Atom} {φ : PL.Proposition Atom}
    (h : DerivableIn (AxiomTheory Axioms : Theory Atom) ((Γ : Ctx Atom) ⊢ φ)) :
    Deriv Axioms Γ.toList φ := by
  obtain ⟨d⟩ := h
  exact ⟨ndToHilbert h_K h_S h_EFQ d⟩

/-! ## Top-Level Equivalence -/

/-- **Generic extensional equivalence**: A formula is derivable in the Hilbert system
(from the empty context) if and only if it is derivable in natural deduction
under `AxiomTheory Axioms` (from the empty context).

This bridges the two proof systems for any axiom predicate that includes K, S, and EFQ. -/
theorem hilbert_iff_nd
    {Axioms : PL.Proposition Atom → Prop}
    (h_K : ∀ (φ ψ : PL.Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_S : ∀ (φ ψ χ : PL.Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_EFQ : ∀ (φ : PL.Proposition Atom), Axioms (Proposition.bot.imp φ))
    {φ : PL.Proposition Atom} :
    Derivable Axioms φ ↔
    DerivableIn (AxiomTheory Axioms : Theory Atom)
      ((∅ : Ctx Atom) ⊢ φ) := by
  constructor
  · intro h
    have := hilbert_to_nd_deriv h
    rwa [List.toFinset_nil] at this
  · intro h
    have hd := nd_to_hilbert_deriv h_K h_S h_EFQ h
    exact weakening_deriv hd (fun x hx => by simp [Finset.mem_toList] at hx)

/-! ## Corollaries -/

/-- Intuitionistic equivalence: Hilbert derivability with `IntPropAxiom` is equivalent
to ND derivability under `AxiomTheory IntPropAxiom`. -/
theorem hilbert_iff_nd_int {φ : PL.Proposition Atom} :
    Derivable IntPropAxiom φ ↔
    DerivableIn (AxiomTheory (@IntPropAxiom Atom) : Theory Atom)
      ((∅ : Ctx Atom) ⊢ φ) :=
  hilbert_iff_nd
    (fun φ ψ => .implyK φ ψ)
    (fun φ ψ χ => .implyS φ ψ χ)
    (fun φ => .efq φ)

/-- Classical equivalence: Hilbert derivability with `PropositionalAxiom` is equivalent
to ND derivability under `AxiomTheory PropositionalAxiom`. -/
theorem hilbert_iff_nd_cl {φ : PL.Proposition Atom} :
    Derivable PropositionalAxiom φ ↔
    DerivableIn (AxiomTheory (@PropositionalAxiom Atom) : Theory Atom)
      ((∅ : Ctx Atom) ⊢ φ) :=
  hilbert_iff_nd
    (fun φ ψ => .implyK φ ψ)
    (fun φ ψ χ => .implyS φ ψ χ)
    (fun φ => .efq φ)

end Cslib.Logic.PL
