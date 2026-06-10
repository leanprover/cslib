/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Bimodal.Metalogic.Algebraic.BooleanStructure
public import Cslib.Logics.Bimodal.Metalogic.Core.MCSProperties
public import Cslib.Logics.Bimodal.Theorems.Perpetuity.Bridge

/-!
# Interior Operators for Modal and Temporal Modalities

This module defines interior operators on the Lindenbaum algebra.

## Main Definitions

- `InteriorOp`: Structure for interior operators (dual of closure operators)
- `boxInterior`: Instance showing Box (□) is an interior operator

## Key Properties

Interior operators satisfy:
1. **Deflationary**: `c(a) ≤ a` (from T-axiom: `□φ → φ`)
2. **Monotone**: `a ≤ b → c(a) ≤ c(b)` (from K-distribution)
3. **Idempotent**: `c(c(a)) = c(a)` (from 4-axiom: `□φ → □□φ` and T-axiom)

## Status

Under strict temporal semantics, G and H are NOT interior operators:
- The T-axiom `Gφ → φ` is not valid when G quantifies over s > t (strict future)
- The T-axiom `Hφ → φ` is not valid when H quantifies over s < t (strict past)

However, the modal operator Box (□) remains an interior operator because
the modal T-axiom `□φ → φ` is still valid (modal accessibility is reflexive).

## References

* Ported from BimodalLogic/Theories/Bimodal/Metalogic/Algebraic/InteriorOperators.lean
  (1 sorry in G_monotone resolved using tempKDistDerived)
-/

set_option linter.style.emptyLine false
set_option linter.style.longLine false

@[expose] public section

namespace Cslib.Logic.Bimodal.Metalogic.Algebraic.InteriorOperators

open Cslib.Logic.Bimodal
open Cslib.Logic.Bimodal.Metalogic.Algebraic.LindenbaumQuotient
open Cslib.Logic.Bimodal.Metalogic.Algebraic.BooleanStructure

variable {Atom : Type*}

/-!
## Interior Operator Definition
-/

/--
An interior operator on a partial order.

This is the dual of Mathlib's ClosureOperator: instead of inflationary, it's deflationary.
-/
structure InteriorOp (α : Type*) [PartialOrder α] where
  /-- The interior operation -/
  toFun : α → α
  /-- Interior is deflationary: i(a) ≤ a -/
  le_self : ∀ a, toFun a ≤ a
  /-- Interior is monotone: a ≤ b → i(a) ≤ i(b) -/
  monotone : ∀ a b, a ≤ b → toFun a ≤ toFun b
  /-- Interior is idempotent: i(i(a)) = i(a) -/
  idempotent : ∀ a, toFun (toFun a) = toFun a

/-!
## G Monotonicity (Valid Under Strict Semantics)
-/

/--
G is monotone: `φ ≤ ψ → Gφ ≤ Gψ`.

Uses K-distribution and temporal necessitation.
This property holds under both reflexive and strict semantics.
-/
theorem G_monotone (a b : LindenbaumAlg Atom) (h : a ≤ b) : G_quot a ≤ G_quot b := by
  induction a using Quotient.ind
  induction b using Quotient.ind
  rename_i φ ψ
  show Derives φ.allFuture ψ.allFuture
  have h' : Derives φ ψ := h
  obtain ⟨d⟩ := h'
  have d_temp : DerivationTree FrameClass.Base [] (Formula.allFuture (φ.imp ψ)) :=
    DerivationTree.temporal_necessitation (φ.imp ψ) d
  have d_k := Theorems.TemporalDerived.tempKDistDerived φ ψ
  exact ⟨DerivationTree.modus_ponens [] _ _ d_k d_temp⟩

/-!
## H Monotonicity (Valid Under Strict Semantics)
-/

/--
H is monotone: `φ ≤ ψ → Hφ ≤ Hψ`.

Uses `pastMono` from Perpetuity (derived via temporal duality).
This property holds under both reflexive and strict semantics.
-/
theorem H_monotone (a b : LindenbaumAlg Atom) (h : a ≤ b) : H_quot a ≤ H_quot b := by
  induction a using Quotient.ind
  induction b using Quotient.ind
  rename_i φ ψ
  show Derives φ.allPast ψ.allPast
  have h' : Derives φ ψ := h
  obtain ⟨d⟩ := h'
  exact ⟨Theorems.Perpetuity.pastMono d⟩

/-!
## Box as Interior Operator

The modal operator Box (□) is an interior operator because the modal T-axiom
`□φ → φ` remains valid. Modal accessibility is reflexive in our logic.
-/

/--
Box is deflationary: `□φ ≤ φ`.

Uses T-axiom `modal_t`: `□φ → φ`.
-/
theorem box_le_self (a : LindenbaumAlg Atom) : boxQuot a ≤ a := by
  induction a using Quotient.ind
  rename_i φ
  show Derives φ.box φ
  exact ⟨DerivationTree.axiom [] _ (Axiom.modal_t φ) trivial⟩

/--
Box is monotone: `φ ≤ ψ → □φ ≤ □ψ`.

Uses K-distribution and necessitation.
-/
theorem box_monotone (a b : LindenbaumAlg Atom) (h : a ≤ b) : boxQuot a ≤ boxQuot b := by
  induction a using Quotient.ind
  induction b using Quotient.ind
  rename_i φ ψ
  show Derives φ.box ψ.box
  have h' : Derives φ ψ := h
  obtain ⟨d⟩ := h'
  have d_box : DerivationTree FrameClass.Base [] (Formula.box (φ.imp ψ)) :=
    DerivationTree.necessitation (φ.imp ψ) d
  have d_k : DerivationTree FrameClass.Base [] ((φ.imp ψ).box.imp (φ.box.imp ψ.box)) :=
    DerivationTree.axiom [] _ (Axiom.modal_k_dist φ ψ) trivial
  exact ⟨DerivationTree.modus_ponens [] _ _ d_k d_box⟩

/--
Box is idempotent: `□(□φ) = □φ`.

Uses 4-axiom `modal_4`: `□φ → □□φ` and T-axiom for the converse.
-/
theorem box_idempotent (a : LindenbaumAlg Atom) : boxQuot (boxQuot a) = boxQuot a := by
  induction a using Quotient.ind
  rename_i φ
  apply Quotient.sound
  show ProvEquiv φ.box.box φ.box
  constructor
  · exact ⟨DerivationTree.axiom [] _ (Axiom.modal_t φ.box) trivial⟩
  · exact ⟨DerivationTree.axiom [] _ (Axiom.modal_4 φ) trivial⟩

/--
Box is an interior operator on the Lindenbaum algebra.
-/
noncomputable def boxInterior : InteriorOp (LindenbaumAlg Atom) where
  toFun := boxQuot
  le_self := box_le_self
  monotone := box_monotone
  idempotent := box_idempotent

end Cslib.Logic.Bimodal.Metalogic.Algebraic.InteriorOperators
