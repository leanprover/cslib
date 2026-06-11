/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Defs.Unbundled

/-! # Propositional Kripke Semantics

This module defines Kripke semantics for propositional (intuitionistic and minimal) logic.

## Main Definitions

- `KripkeModel`: A Kripke model bundles a preordered set of worlds, a valuation, a `botForces`
  predicate, and upward-closure proofs for both.
- `IForces`: The forcing relation for propositional Kripke semantics, parameterized by `botForces`.
  Recursion on `PL.Proposition` with three cases: atom (valuation lookup), bot (`botForces`),
  imp (universal quantification over successors).
- `iforces_persistence`: Persistence of forcing under the preorder
  ([ChagrovZakharyaschev1997] Proposition 2.1).
- `IValid`: Intuitionistic validity -- forced at every world in every intuitionistic Kripke model
  (where `botForces = fun _ => False`).
- `MValid`: Minimal validity -- forced at every world in every minimal Kripke model
  (where `botForces` is an arbitrary upward-closed predicate).

## Design Notes

- Uses `Preorder World` rather than `PartialOrder World`: antisymmetry is never needed for
  persistence or downstream soundness/completeness proofs, and `Preorder` is strictly more general.
- `IForces` is standalone (not reusing `Modal.Satisfies`) because intuitionistic implication
  requires universal quantification over accessible worlds, which is semantically different from
  the local interpretation in `Modal.Satisfies`.
- `PL.Proposition` has only `atom | bot | imp`; derived connectives (and/or/neg) reduce
  automatically via abbreviations.

## References

* [A. Chagrov, M. Zakharyaschev,
  *Modal Logic*][ChagrovZakharyaschev1997],
  Section 2.2, Proposition 2.1
-/

@[expose] public section

universe u v

namespace Cslib.Logic.PL

variable {Atom : Type u}

/-- A Kripke model for propositional logic.

Bundles a preordered type of worlds, a valuation `v : World -> Atom -> Prop`,
a predicate `botForces : World -> Prop` controlling whether falsum is forced,
and upward-closure proofs for both `v` and `botForces`. -/
structure KripkeModel (World : Type*) (Atom : Type*) [Preorder World] where
  /-- Valuation assigning propositions to atoms at each world. -/
  v : World → Atom → Prop
  /-- Predicate controlling whether falsum is forced at a world.
  Set to `fun _ => False` for intuitionistic semantics. -/
  botForces : World → Prop
  /-- The valuation is upward-closed: if `v w p` and `w ≤ w'`, then `v w' p`. -/
  v_upward_closed : ∀ {w w' : World} (p : Atom), w ≤ w' → v w p → v w' p
  /-- `botForces` is upward-closed: if `botForces w` and `w ≤ w'`, then `botForces w'`. -/
  bf_upward_closed : ∀ {w w' : World}, w ≤ w' → botForces w → botForces w'

/-- Forcing relation for propositional Kripke semantics, parameterized by `bot_forces`.

- **Intuitionistic instantiation**: `bot_forces = fun _ => False`
- **Minimal instantiation**: `bot_forces` is an arbitrary upward-closed predicate

The three cases correspond to the constructors of `PL.Proposition`:
- `atom p`: forced iff the valuation assigns `p` at world `w`
- `bot`: forced iff `bot_forces w`
- `imp φ ψ`: forced iff for every successor `w' ≥ w`, forcing `φ` at `w'` implies forcing `ψ`
  at `w'` -/
def IForces [Preorder World]
    (v : World → Atom → Prop) (bot_forces : World → Prop)
    (w : World) : PL.Proposition Atom → Prop
  | .atom p => v w p
  | .bot => bot_forces w
  | .imp φ ψ => ∀ w', w ≤ w' → IForces v bot_forces w' φ → IForces v bot_forces w' ψ

/-- Persistence of forcing under the preorder ([ChagrovZakharyaschev1997] Proposition 2.1).

If a formula is forced at world `w` and `w ≤ w'`, then the formula is forced at `w'`.
The proof is by structural induction on the formula:
- **atom**: follows from upward-closure of the valuation
- **bot**: follows from upward-closure of `bot_forces`
- **imp**: follows from transitivity of the preorder (no inductive hypothesis needed) -/
theorem iforces_persistence [Preorder World]
    {v : World → Atom → Prop} {bot_forces : World → Prop}
    (v_uc : ∀ {w w' : World} (p : Atom), w ≤ w' → v w p → v w' p)
    (bf_uc : ∀ {w w' : World}, w ≤ w' → bot_forces w → bot_forces w')
    {w w' : World} (hw : w ≤ w') {φ : PL.Proposition Atom}
    (hf : IForces v bot_forces w φ) : IForces v bot_forces w' φ := by
  induction φ with
  | atom p => exact v_uc p hw hf
  | bot => exact bf_uc hw hf
  | imp φ ψ _ _ =>
    intro u hu hfu
    exact hf u (le_trans hw hu) hfu

/-- A formula is intuitionistically valid (`IValid`) if it is forced at every world
in every intuitionistic Kripke model, i.e., for every preordered type of worlds,
every upward-closed valuation, and with `bot_forces = fun _ => False`. -/
def IValid (φ : PL.Proposition Atom) : Prop :=
  ∀ (World : Type v) [Preorder World] (val : World → Atom → Prop),
    (∀ {w w' : World} (p : Atom), w ≤ w' → val w p → val w' p) →
    ∀ w, IForces val (fun _ => False) w φ

/-- A formula is minimally valid (`MValid`) if it is forced at every world
in every minimal Kripke model, i.e., for every preordered type of worlds,
every upward-closed valuation, and every upward-closed `bot_forces` predicate. -/
def MValid (φ : PL.Proposition Atom) : Prop :=
  ∀ (World : Type v) [Preorder World] (val : World → Atom → Prop)
    (bot_forces : World → Prop),
    (∀ {w w' : World} (p : Atom), w ≤ w' → val w p → val w' p) →
    (∀ {w w' : World}, w ≤ w' → bot_forces w → bot_forces w') →
    ∀ w, IForces val bot_forces w φ

/-- Minimal validity implies intuitionistic validity.

Since `IValid` is `MValid` with `bot_forces = fun _ => False`
(which is trivially upward-closed), any minimally valid formula
is also intuitionistically valid. -/
theorem mvalid_implies_ivalid {φ : PL.Proposition Atom}
    (h : (MValid.{u, v} φ)) : IValid.{u, v} φ :=
  fun World _ val v_uc w =>
    h World val (fun _ => False) v_uc (fun {_ _} _ hf => absurd hf id) w

end Cslib.Logic.PL
