/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.Defs
public import Cslib.Logics.Modal.Basic
public import Cslib.Logics.Temporal.Syntax.Formula

/-! # Propositional Embeddings

This module defines structural embedding functions from propositional logic into modal
and temporal logic, along with `Coe` instances.

## Embeddings

- `PL.Proposition.toModal`: Propositional → Modal (maps atom/bot/imp to their modal counterparts)
- `PL.Proposition.toTemporal`: Propositional → Temporal
  (maps atom/bot/imp to their temporal counterparts)

Both embeddings are structure-preserving: they map each primitive constructor to the
corresponding constructor in the target formula type.
-/

@[expose] public section

namespace Cslib.Logic

/-- Embed a propositional formula into modal logic. -/
def PL.Proposition.toModal : PL.Proposition Atom → Modal.Proposition Atom
  | .atom p => .atom p
  | .bot => .bot
  | .imp φ₁ φ₂ => .imp (φ₁.toModal) (φ₂.toModal)

/-- Embed a propositional formula into temporal logic. -/
def PL.Proposition.toTemporal : PL.Proposition Atom → Temporal.Formula Atom
  | .atom p => .atom p
  | .bot => .bot
  | .imp φ₁ φ₂ => .imp (φ₁.toTemporal) (φ₂.toTemporal)

/-- Coercion from propositional to modal formulas. -/
instance instCoePLToModal : Coe (PL.Proposition Atom) (Modal.Proposition Atom) where
  coe := PL.Proposition.toModal

/-- Coercion from propositional to temporal formulas. -/
instance instCoePLToTemporal : Coe (PL.Proposition Atom) (Temporal.Formula Atom) where
  coe := PL.Proposition.toTemporal

/-- Embedding preserves atom. -/
@[simp]
theorem PL.Proposition.toModal_atom (p : Atom) :
    (PL.Proposition.atom p : PL.Proposition Atom).toModal = Modal.Proposition.atom p := rfl

/-- Embedding preserves atom (temporal). -/
@[simp]
theorem PL.Proposition.toTemporal_atom (p : Atom) :
    (PL.Proposition.atom p : PL.Proposition Atom).toTemporal = Temporal.Formula.atom p := rfl

/-- Embedding preserves bot. -/
@[simp]
theorem PL.Proposition.toModal_bot :
    (PL.Proposition.bot : PL.Proposition Atom).toModal = Modal.Proposition.bot := rfl

/-- Embedding preserves imp. -/
@[simp]
theorem PL.Proposition.toModal_imp (φ₁ φ₂ : PL.Proposition Atom) :
    (PL.Proposition.imp φ₁ φ₂).toModal = Modal.Proposition.imp φ₁.toModal φ₂.toModal := rfl

/-- Embedding preserves neg. -/
@[simp]
theorem PL.Proposition.toModal_neg (φ : PL.Proposition Atom) :
    (PL.Proposition.neg φ).toModal = Modal.Proposition.neg φ.toModal := rfl

/-- Embedding preserves bot (temporal). -/
@[simp]
theorem PL.Proposition.toTemporal_bot :
    (PL.Proposition.bot : PL.Proposition Atom).toTemporal = Temporal.Formula.bot := rfl

/-- Embedding preserves imp (temporal). -/
@[simp]
theorem PL.Proposition.toTemporal_imp (φ₁ φ₂ : PL.Proposition Atom) :
    (PL.Proposition.imp φ₁ φ₂).toTemporal = Temporal.Formula.imp φ₁.toTemporal φ₂.toTemporal := rfl

/-- Embedding preserves neg (temporal). -/
@[simp]
theorem PL.Proposition.toTemporal_neg (φ : PL.Proposition Atom) :
    (PL.Proposition.neg φ).toTemporal = Temporal.Formula.neg φ.toTemporal := rfl

end Cslib.Logic
