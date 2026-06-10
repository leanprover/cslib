/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.Defs
public import Cslib.Logics.Modal.Basic

/-! # Propositional to Modal Embedding

This module defines the structural embedding from propositional logic into modal logic.
The embedding maps each propositional primitive constructor to the corresponding modal
constructor, establishing Propositional as a sub-logic of Modal.

## Main Definitions

- `PL.Proposition.toModal`: Propositional → Modal (maps atom/bot/imp)
-/

@[expose] public section

namespace Cslib.Logic

/-- Embed a propositional formula into modal logic. -/
def PL.Proposition.toModal : PL.Proposition Atom → Modal.Proposition Atom
  | .atom p => .atom p
  | .bot => .bot
  | .imp φ₁ φ₂ => .imp (φ₁.toModal) (φ₂.toModal)

/-- Coercion from propositional to modal formulas. -/
instance instCoePLToModal : Coe (PL.Proposition Atom) (Modal.Proposition Atom) where
  coe := PL.Proposition.toModal

/-- Embedding preserves atom. -/
@[simp]
theorem PL.Proposition.toModal_atom (p : Atom) :
    (PL.Proposition.atom p : PL.Proposition Atom).toModal = Modal.Proposition.atom p := rfl

/-- Embedding preserves bot. -/
@[simp]
theorem PL.Proposition.toModal_bot :
    (PL.Proposition.bot : PL.Proposition Atom).toModal = Modal.Proposition.bot := rfl

/-- Embedding preserves imp. -/
@[simp]
theorem PL.Proposition.toModal_imp (φ₁ φ₂ : PL.Proposition Atom) :
    (PL.Proposition.imp φ₁ φ₂).toModal = Modal.Proposition.imp φ₁.toModal φ₂.toModal := rfl

/-- Embedding preserves neg. -/
theorem PL.Proposition.toModal_neg (φ : PL.Proposition Atom) :
    (PL.Proposition.neg φ).toModal = Modal.Proposition.neg φ.toModal := rfl

end Cslib.Logic
