/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.FromPropositional
public import Cslib.Logics.Temporal.FromPropositional
public import Cslib.Logics.Bimodal.Embedding.ModalEmbedding
public import Cslib.Logics.Bimodal.Embedding.TemporalEmbedding

/-! # Propositional to Bimodal Embedding

This module defines the direct structural embedding from propositional logic formulas into
bimodal logic formulas, and proves that the embedding diamond commutes: going through
Modal is the same as going through Temporal.

The PL-to-Modal and PL-to-Temporal embeddings are imported from `Modal.FromPropositional`
and `Temporal.FromPropositional` respectively.

## Main Definitions

- `PL.Proposition.toBimodal`: Propositional → Bimodal (maps atom/bot/imp)

## Main Results

- `PL.Proposition.toModal_toBimodal`: PL → Modal → Bimodal = PL → Bimodal
- `PL.Proposition.toTemporal_toBimodal`: PL → Temporal → Bimodal = PL → Bimodal
- `PL.Proposition.embedding_commutes`: both composite paths agree
-/

@[expose] public section

namespace Cslib.Logic

/-- Embed a propositional formula directly into bimodal logic. -/
def PL.Proposition.toBimodal : PL.Proposition Atom → Bimodal.Formula Atom
  | .atom p => .atom p
  | .bot => .bot
  | .imp φ₁ φ₂ => .imp φ₁.toBimodal φ₂.toBimodal

/-- Coercion from propositional to bimodal formulas. -/
instance instCoePLToBimodal : Coe (PL.Proposition Atom) (Bimodal.Formula Atom) where
  coe := PL.Proposition.toBimodal

/-- Direct embedding preserves atom. -/
@[simp]
theorem PL.Proposition.toBimodal_atom (p : Atom) :
    (PL.Proposition.atom p : PL.Proposition Atom).toBimodal = Bimodal.Formula.atom p := rfl

/-- Direct embedding preserves bot. -/
@[simp]
theorem PL.Proposition.toBimodal_bot :
    (PL.Proposition.bot : PL.Proposition Atom).toBimodal = Bimodal.Formula.bot := rfl

/-- Direct embedding preserves imp. -/
@[simp]
theorem PL.Proposition.toBimodal_imp (φ₁ φ₂ : PL.Proposition Atom) :
    (PL.Proposition.imp φ₁ φ₂).toBimodal =
      Bimodal.Formula.imp φ₁.toBimodal φ₂.toBimodal := rfl

/-- Direct embedding preserves neg. -/
@[simp]
theorem PL.Proposition.toBimodal_neg (φ : PL.Proposition Atom) :
    (PL.Proposition.neg φ).toBimodal = Bimodal.Formula.neg φ.toBimodal := rfl

/-- The diagram PL → Modal → Bimodal commutes with the direct path PL → Bimodal. -/
@[simp]
theorem PL.Proposition.toModal_toBimodal (φ : PL.Proposition Atom) :
    φ.toModal.toBimodal = φ.toBimodal := by
  induction φ <;> simp [*]

/-- The diagram PL → Temporal → Bimodal commutes with the direct path PL → Bimodal. -/
@[simp]
theorem PL.Proposition.toTemporal_toBimodal (φ : PL.Proposition Atom) :
    φ.toTemporal.toBimodal = φ.toBimodal := by
  induction φ <;> simp [*]

/-- The embedding diamond commutes:
    going through Modal is the same as going through Temporal. -/
theorem PL.Proposition.embedding_commutes (φ : PL.Proposition Atom) :
    φ.toModal.toBimodal = φ.toTemporal.toBimodal := by
  simp

end Cslib.Logic
