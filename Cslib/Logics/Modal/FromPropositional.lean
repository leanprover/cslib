/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.Defs
public import Cslib.Logics.Propositional.Semantics.Basic
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

/-! ## Semantic Coherence

The `toModal` embedding preserves semantic meaning: modal satisfaction of `φ.toModal` at a
world `w` in model `m` coincides with propositional evaluation of `φ` under the valuation
`m.v w`. Since `toModal` never introduces `box`, the accessibility relation plays no role. -/

/-- Bridge lemma: modal satisfaction of `φ.toModal` equals propositional
evaluation under `m.v w`. -/
theorem modal_satisfies_toModal_iff_evaluate
    {World : Type*} {Atom : Type*}
    (m : Modal.Model World Atom) (w : World)
    (φ : PL.Proposition Atom) :
    Modal.Satisfies m w φ.toModal ↔ PL.Evaluate (m.v w) φ := by
  induction φ with
  | atom p => rfl
  | bot => rfl
  | imp φ ψ ih1 ih2 =>
    simp only [PL.Proposition.toModal, Modal.Satisfies, PL.Evaluate]
    exact ⟨fun h he => ih2.mp (h (ih1.mpr he)),
           fun h hm => ih2.mpr (h (ih1.mp hm))⟩

/-- Forward direction: every propositional tautology is modally valid under `toModal`. -/
theorem tautology_toModal_valid {Atom : Type*}
    {φ : PL.Proposition Atom} (h : PL.Tautology φ)
    {World : Type*} (m : Modal.Model World Atom) (w : World) :
    Modal.Satisfies m w φ.toModal :=
  (modal_satisfies_toModal_iff_evaluate m w φ).mpr (h (m.v w))

/-- Backward direction: if `φ.toModal` is modally valid over all models, then `φ` is a tautology. -/
theorem toModal_valid_implies_tautology {Atom : Type*}
    {φ : PL.Proposition Atom}
    (h : ∀ (World : Type) (m : Modal.Model World Atom) (w : World),
      Modal.Satisfies m w φ.toModal) :
    PL.Tautology φ := by
  intro v
  let m : Modal.Model Unit Atom := ⟨fun _ _ => False, fun _ => v⟩
  exact (modal_satisfies_toModal_iff_evaluate m () φ).mp (h Unit m ())

/-- Full coherence: `φ` is a propositional tautology iff `φ.toModal` is modally valid. -/
theorem tautology_iff_toModal_valid {Atom : Type*}
    {φ : PL.Proposition Atom} :
    PL.Tautology φ ↔
    (∀ (World : Type) (m : Modal.Model World Atom) (w : World),
      Modal.Satisfies m w φ.toModal) :=
  ⟨fun h _ m w => tautology_toModal_valid h m w, toModal_valid_implies_tautology⟩

end Cslib.Logic
