/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Foundations.Data.PFunctor.Basic
public import Cslib.Logics.Modal.Semantics
public import Cslib.Logics.Modal.Unary.Basic
public import Cslib.Foundations.Semantics.LTS.Basic
public import Cslib.Foundations.Semantics.Frame.LTS

/-! # Unary Modal Logic -/

@[expose] public section

namespace Cslib.Logic.Modal

open PFunctor

/-- Constructs a unary model from an `LTS` and a valuation `v`. -/
def Model.ofLTS (lts : LTS State Label) (v : State → Atom → Prop) :
    Model State (mkUnary Label) Atom where
  toFrame := lts.toFrame
  v := v

@[simp, scoped grind =, modal =]
theorem Model.ofLTS_toFrame (lts : LTS State Label) (v : State → Atom → Prop) :
    (ofLTS lts v).toFrame = lts.toFrame := by
  rfl

open Model
open scoped InferenceSystem

variable {lts : LTS State Label} {v : State → Atom → Prop}

@[scoped grind =, modal =]
theorem Satisfies.ofLTS_atom_iff {p : Atom} : ⇓Modal[ofLTS lts v,s ⊨ p] ↔ v s p := by rfl

theorem Satisfies.ofLTS_dynDiamond_iff_exists :
    ⇓Modal[ofLTS lts v,s ⊨ d⟨μ⟩φ] ↔ ∃ s', lts.Tr s μ s' ∧ ⇓Modal[ofLTS lts v,s' ⊨ φ] := by
  rw [Satisfies.dynDiamond_iff_exists]
  simp [ofLTS]

theorem Satisfies.ofLTS_dynBox_iff_forall :
    ⇓Modal[ofLTS lts v,s ⊨ d[μ]φ] ↔ ∀ s', lts.Tr s μ s' → ⇓Modal[ofLTS lts v,s' ⊨ φ] := by
  rw [Satisfies.dynBox_iff_forall]
  simp [ofLTS]

@[modal ⇒]
theorem Satisfies.ofLTS_dynDiamond_intro (htr : lts.Tr s μ s')
    (h : ⇓Modal[ofLTS lts v,s' ⊨ φ]) : ⇓Modal[ofLTS lts v,s ⊨ d⟨μ⟩φ] := by
  grind [modal]

@[modal ⇒]
theorem Satisfies.ofLTS_dynBox_elim (hbox : ⇓Modal[ofLTS lts v,s ⊨ d[μ]φ])
    (htr : lts.Tr s μ s') : ⇓Modal[ofLTS lts v,s' ⊨ φ] := by grind [modal]

end Cslib.Logic.Modal
