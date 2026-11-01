/-
Copyright (c) 2026 Malvin Gattinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Malvin Gattinger
-/

module

public import Cslib.Foundations.Semantics.Frame.Basic
public import Cslib.Foundations.Semantics.Frame.LTS
public import Cslib.Logics.Modal.Semantics
public import Cslib.Logics.Modal.Unary.Basic
public import Cslib.Logics.PDL.Basic
-- public import Cslib.Foundations.Semantics.LTS.Bisimulation

/-! # Semantics for Propositional Dynamic Logic (PDL) -/

@[expose] public section

namespace Cslib.Logic.Modal.PDL

variable {State Label Atom : Type*}

/-! ## Models -/

/-- A PDL model consists of an `LTS` and a valuation for its states.
The LTS uses all programs as labels, so this type includes irregular frames. -/
structure Model State Label Atom where
  /-- The labelled transition system. -/
  lts : LTS State (Program Label Atom)
  /-- Valuation of atoms at states. -/
  val : State → Atom → Prop

/-- Converts a PDL model into a unary modal model. -/
def Model.toModal (m : Model State Label Atom) :
    Modal.Model State (.mkUnary (Program Label Atom)) Atom :=
  Modal.Model.mk m.lts.toFrame m.val

@[simp, scoped grind =, modal =]
theorem Model.toModal_toFrame (m : Model State Label Atom) :
    m.toModal.toFrame = m.lts.toFrame := rfl

open Cslib.Logic.Modal in
/-- View a PDL formula over the unary signature with one modality per program. -/
def Formula.toUnary :
    Formula Label Atom → Proposition (PFunctor.mkUnary (Program Label Atom)) Atom
  | .atom p => .atom p
  | .false => .false
  | .not φ => .not (toUnary φ)
  | .or φ ψ => .or (toUnary φ) (toUnary ψ)
  | .triangle s φs => .triangle ⟨s, φs ∘ Sum.inl⟩ (fun _ => toUnary (φs (.inr ())))

@[simp, scoped grind =, modal =]
theorem Formula.toUnary_atom (p : Atom) :
    Formula.toUnary (.atom p : Formula Label Atom) = .atom p := rfl

@[simp, scoped grind =, modal =]
theorem Formula.toUnary_bot : (⊥ : Formula Label Atom).toUnary = ⊥ := rfl

@[simp, scoped grind =, modal =]
theorem Formula.toUnary_top : (⊤ : Formula Label Atom).toUnary = ⊤ := rfl

@[simp, scoped grind =, modal =]
theorem Formula.toUnary_not (φ : Formula Label Atom) : (¬φ).toUnary = ¬φ.toUnary := rfl

@[simp, scoped grind =, modal =]
theorem Formula.toUnary_or (φ ψ : Formula Label Atom) :
    (φ ∨ ψ).toUnary = (φ.toUnary ∨ ψ.toUnary) := rfl

@[simp, scoped grind =, modal =]
theorem Formula.toUnary_and (φ ψ : Formula Label Atom) :
    (φ ∧ ψ).toUnary = (φ.toUnary ∧ ψ.toUnary) := rfl

@[simp, scoped grind =, modal =]
theorem Formula.toUnary_imp (φ ψ : Formula Label Atom) :
    (φ → ψ).toUnary = (φ.toUnary → ψ.toUnary) := rfl

@[simp, scoped grind =, modal =]
theorem Formula.toUnary_iff (φ ψ : Formula Label Atom) :
    (φ ↔ ψ).toUnary = (φ.toUnary ↔ ψ.toUnary) := rfl

@[simp, scoped grind =, modal =]
theorem Formula.toUnary_dynDiamond (a : Program Label Atom) (φ : Formula Label Atom) :
    (d⟨a⟩φ).toUnary = d⟨a⟩(φ.toUnary) := rfl

@[simp, scoped grind =, modal =]
theorem Formula.toUnary_dynBox (a : Program Label Atom) (φ : Formula Label Atom) :
    (d[a]φ).toUnary = d[a](φ.toUnary) := rfl

/-- Shortcut for `Modal[PDL.Model.toModal m,s ⊨ φ]`. -/
scoped notation "PDL[" m "," s " ⊨ " φ "]" => Modal[PDL.Model.toModal m,s ⊨ Formula.toUnary φ]

open scoped InferenceSystem

/-! ## Regular Frames and Standard Models -/

/-- A frame (i.e. an `LTS`) is *regular* for PDL iff
the transition relations for `∪`, `?'` and `;'` are as expected. -/
structure _root_.Cslib.LTS.IsRegularPDL (lts : LTS State (Program Label Atom)) : Prop where
  seq   : ∀ a b w w', lts.Tr w (a ;' b) w' ↔ ∃ u, lts.Tr w a u ∧ lts.Tr u b w'
  union : ∀ a b w w', lts.Tr w (a ∪ b) w' ↔ lts.Tr w a w' ∨ lts.Tr w b w'
  star  : ∀ a w w', lts.Tr w (a*) w' ↔ Relation.ReflTransGen (lts.Tr · a ·) w w'

/-- A PDL model is *standard* iff its frame is regular and the transition
relation for tests agrees with the semantics (and thus the valuation). -/
structure Model.IsStandard (m : Model State Label Atom) : Prop where
  regular : m.lts.IsRegularPDL
  test    : ∀ ψ w w', m.lts.Tr w (?' ψ) w' ↔ w = w' ∧ ⇓PDL[m, w ⊨ ψ]

/-! ## Examples / checks -/

/-! ## TODO: make a standard model from an LTS -/

def LTS.regularFromLTS (lts : LTS State Label) : LTS State (Program Label Atom) := by
  sorry -- TODO

def Model.fromLTS (lts : LTS State Label) (val : State → Atom → Prop) : Model State Label Atom :=
  sorry -- TODO

/-! ## Characterizations (as for HML) -/

open PDL
open scoped PDL.Model Modal.Proposition InferenceSystem Satisfies Frame

variable {m : PDL.Model State Label Atom}

@[scoped grind =, modal =]
theorem Satisfies.pdl_atom_iff {p : Atom} : ⇓PDL[m,s ⊨ p] ↔ m.val s p := by rfl

theorem Satisfies.pdl_dynDiamond_iff_exists :
    ⇓PDL[m,s ⊨ d⟨μ⟩φ] ↔ ∃ s', m.lts.Tr s μ s' ∧ ⇓PDL[m,s' ⊨ φ] := by grind [modal]

theorem Satisfies.pdl_dynBox_iff_forall :
    ⇓PDL[m,s ⊨ d[μ]φ] ↔ ∀ s', m.lts.Tr s μ s' → ⇓PDL[m,s' ⊨ φ] := by grind [modal]

@[modal ⇒]
theorem Satisfies.pdl_dynDiamond_intro (htr : m.lts.Tr s μ s')
    (h : ⇓PDL[m,s' ⊨ φ]) : ⇓PDL[m,s ⊨ d⟨μ⟩φ] := by grind [modal]

theorem Satisfies.pdl_dynBox_elim (hbox : ⇓PDL[m,s ⊨ d[μ]φ])
    (htr : m.lts.Tr s μ s') : ⇓PDL[m,s' ⊨ φ] := by grind [modal]

/-! ## Axioms (BRV Def 4.78) -/

-- TODO: should we separate the statement of the axioms from their soundness theorem?

namespace Axioms

variable {State : Type*} (m : Model State Label Atom) (s : State)
  (a b : Program Label Atom) (p q ψ : Formula Label Atom)

/-- (i) K: valid on all frames. -/
theorem K : ⇓PDL[m, s ⊨ d[a](p → q) → (d[a]p → d[a]q)] := by grind [modal]

/-- (ii) Duality: valid on all frames. -/
theorem dual : ⇓PDL[m, s ⊨ d⟨a⟩p ↔ ¬d[a](¬p)] := by grind [modal]

/-- (iii) Composition: valid on frames regular for `;'`. -/
theorem seq (h : m.lts.IsRegularPDL) :
    ⇓PDL[m, s ⊨ d⟨a ;' b⟩p ↔ d⟨a⟩(d⟨b⟩p)] := sorry

/-- (iv) Choice: valid on frames regular for `∪`. -/
theorem union (h : m.lts.IsRegularPDL) :
    ⇓PDL[m, s ⊨ d⟨a ∪ b⟩p ↔ (d⟨a⟩p ∨ d⟨b⟩p)] := sorry

/-- (v) Mix: valid on frames regular for `*`. -/
theorem mix (h : m.lts.IsRegularPDL) :
    ⇓PDL[m, s ⊨ d⟨a*⟩p ↔ (p ∨ d⟨a⟩(d⟨a*⟩p))] := sorry

/-- (vi) Induction: valid on frames regular for `*`. -/
theorem ind (h : m.lts.IsRegularPDL) :
    ⇓PDL[m, s ⊨ d[a*](p → d[a]p) → (p → d[a*]p)] := sorry

/-- Test axiom (not in BRV's test-free list): needs a standard model. -/
theorem test (h : m.IsStandard) :
    ⇓PDL[m, s ⊨ d⟨?' ψ⟩p ↔ (ψ ∧ p)] := sorry

end Axioms

end Cslib.Logic.Modal.PDL
