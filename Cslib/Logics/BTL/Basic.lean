/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Logics.Modal.Unary.Basic

/-! # Basic Temporal Logic (BTL)

The basic temporal language has two unary modalities: `F` (sometime in the future) and
`P` (sometime in the past). Their duals are `G` (always in the future) and `H` (always in
the past).

## Notation

Open `Cslib.Logic.Modal.BTL` for `F`, `P`, `G`, `H`, and the judgement `BTL[m,w ⊨ φ]`.
Satisfaction is expressed by `⇓BTL[m,w ⊨ φ]`, using the modal inference system.

## References

* [P. Blackburn, M. de Rijke, Y. Venema, *Modal Logic*][Blackburn2001]
-/

@[expose] public section

namespace Cslib.Logic.Modal

namespace BTL

/-- The two directions of the basic temporal language. -/
inductive Direction where
  /-- Into the future. -/
  | future
  /-- Into the past. -/
  | past
  deriving DecidableEq

/-- The modal signature of the basic temporal language. -/
abbrev τBTL : PFunctor := PFunctor.mkUnary Direction

/-- Temporal propositions, with a unary modality for each direction. -/
abbrev Proposition Atom := Modal.Proposition τBTL Atom

/-! Operator notation for BTL. -/

/-- Sometime in the future. -/
scoped prefix:40 "F" => fun φ => d⟨Direction.future⟩φ
/-- Sometime in the past. -/
scoped prefix:40 "P" => fun φ => d⟨Direction.past⟩φ
/-- Every time in the future: 'It is always going to be the case that ...' -/
scoped prefix:40 "G" => fun φ => d[Direction.future]φ
/-- Every time in the past: 'It has always been the case that ...' -/
scoped prefix:40 "H" => fun φ => d[Direction.past]φ

@[scoped grind =, modal =]
theorem Proposition.always_eq_not_future_not (φ : Proposition Atom) : (G φ) = ¬F¬φ := rfl

@[scoped grind =, modal =]
theorem Proposition.hasAlwaysBeen_eq_not_past_not (φ : Proposition Atom) : (H φ) = ¬P¬φ := rfl

/-- A temporal model consists of an accessibility relation and a valuation at each world.

No order properties are imposed on the relation. In particular, the modalities include
the present only when the relation is reflexive at the current world, and the flow of time is
modelled only when the relation is transitive.
-/
structure Model World Atom where
  /-- The accessibility relation. -/
  r : World → World → Prop
  /-- Valuation of atoms at each world. -/
  v : World → Atom → Prop

/-- The bidirectional frame of a temporal model.

This definition guarantees by construction that the future and past accessibility relations are
inverse of each other. Modally, this is witnessed by `btl_future_past_prop` and
`btl_past_future_prop`.
-/
def Model.toFrame (m : Model World Atom) : Frame World τBTL :=
  Frame.ofRelations fun
    | .future => m.r
    | .past => flip m.r

/-- Interprets a temporal model as a unary modal model. -/
def Model.toModal (m : Model World Atom) : Modal.Model World τBTL Atom := ⟨m.toFrame, m.v⟩

@[simp, scoped grind =, modal =]
theorem Model.toModal_toFrame (m : Model World Atom) : m.toModal.toFrame = m.toFrame := rfl

@[simp, scoped grind =, modal =]
theorem Model.toFrame_future_iff (m : Model World Atom) (w w' : World) :
    m.toFrame.diagonal .future w w' ↔ m.r w w' := Iff.rfl

@[simp, scoped grind =, modal =]
theorem Model.toFrame_past_iff (m : Model World Atom) (w w' : World) :
    m.toFrame.diagonal .past w w' ↔ m.r w' w := Iff.rfl

/-- Shortcut for `Modal[BTL.Model.toModal m,w ⊨ φ]`. -/
scoped notation "BTL[" m "," w " ⊨ " φ "]" => Modal[BTL.Model.toModal m,w ⊨ φ]

/-- The future and past modalities in a BTL model have inverse diagonal relations. -/
instance (m : Model World Atom) : m.toModal.toFrame.DiagonalInverse .future .past where
  diagonalInverse w w' := by simp [Model.toFrame_past_iff, Model.toFrame_future_iff]

end BTL

open BTL
open scoped InferenceSystem

variable {m : BTL.Model World Atom} {w w' : World} {φ : BTL.Proposition Atom}

@[scoped grind =, modal =]
theorem Satisfies.btl_atom_iff {a : Atom} : ⇓BTL[m,w ⊨ a] ↔ m.v w a := Iff.rfl

@[scoped grind =]
theorem Satisfies.btl_future_iff_exists : ⇓BTL[m,w ⊨ F φ] ↔ ∃ w', m.r w w' ∧ ⇓BTL[m,w' ⊨ φ] :=
  Satisfies.dynDiamond_iff_exists

@[scoped grind =]
theorem Satisfies.btl_past_iff_exists : ⇓BTL[m,w ⊨ P φ] ↔ ∃ w', m.r w' w ∧ ⇓BTL[m,w' ⊨ φ] :=
  Satisfies.dynDiamond_iff_exists

@[scoped grind =]
theorem Satisfies.btl_always_iff_forall : ⇓BTL[m,w ⊨ G φ] ↔ ∀ w', m.r w w' → ⇓BTL[m,w' ⊨ φ] :=
  Satisfies.dynBox_iff_forall

@[scoped grind =]
theorem Satisfies.btl_hasAlwaysBeen_iff_forall :
    ⇓BTL[m,w ⊨ H φ] ↔ ∀ w', m.r w' w → ⇓BTL[m,w' ⊨ φ] := Satisfies.dynBox_iff_forall

@[modal ⇒]
theorem Satisfies.btl_future_intro (hr : m.r w w') (h : ⇓BTL[m,w' ⊨ φ]) : ⇓BTL[m,w ⊨ F φ] :=
  btl_future_iff_exists.mpr ⟨w', hr, h⟩

@[modal ⇒]
theorem Satisfies.btl_past_intro (hr : m.r w' w) (h : ⇓BTL[m,w' ⊨ φ]) : ⇓BTL[m,w ⊨ P φ] :=
  btl_past_iff_exists.mpr ⟨w', hr, h⟩

@[modal ⇒]
theorem Satisfies.btl_always_elim (h : ⇓BTL[m,w ⊨ G φ]) (hr : m.r w w') : ⇓BTL[m,w' ⊨ φ] :=
  btl_always_iff_forall.mp h w' hr

@[modal ⇒]
theorem Satisfies.btl_hasAlwaysBeen_elim (h : ⇓BTL[m,w ⊨ H φ]) (hr : m.r w' w) : ⇓BTL[m,w' ⊨ φ] :=
  btl_hasAlwaysBeen_iff_forall.mp h w' hr

/-- If a proposition holds now, then it is always going to be the case that it was true. -/
theorem Satisfies.btl_future_past : ⇓BTL[m,w ⊨ φ → G P φ] :=
  Satisfies.dynBox_dynDiamond_diagonalInverse₁

/-- If a proposition holds now, then it has always been the case that it will be true. -/
theorem Satisfies.btl_past_future : ⇓BTL[m,w ⊨ φ → H F φ] :=
  Satisfies.dynBox_dynDiamond_diagonalInverse₂

end Cslib.Logic.Modal
