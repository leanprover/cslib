/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Marianna Girlando
-/

module

public import Cslib.Logics.Modal.Unary.Basic
public import Cslib.Logics.Modal.LogicalEquivalence

/-! # Basic Modal Logic

Basic modal logic is the modal logic with a single unary modality.

## References

* [P. Blackburn, M. de Rijke, Y. Venema, *Modal Logic*][Blackburn2001]
-/

@[expose] public section

namespace Cslib

section Unimodal

open PFunctor

variable {τ : PFunctor} [Unary τ] [Unique τ.A]

namespace Frame

/-- The accessibility relation of a unimodal frame. -/
@[instance_reducible]
def rel (f : Frame World τ) : World → World → Prop := f.diagonal default

omit [Unary τ] in
@[scoped grind =, modal =]
theorem rel_iff_diagonal (f : Frame World τ) (w w' : World) :
    f.rel w w' ↔ f.diagonal default w w' := by rfl

/-- Builds a unimodal frame out of a binary relation. -/
@[instance_reducible]
def ofRelation (r : World → World → Prop) : Frame World τ where
  r := fun _ w ws => r w (ws default)

@[simp, scoped grind =, modal =]
theorem ofRelation_rel (r : World → World → Prop) : Frame.rel (Frame.ofRelation (τ := τ) r) = r :=
  rfl

instance {r : World → World → Prop} [Std.Refl r] : Std.Refl (ofRelation (τ := τ) r).rel := by
  infer_instance

instance {r : World → World → Prop} [Std.Symm r] : Std.Symm (ofRelation (τ := τ) r).rel := by
  infer_instance

instance {r : World → World → Prop} [IsTrans World r] :
    IsTrans World (Frame.ofRelation (τ := τ) r).rel := by
  change IsTrans World r
  infer_instance

@[scoped grind =, modal =]
theorem ofRelation_rel_iff (r : World → World → Prop) (w w' : World) :
    (ofRelation (τ := τ) r).rel w w' ↔ r w w' := by rfl

@[scoped grind ., modal .]
theorem ofRelation_rel_of {r : World → World → Prop} {w w' : World}
    (h : r w w') : (ofRelation (τ := τ) r).rel w w' := by grind

open Relation in
@[scoped grind =, modal =]
theorem preservesMap_const_iff_preserves {r : α → α → Prop} {P : α → Prop} :
    (ofRelation (τ := τ) r).PreservesMap default P (fun _ => P) ↔ Preserves r P := by
  constructor
  · intro h a₁ a₂ hr hP
    obtain ⟨i, hi⟩ := h a₁ (fun _ => a₂) hr hP
    exact hi
  · intro h a₁ ws hr hP
    refine ⟨default, ?_⟩
    exact h hr hP

end Frame

namespace Logic.Modal

open scoped InferenceSystem Satisfies Proposition Proposition.Context Frame

@[scoped grind =]
theorem Satisfies.diamond_iff_exists {m : Model World τ Atom} {φ : Proposition τ Atom} :
    ⇓Modal[m,w ⊨ ◇φ] ↔ ∃ w', m.rel w w' ∧ ⇓Modal[m,w' ⊨ φ] := by
  grind [diamond_eq_dynDiamond (φ := φ)]

@[scoped grind →, modal →]
theorem Satisfies.diamond_of {m : Model World τ Atom} {φ : Proposition τ Atom}
    (hr : m.toFrame.rel w w') (hφ : ⇓Modal[m,w' ⊨ φ]) : ⇓Modal[m,w ⊨ ◇φ] :=
  Satisfies.diamond_iff_exists.mpr ⟨w', hr, hφ⟩

@[scoped grind =]
theorem Satisfies.box_iff_forall {m : Model World τ Atom} {φ : Proposition τ Atom} :
    ⇓Modal[m,w ⊨ □φ] ↔ ∀ w', m.rel w w' → ⇓Modal[m,w' ⊨ φ] :=
  Satisfies.dynBox_iff_forall

/-- Axiom K for unimodal logic. -/
@[scoped grind ., modal .]
theorem Satisfies.unimodal_k (f : Frame World τ) (φ₁ φ₂ : Proposition τ Atom) :
    Axiom f⇓(□(φ₁ → φ₂) → (□φ₁ → □φ₂)) := by grind

/-- The dual axiom for unimodal logic. -/
theorem Satisfies.unimodal_dual (f : Frame World τ) (φ : Proposition τ Atom) :
    Axiom f⇓(◇φ ↔ ¬□¬φ) := by grind

@[scoped grind ., modal .]
theorem Satisfies.diamond_and (f : Frame World τ) (φ₁ φ₂ : Proposition τ Atom) :
    Axiom f⇓(◇(φ₁ ∧ φ₂) → (◇φ₁ ∧ ◇φ₂)) := by grind

@[modal .]
theorem Satisfies.diamond_and_box (f : Frame World τ) (φ₁ φ₂ : Proposition τ Atom) :
    Axiom f⇓((◇φ₁ ∧ □φ₂) → ◇(φ₁ ∧ φ₂)) := by grind

@[scoped grind ., modal .]
theorem Satisfies.diamond_of_box (f : Frame World τ) (φ₁ φ₂ : Proposition τ Atom) :
    Axiom f⇓(□φ₁ ∧ ◇φ₂ → ◇φ₁) := by grind

/-- Axiom T. -/
theorem Satisfies.unimodal_t (f : Frame World τ) [instRefl : Std.Refl f.rel]
    (φ : Proposition τ Atom) : Axiom f⇓(φ → ◇φ) := by grind [instRefl.refl]

/-- Any frame that admits T is reflexive. -/
theorem Satisfies.unimodal_t_refl (f : Frame World τ) [Nonempty Atom]
    (h : ∀ φ : Proposition τ Atom, Axiom f⇓(φ → ◇φ)) : Std.Refl f.rel where
  refl w := by
    have a := Classical.arbitrary Atom
    let v := fun (w' : World) (a : Atom) => w' = w
    let h' := h (v := v) (w := w) (φ := a)
    grind

/-- In any reflexive model, `□φ → φ` is equivalent to `φ → ◇φ`. -/
theorem Satisfies.t_box_diamond {m : Model World τ Atom} [Std.Refl m.rel] :
    ⇓Modal[m,w ⊨ □φ → φ] ↔ ⇓Modal[m,w ⊨ φ → ◇φ] := by
  have := Std.Refl.refl (r := m.rel) w
  grind

/-- Axiom B. -/
theorem Satisfies.unimodal_b (f : Frame World τ) [Std.Symm f.rel]
    (φ : Proposition τ Atom) : Axiom f⇓(φ → □◇φ) := by
  intro _ w
  have := Std.Symm.symm (r := f.rel) w
  grind

/-- Any frame that admits B is symmetric. -/
theorem Satisfies.unimodal_b_symm (f : Frame World τ) [Nonempty Atom]
    (h : ∀ φ : Proposition τ Atom, Axiom f⇓(φ → □◇φ)) : Std.Symm f.rel where
  symm w₁ := by
    have a := Classical.arbitrary Atom
    let v₁ := fun (w' : World) (a : Atom) => w' = w₁
    let h₁ := h (v := v₁) (w := w₁) (φ := a)
    grind

/-- Axiom 4, valid for all transitive frames. -/
theorem Satisfies.unimodal_four (f : Frame World τ) [IsTrans World f.rel]
    (φ : Proposition τ Atom) : Axiom f⇓(◇◇φ → ◇φ) := by
  intro _ _
  simp only [Satisfies.imp_iff_imp, Satisfies.diamond_iff_exists]
  rintro ⟨w', h₁, w'', h₂, hs⟩
  exact ⟨w'', IsTrans.trans _ _ _ h₁ h₂, hs⟩

/-- Any frame that admits 4 is transitive. -/
theorem Satisfies.unimodal_four_trans (f : Frame World τ) [Nonempty Atom]
    (h : ∀ (φ : Proposition τ Atom), Axiom f⇓(◇◇φ → ◇φ)) : IsTrans World f.rel where
  trans w₁ w₂ w₃ h₁ h₂ := by
    have a := Classical.arbitrary Atom
    let v := fun (w' : World) (a : Atom) => w' = w₃
    let h' := h (v := v) (w := w₁) (φ := a)
    grind

/-- Axiom 5. -/
theorem Satisfies.unimodal_five (f : Frame World τ) [Relation.RightEuclidean f.rel]
    (φ : Proposition τ Atom) : Axiom f⇓(◇φ → □◇φ) := by
  have := @Relation.RightEuclidean.rightEuclidean (r := f.rel)
  grind

/-- Any frame that admits 5 is Euclidean. -/
theorem Satisfies.unimodal_five_rightEuclidean (f : Frame World τ) [Nonempty Atom]
    (h : ∀ φ : Proposition τ Atom, Axiom f⇓(◇φ → □◇φ)) :
    Relation.RightEuclidean f.rel where
  rightEuclidean {w₁ w₂ w₃} h₁ h₂ := by
    have a := Classical.arbitrary Atom
    let v := fun (w' : World) (a : Atom) => w' = w₃
    let h' := h (v := v) (w := w₁) (φ := a)
    grind

/-- Axiom D, valid for all serial frames. -/
theorem Satisfies.d (f : Frame World τ) [Relation.Serial f.rel]
    (φ : Proposition τ Atom) : Axiom f⇓(□φ → ◇φ) := by
  intro _ w
  have : ∃ w', f.rel w w' := Relation.Serial.serial w
  grind

/-- Any model that admits D is serial. -/
theorem Satisfies.d_serial (f : Frame World τ) [Nonempty Atom]
    (h : ∀ φ : Proposition τ Atom, Axiom f⇓(□φ → ◇φ)) : Relation.Serial f.rel where
  serial w₁ := by
    have a := Classical.arbitrary Atom
    let v := fun (w' : World) (a : Atom) => w' = w₁
    let h' := h (v := v) (w := w₁) (φ := a)
    grind

/-- The L axiom, or Löb's theorem, valid for all transitive and converse well-founded models. -/
theorem Satisfies.l (f : Frame World τ) [IsTrans World f.rel]
    (hwf : Relation.Terminating f.rel) (φ : Proposition τ Atom) :
    Axiom f⇓(□(□φ → φ) → □φ) := by
  intro v w
  let m : Model World τ Atom := ⟨f, v⟩
  simp_rw [Satisfies.imp_iff_imp, Satisfies.box_iff_forall]
  intro h
  refine (hwf.induction (C := fun w' : World => f.rel w w' → ⇓Modal[m,w' ⊨ φ]) · ?_)
  intro w' ih hww'
  have hImp : ⇓Modal[m,w' ⊨ □φ → φ] := h _ hww'
  rw [Satisfies.imp_iff_imp, Satisfies.box_iff_forall (τ := τ)] at hImp
  apply hImp
  intro w'' hw'w''
  apply ih _ hw'w''
  exact IsTrans.trans _ _ _ hww' hw'w''

/-- Löb induction, via the L axiom. -/
theorem Satisfies.l_induction (m : Model World τ Atom) [IsTrans World m.rel]
    (hwf : Relation.Terminating m.rel) (hstep : ∀ w, ⇓Modal[m,w ⊨ □φ → φ]) (w : World) :
    ⇓Modal[m, w ⊨ φ] := by
  have hl := Satisfies.of_axiom m _ (Satisfies.l m.toFrame hwf φ) w
  /- We use `grind only` here as a memo and test that the `modal` grind set should be able to derive
    (the modal part of) this proof. -/
  grind only [modal, = box_iff_forall]

open Relation in
/-- Axiom .2, valid for all frames with the diamond property. -/
theorem Satisfies.pointTwo (f : Frame World τ) (h : Diamond f.rel)
    (φ : Proposition τ Atom) : Axiom f⇓(◇□φ → □◇φ) := by
  simp_rw [← Satisfies.axiom_def, Satisfies.imp_iff_imp, Satisfies.diamond_iff_exists,
    Satisfies.box_iff_forall]
  rintro v w ⟨_, hww₁, _⟩ _ hww₂
  obtain ⟨w₃, hww₃⟩ := h hww₁ hww₂
  grind

open Relation in
/-- Any model that admits axiom .2 has the diamond property. -/
theorem Satisfies.pointTwo_diamond (f : Frame World τ) [Nonempty Atom]
    (h : ∀ φ : Proposition τ Atom, Axiom f⇓(◇□φ → □◇φ)) : Diamond f.rel := by
  intro w w₁ w₂ hww₁ hww₂
  specialize h (Classical.arbitrary Atom) (fun w' _ => f.rel w₁ w') w
  grind [Join]

open Relation in
/-- In a transitive diamond model, possibility distributes over conjunction for propositions
whose satisfaction is preserved along accessibility. -/
@[scoped grind ⇒]
theorem Proposition.diamond_and_equiv_of_preserves {m : Model World τ Atom}
    [IsTrans World m.rel] {φ₁ φ₂ : Proposition τ Atom} (hd : Diamond m.rel)
    (h₁ : Preserves m.rel (⇓Modal[m,· ⊨ φ₁])) (h₂ : Preserves m.rel (⇓Modal[m,· ⊨ φ₂])) :
    ◇(φ₁ ∧ φ₂) ≡[Equiv m] (◇φ₁ ∧ ◇φ₂) := by
  rw [equiv_iff_forall_iff]
  intro a
  constructor
  case mp =>
    grind only [modal, Satisfies.diamond_iff_exists]
  case mpr =>
    intro h
    simp only [Satisfies.and_iff_and, Satisfies.diamond_iff_exists] at h
    obtain ⟨⟨b, hab, hb⟩, ⟨c, hac, hc⟩⟩ := h
    obtain ⟨d, hbd, hcd⟩ := hd hab hac
    rw [Satisfies.diamond_iff_exists (τ := τ)]
    refine ⟨d, IsTrans.trans a b d hab hbd, ?_⟩
    apply Satisfies.and_iff_and.mpr
    exact ⟨h₁ hbd hb, h₂ hcd hc⟩

/-- In a reflexive and transitive model, diamond absorbs itself (idempotency). -/
theorem Proposition.diamond_diamond_equiv {m : Model World τ Atom} [Std.Refl m.rel]
    [IsTrans World m.rel] (φ : Proposition τ Atom) : ◇◇φ ≡[Equiv m] ◇φ := by
  rw [equiv_iff_forall_iff]
  intro w
  constructor <;> rw [← Satisfies.imp_iff_imp]
  · grind [Satisfies.unimodal_four]
  · grind [Satisfies.unimodal_t]

/-- Context constructor for the diamond modality. -/
def Proposition.Context.diamond (c : Context τ Atom) : Context τ Atom :=
  .triangle default default c fun ⟨i, hi⟩ => (hi (Subsingleton.elim i default)).elim

/-- Constructs a signature for basic modal logic at the same universe level of the input type. -/
def τUnimodal (_ : Type u) : PFunctor.{u,u} where
  A := PUnit
  B := fun _ => PUnit

instance : (τUnimodal α).Unary where
  unary _ := by
    change Unique PUnit
    infer_instance

instance : Unique ((τUnimodal α).A) := by
  change Unique PUnit
  infer_instance

instance : (τUnimodal α).DecidableEqChildren := ⟨by infer_instance⟩

@[simp, scoped grind =, modal =]
theorem _root_.Cslib.Frame.ofRelation_unimodal_rel_iff
    (r : World → World → Prop) (w w' : World) :
    (Frame.ofRelation (τ := τUnimodal World) r).rel w w' ↔ r w w' := by
  rfl

namespace Unimodal

/-- A basic model, constructed on `τUnimodal`. -/
abbrev Model World Atom := Modal.Model World (τUnimodal Atom) Atom

/-- The language of modal propositions instantiated for `τUnimodal Atom`. -/
abbrev Proposition Atom := Modal.Proposition (τUnimodal Atom) Atom

end Unimodal

end Logic.Modal

end Unimodal

end Cslib
