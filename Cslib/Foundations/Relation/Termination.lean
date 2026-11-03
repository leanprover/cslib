/-
Copyright (c) 2025 Fabrizio Montesi and Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Thomas Waring, Chris Henson
-/

module

public import Cslib.Foundations.Relation.Basic

/-! # Termination (well-foundedness) properties of relations -/

@[expose] public section

variable {α : Type*} {r r₁ r₂ : α → α → Prop}

namespace Relation

theorem normal_iff (r : α → α → Prop) (x : α) : Normal r x ↔ ∀ y, ¬ r x y := by
  rw [Normal, not_exists]

@[deprecated (since := "2026-09-03")] alias Normal_iff := normal_iff

/-- A multi-step from a normal form must be reflexive. -/
@[grind =>]
theorem Normal.reflTransGen_eq (h : Normal r x) (xy : ReflTransGen r x y) : x = y := by
  induction xy <;> grind

lemma SN_iff_SN_of_rel (x : α) : SN r x ↔ ∀ y, r x y → SN r y := by grind [Acc]

lemma SN.intro : (h : ∀ y, r x y → SN r y) → SN r x := (SN_iff_SN_of_rel x).mpr

lemma SN.of_rel (hx : SN r x) (h : r x y) : SN r y := Acc.inv hx h

@[grind →]
lemma SN.of_rel_reflTransGen (hx : SN r x) (h : ReflTransGen r x y) : SN r y := by
  induction h with
  | refl => exact hx
  | tail _ h ih => exact ih.of_rel h

lemma SN.transGen (hx : SN r x) : SN (TransGen r) x := by
  have eq : TransGen (Function.swap r) = (fun a b => TransGen r b a) := by
    ext
    exact transGen_swap
  simpa [eq] using Acc.transGen hx

lemma SN.of_le {r' : α → α → Prop} (hx : SN r x) (h : r' ≤ r) : SN r' x := by
  refine Subrelation.accessible ?_ hx
  exact subrelation_iff_le.mpr fun {x y} => h y x

@[simp]
lemma SN.iff_transGen (x : α) : SN (TransGen r) x ↔ SN r x :=
  ⟨fun hx => hx.of_le <| fun _ _ => TransGen.single, transGen⟩

/-- `SN r x` is equivalent to the more elementary definition, that there is no infinite sequence
of reductions starting with `x`. -/
theorem SN.iff_isEmpty_chain :
    SN r x ↔ IsEmpty {f : ℕ → α | f 0 = x ∧ ∀ n, r (f n) (f (n + 1))} :=
  acc_iff_isEmpty_descending_chain

lemma SN.onFun_of_image {r : β → β → Prop} {f : α → β} (hx : SN r (f x)) :
    SN (Function.onFun r f) x := InvImage.accessible f hx

lemma SN.of_normal (hx : Normal r x) : SN r x := SN.intro fun y hy => (hx ⟨y, hy⟩).elim

theorem SN.normalizable (hx : SN r x) : Normalizable r x := by
  induction hx with | intro x h ih =>
  by_cases hy: (∃ y, r x y)
  · obtain ⟨y, hy⟩ := hy
    obtain ⟨z, hz, hnormal⟩ := ih y hy
    exact ⟨z, .head hy hz, hnormal⟩
  · exists x

lemma Terminating.apply (hr : Terminating r) (x : α) : SN r x := WellFounded.apply hr x

lemma Terminating.iff_forall_sn : Terminating r ↔ ∀ x, SN r x :=
  ⟨WellFounded.apply, WellFounded.intro⟩

theorem Terminating.to_transGen (ht : Terminating r) : Terminating (TransGen r) := by
  simp_rw [iff_forall_sn, SN.iff_transGen] at ht ⊢
  exact ht

@[deprecated (since := "2026-09-03")] alias Terminating.toTransGen := Terminating.to_transGen

/-- A terminating relation is acyclic. -/
theorem Terminating.to_acyclic (ht : Terminating r) : Acyclic r :=
  ⟨fun x hx => ht.to_transGen.irrefl.irrefl x hx⟩

@[deprecated (since := "2026-09-03")] alias Terminating.toAcyclic := Terminating.to_acyclic

theorem Terminating.of_transGen : Terminating (TransGen r) → Terminating r := by
  simp_rw [iff_forall_sn, SN.iff_transGen]
  exact id

@[deprecated (since := "2026-09-03")] alias Terminating.ofTransGen := Terminating.of_transGen

theorem Terminating.iff_transGen : Terminating (TransGen r) ↔ Terminating r := by
  simp_rw [iff_forall_sn, SN.iff_transGen]

theorem Terminating.iff_isEmpty_chain :
    Terminating r ↔ IsEmpty {f : ℕ → α // ∀ n, r (f n) (f (n + 1))} :=
  wellFounded_iff_isEmpty_descending_chain

theorem Terminating.of_le {r' : α → α → Prop} (hr : Terminating r) (h : r' ≤ r) :
    Terminating r' := by
  rw [iff_forall_sn] at hr ⊢
  exact fun x => (hr x).of_le h

lemma Terminating.subtype_sn (r : α → α → Prop) :
    Terminating (α := {x // SN r x}) (fun a b => r a b) :=
  iff_forall_sn.mpr fun x => x.property.onFun_of_image

theorem Terminating.to_normalizing (hr : Terminating r) : Normalizing r :=
  fun x => (hr.apply x).normalizable

@[deprecated (since := "2026-09-03")] alias Terminating.isNormalizing := Terminating.to_normalizing

end Relation
