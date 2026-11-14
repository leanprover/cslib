/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Init
public import Mathlib.Combinatorics.Configuration

/-!
# Projective completion of an affine plane

An affine plane can be presented by its set `D` of points together with, for each direction
`p : Dir`, the equivalence relation `E p` of lying on a common line of direction `p`. The
conditions are that two distinct points lie on a common line of exactly one direction, and that
lines of different directions meet. Adjoining one point at infinity for each direction, and one
line at infinity containing them, gives a projective plane in the sense of Mathlib's
`Configuration.ProjectivePlane`.

This module is a deliberately minimal development of what is needed to pass from a representation
of a Lyndon algebra to a projective plane, and is intended to be replaced once finite geometry is
further developed in Mathlib. Only the statement listed below is public.

## Main statements

* `Cslib.exists_projectivePlane_order_of_setoid`: when there are finitely many directions, the
  projective completion is a finite projective plane whose order is one less than the number of
  directions.

-/

universe u v

namespace Cslib

open Configuration

/-- An affine plane presented by its parallel classes: `rel p x y` means that `x` and `y` lie on a
common line of direction `p`. -/
structure ParallelClasses (D : Type u) (Dir : Type v) where
  rel : Dir → D → D → Prop
  refl {p x} : rel p x x
  symm {p x y} : rel p x y → rel p y x
  trans {p x y z} : rel p x y → rel p y z → rel p x z
  exists_rel {x y} : x ≠ y → ∃ p, rel p x y
  eq_of_rel {p q x y} : x ≠ y → rel p x y → rel q x y → p = q
  exists_rel_rel {p q} : p ≠ q → ∀ x z, ∃ y, rel p x y ∧ rel q y z
  exists_ne : ∃ x y : D, x ≠ y
  exists_dir : ∃ a b c : Dir, a ≠ b ∧ b ≠ c ∧ a ≠ c

namespace ParallelClasses

variable {D : Type u} {Dir : Type v} (π : ParallelClasses D Dir)

/-- The equivalence relation of lying on a common line of a given direction. -/
def setoid (p : Dir) : Setoid D := ⟨π.rel p, ⟨fun _ => π.refl, π.symm, π.trans⟩⟩

/-- The affine line of direction `p` through `x`. -/
def line (p : Dir) (x : D) : Quotient (π.setoid p) := Quotient.mk _ x

theorem line_eq_line {p : Dir} {x y : D} : π.line p x = π.line p y ↔ π.rel p x y :=
  Quotient.eq

/-- The points of the projective completion: the affine points and the directions. -/
def Points (_ : ParallelClasses D Dir) : Type _ := D ⊕ Dir

/-- The lines of the projective completion: the affine lines, each with its direction, and the
line at infinity. -/
def Lines : Type _ := (Σ p : Dir, Quotient (π.setoid p)) ⊕ Unit

/-- An affine point of the projective completion. -/
def point (x : D) : π.Points := Sum.inl x

/-- The point at infinity of a direction. -/
def dir (p : Dir) : π.Points := Sum.inr p

/-- The affine line of direction `p` through `x`, as a line of the projective completion. -/
def affineLine (p : Dir) (x : D) : π.Lines := Sum.inl ⟨p, π.line p x⟩

/-- The line at infinity. -/
def infinity : π.Lines := Sum.inr ()

instance : Membership π.Points π.Lines where
  mem l pt :=
    match pt, l with
    | .inl x, .inl ⟨p, c⟩ => π.line p x = c
    | .inr q, .inl ⟨p, _⟩ => q = p
    | .inl _, .inr _ => False
    | .inr _, .inr _ => True

@[elab_as_elim]
theorem points_induction {motive : π.Points → Prop} (pt : π.Points)
    (point : ∀ x, motive (π.point x)) (dir : ∀ p, motive (π.dir p)) : motive pt :=
  match pt with
  | .inl x => point x
  | .inr p => dir p

@[elab_as_elim]
theorem lines_induction {motive : π.Lines → Prop} (l : π.Lines)
    (affineLine : ∀ p x, motive (π.affineLine p x)) (infinity : motive π.infinity) : motive l :=
  match l with
  | .inl ⟨p, c⟩ => Quotient.inductionOn c (affineLine p)
  | .inr () => infinity

variable {π} {p q : Dir} {x y : D}

@[simp]
theorem point_mem_affineLine : π.point x ∈ π.affineLine p y ↔ π.rel p x y := π.line_eq_line

@[simp]
theorem dir_mem_affineLine : π.dir q ∈ π.affineLine p x ↔ q = p := .rfl

@[simp]
theorem point_notMem_infinity : π.point x ∉ π.infinity := id

@[simp]
theorem dir_mem_infinity : π.dir p ∈ π.infinity := trivial

@[simp]
theorem point_inj : π.point x = π.point y ↔ x = y := Sum.inl_injective.eq_iff

@[simp]
theorem dir_inj : π.dir p = π.dir q ↔ p = q := Sum.inr_injective.eq_iff

@[simp]
theorem point_ne_dir : π.point x ≠ π.dir p := Sum.inl_ne_inr

@[simp]
theorem dir_ne_point : π.dir p ≠ π.point x := Sum.inr_ne_inl

@[simp]
theorem affineLine_ne_infinity : π.affineLine p x ≠ π.infinity := Sum.inl_ne_inr

@[simp]
theorem infinity_ne_affineLine : π.infinity ≠ π.affineLine p x := Sum.inr_ne_inl

@[simp]
theorem affineLine_eq_affineLine :
    π.affineLine p x = π.affineLine q y ↔ p = q ∧ π.rel p x y := by
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨rfl, h⟩ := Sigma.mk.inj (Sum.inl_injective h)
    exact ⟨rfl, π.line_eq_line.mp (eq_of_heq h)⟩
  · rintro ⟨rfl, h⟩
    rw [affineLine, affineLine, π.line_eq_line.mpr h]

variable (π)

theorem exists_line_mem (pt₁ pt₂ : π.Points) (h : pt₁ ≠ pt₂) :
    ∃ l : π.Lines, pt₁ ∈ l ∧ pt₂ ∈ l := by
  induction pt₁ using points_induction with
  | point x =>
    induction pt₂ using points_induction with
    | point y =>
      obtain ⟨p, hp⟩ := π.exists_rel fun hxy => h (congrArg π.point hxy)
      exact ⟨π.affineLine p y, by simp [hp, π.refl]⟩
    | dir q => exact ⟨π.affineLine q x, by simp [π.refl]⟩
  | dir p =>
    induction pt₂ using points_induction with
    | point y => exact ⟨π.affineLine p y, by simp [π.refl]⟩
    | dir q => exact ⟨π.infinity, by simp⟩

theorem exists_point_mem (l₁ l₂ : π.Lines) : ∃ pt : π.Points, pt ∈ l₁ ∧ pt ∈ l₂ := by
  induction l₁ using lines_induction with
  | infinity =>
    induction l₂ using lines_induction with
    | infinity => exact ⟨π.dir π.exists_dir.choose, by simp⟩
    | affineLine q z => exact ⟨π.dir q, by simp⟩
  | affineLine p x =>
    induction l₂ using lines_induction with
    | infinity => exact ⟨π.dir p, by simp⟩
    | affineLine q z =>
      by_cases hpq : p = q
      · exact ⟨π.dir p, by simp [hpq]⟩
      · obtain ⟨y, hxy, hyz⟩ := π.exists_rel_rel hpq x z
        exact ⟨π.point y, by simp [π.symm hxy, hyz]⟩

theorem eq_or_eq {pt₁ pt₂ : π.Points} {l₁ l₂ : π.Lines} (h₁₁ : pt₁ ∈ l₁) (h₂₁ : pt₂ ∈ l₁)
    (h₁₂ : pt₁ ∈ l₂) (h₂₂ : pt₂ ∈ l₂) : pt₁ = pt₂ ∨ l₁ = l₂ := by
  induction l₁ using lines_induction <;> induction l₂ using lines_induction <;>
    induction pt₁ using points_induction <;> induction pt₂ using points_induction <;>
    simp only [point_mem_affineLine, dir_mem_affineLine, point_notMem_infinity, dir_mem_infinity,
      point_inj, dir_inj, point_ne_dir, dir_ne_point, affineLine_ne_infinity,
      infinity_ne_affineLine, affineLine_eq_affineLine, or_false, false_or, or_true] at * <;>
    grind [ParallelClasses.symm, ParallelClasses.trans, ParallelClasses.eq_of_rel]

include π in
/-- Every direction is avoided by two further distinct directions. -/
theorem exists_dir_ne (p : Dir) : ∃ a c, a ≠ p ∧ c ≠ p ∧ a ≠ c := by
  obtain ⟨a, b, c, hab, hbc, hac⟩ := π.exists_dir
  by_cases ha : a = p
  · exact ⟨b, c, by grind, by grind, hbc⟩
  by_cases hb : b = p
  · exact ⟨a, c, ha, by grind, hac⟩
  · exact ⟨a, b, ha, hb, hab⟩

instance : Nondegenerate π.Points π.Lines where
  exists_point l := by
    induction l using lines_induction with
    | affineLine p x =>
      obtain ⟨q, -, hq, -, -⟩ := π.exists_dir_ne p
      exact ⟨π.dir q, by simpa using hq⟩
    | infinity =>
      obtain ⟨x, -⟩ := π.exists_ne
      exact ⟨π.point x, point_notMem_infinity⟩
  exists_line pt := by
    induction pt using points_induction with
    | point x => exact ⟨π.infinity, point_notMem_infinity⟩
    | dir p =>
      obtain ⟨q, -, hq, -, -⟩ := π.exists_dir_ne p
      obtain ⟨x, -⟩ := π.exists_ne
      exact ⟨π.affineLine q x, by simpa using hq.symm⟩
  eq_or_eq := π.eq_or_eq

/-- The projective completion of an affine plane presented by its parallel classes. -/
noncomputable instance : ProjectivePlane π.Points π.Lines where
  mkPoint {l₁ l₂} _ := (π.exists_point_mem l₁ l₂).choose
  mkPoint_ax {l₁ l₂} _ := (π.exists_point_mem l₁ l₂).choose_spec
  mkLine h := (π.exists_line_mem _ _ h).choose
  mkLine_ax h := (π.exists_line_mem _ _ h).choose_spec
  exists_config := by
    obtain ⟨x, y, hxy⟩ := π.exists_ne
    obtain ⟨b, hb⟩ := π.exists_rel hxy
    obtain ⟨a, c, hab, hcb, hac⟩ := π.exists_dir_ne b
    refine ⟨π.point y, π.dir a, π.dir b, π.affineLine c x, π.infinity, π.affineLine a x,
      point_notMem_infinity, ?_, by simpa using hac, dir_mem_infinity, by simp,
      by simpa using hcb.symm, dir_mem_infinity, by simpa using hab.symm⟩
    rw [point_mem_affineLine]
    exact fun hyx => hab (π.eq_of_rel hxy (π.symm hyx) hb)

/-- The points on the line at infinity are the directions. -/
def infinityEquiv : {pt : π.Points // pt ∈ π.infinity} ≃ Dir where
  toFun
    | ⟨.inr p, _⟩ => p
    | ⟨.inl _, h⟩ => h.elim
  invFun p := ⟨π.dir p, dir_mem_infinity⟩
  left_inv
    | ⟨.inr _, _⟩ => rfl
    | ⟨.inl _, h⟩ => h.elim
  right_inv _ := rfl

section Finite

open scoped Classical in
/-- The direction of the line through two points, or `none` if the points agree. -/
noncomputable def dirOf (o y : D) : Option Dir :=
  if h : o = y then none else some (π.exists_rel h).choose

theorem eq_or_rel_of_dirOf_eq {o y y' : D} (h : π.dirOf o y = π.dirOf o y') :
    y = y' ∨ ∃ p, o ≠ y ∧ o ≠ y' ∧ π.rel p o y ∧ π.rel p o y' := by
  unfold dirOf at h
  split_ifs at h with hy hy' hy'
  · exact .inl (hy.symm.trans hy')
  · exact .inr ⟨_, hy, hy', (π.exists_rel hy).choose_spec,
      Option.some.inj h ▸ (π.exists_rel hy').choose_spec⟩

include π in
/-- An affine plane with finitely many directions has finitely many points: a point is determined
by the directions in which it is seen from three points that are not collinear. -/
theorem finite [Finite Dir] : Finite D := by
  obtain ⟨o₁, o₂, h₁₂⟩ := π.exists_ne
  obtain ⟨a, ha⟩ := π.exists_rel h₁₂
  obtain ⟨b, c, hba, hca, hbc⟩ := π.exists_dir_ne a
  obtain ⟨o₃, hb, hc⟩ := π.exists_rel_rel hbc o₁ o₂
  refine Finite.of_injective (fun y => (π.dirOf o₁ y, π.dirOf o₂ y, π.dirOf o₃ y)) fun y y' h => ?_
  rw [Prod.mk.injEq, Prod.mk.injEq] at h
  have h₁ := π.eq_or_rel_of_dirOf_eq h.1
  have h₂ := π.eq_or_rel_of_dirOf_eq h.2.1
  have h₃ := π.eq_or_rel_of_dirOf_eq h.2.2
  grind [ParallelClasses.symm, ParallelClasses.trans, ParallelClasses.eq_of_rel]

variable [Finite Dir]

instance : Finite π.Points :=
  have := π.finite
  inferInstanceAs (Finite (D ⊕ Dir))

instance : Finite π.Lines :=
  have := π.finite
  inferInstanceAs (Finite ((Σ p : Dir, Quotient (π.setoid p)) ⊕ Unit))

/-- The order of the projective completion is one less than the number of directions. -/
theorem order_add_one : ProjectivePlane.order π.Points π.Lines + 1 = Nat.card Dir := by
  rw [← ProjectivePlane.pointCount_eq π.Points π.infinity, pointCount]
  exact Nat.card_congr π.infinityEquiv

end Finite

end ParallelClasses

/-- The projective completion of an affine plane, presented by its parallel classes, is a
projective plane. Here `E p x y` means that the points `x` and `y` lie on a common line of
direction `p`: two distinct points lie on a common line of exactly one direction, and two lines of
different directions meet. When there are finitely many directions, the completion is finite and
its order is one less than the number of directions. -/
public theorem exists_projectivePlane_order_of_setoid {D : Type u} {Dir : Type v} [Nontrivial D]
    [Finite Dir] (E : Dir → Setoid D) (hDir : ∃ a b c : Dir, a ≠ b ∧ b ≠ c ∧ a ≠ c)
    (h₁ : ∀ x y, x ≠ y → ∃! p, E p x y)
    (h₂ : ∀ p q, p ≠ q → ∀ x z, ∃ y, E p x y ∧ E q y z) :
    ∃ (P L : Type (max u v)) (_ : Membership P L) (_ : ProjectivePlane P L) (_ : Finite P)
      (_ : Finite L), ProjectivePlane.order P L + 1 = Nat.card Dir :=
  let π : ParallelClasses D Dir :=
    { rel p := E p
      refl := (E _).refl _
      symm := (E _).symm
      trans := (E _).trans
      exists_rel hxy := (h₁ _ _ hxy).exists
      eq_of_rel hxy hp hq := (h₁ _ _ hxy).unique hp hq
      exists_rel_rel hpq := h₂ _ _ hpq
      exists_ne := exists_pair_ne D
      exists_dir := hDir }
  ⟨π.Points, π.Lines, inferInstance, inferInstance, inferInstance, inferInstance, π.order_add_one⟩

end Cslib
