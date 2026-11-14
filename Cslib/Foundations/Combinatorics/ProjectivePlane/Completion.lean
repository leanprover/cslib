/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Init
public import Mathlib.Combinatorics.Configuration

/-!
# Projective completion of an affine plane with labelled directions

An affine plane can be presented by its set `D` of points together with, for each direction
`p : Dir`, the relation `rel p x y` saying that `x` and `y` are distinct points on a common line
of direction `p`. We call such a presentation a `Parallelism`. Adjoining one point at infinity for
each direction, and one line at infinity containing them, gives a projective plane in the sense of
Mathlib's `Configuration.ProjectivePlane`.

This is deliberately minimal: it is the construction needed to pass from a representation of a
Lyndon algebra to a projective plane, and is not intended as a general theory of affine planes.

## Main definitions

* `Cslib.Parallelism`: an affine plane presented by its directions.
* `Cslib.Parallelism.Points`, `Cslib.Parallelism.Lines`: the points and lines of the projective
  completion, which is a `Configuration.ProjectivePlane`.

## Main statements

* `Cslib.Parallelism.infinityEquiv`: the points on the line at infinity are the directions.
* `Cslib.Parallelism.order_add_one`: when there are finitely many directions, the completion is
  finite and its order is one less than the number of directions.

-/

@[expose] public section

namespace Cslib

open Configuration

/-- An affine plane with points `D`, presented by its directions: `rel p x y` means that `x` and
`y` are distinct points on a common line of direction `p`. -/
structure Parallelism (D : Type*) (Dir : Type*) where
  /-- Two distinct points on a common line of the given direction. -/
  rel : Dir → D → D → Prop
  symm {p x y} : rel p x y → rel p y x
  irrefl {p x} : ¬ rel p x x
  /-- Two distinct points determine a direction. -/
  exists_rel_of_ne {x y} : x ≠ y → ∃ p, rel p x y
  /-- Two distinct points determine only one direction. -/
  eq_of_rel {p q x y} : rel p x y → rel q x y → p = q
  trans {p x y z} : rel p x y → rel p y z → x = z ∨ rel p x z
  /-- Every line has at least two points. -/
  exists_rel (p x) : ∃ y, rel p x y
  /-- Two lines of different directions meet. -/
  exists_rel_rel {p q r x z} : p ≠ q → q ≠ r → p ≠ r → rel r x z → ∃ y, rel p x y ∧ rel q y z
  nonempty : Nonempty D
  /-- There are at least three directions. -/
  exists_dir : ∃ a b c : Dir, a ≠ b ∧ b ≠ c ∧ a ≠ c

namespace Parallelism

variable {D Dir : Type*} (π : Parallelism D Dir)

/-- The equivalence relation of lying on a common line of a given direction. -/
def setoid (p : Dir) : Setoid D where
  r x y := x = y ∨ π.rel p x y
  iseqv :=
    { refl _ := .inl rfl
      symm h := h.elim (fun h => .inl h.symm) fun h => .inr (π.symm h)
      trans := by
        rintro x y z (rfl | hxy) (rfl | hyz)
        · exact .inl rfl
        · exact .inr hyz
        · exact .inr hxy
        · exact π.trans hxy hyz }

/-- The affine line of direction `p` through `x`. -/
def line (p : Dir) (x : D) : Quotient (π.setoid p) := Quotient.mk _ x

theorem line_eq_line {p : Dir} {x y : D} : π.line p x = π.line p y ↔ x = y ∨ π.rel p x y :=
  Quotient.eq

/-- The points of the projective completion: the affine points and the directions. -/
def Points (_ : Parallelism D Dir) : Type _ := D ⊕ Dir

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
theorem point_mem_affineLine : π.point x ∈ π.affineLine p y ↔ x = y ∨ π.rel p x y :=
  π.line_eq_line

@[simp]
theorem dir_mem_affineLine : π.dir q ∈ π.affineLine p x ↔ q = p := .rfl

@[simp]
theorem point_notMem_infinity : π.point x ∉ π.infinity := id

@[simp]
theorem dir_mem_infinity : π.dir p ∈ π.infinity := trivial

theorem affineLine_eq_affineLine :
    π.affineLine p x = π.affineLine q y ↔ p = q ∧ (x = y ∨ π.rel p x y) := by
  constructor
  · intro h
    obtain ⟨rfl, h⟩ := Sigma.mk.inj (Sum.inl_injective h)
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
      obtain ⟨p, hp⟩ := π.exists_rel_of_ne (fun hxy => h (congrArg π.point hxy))
      exact ⟨π.affineLine p x, by simp, by simpa using .inr (π.symm hp)⟩
    | dir q => exact ⟨π.affineLine q x, by simp, by simp⟩
  | dir p =>
    induction pt₂ using points_induction with
    | point y => exact ⟨π.affineLine p y, by simp, by simp⟩
    | dir q => exact ⟨π.infinity, by simp, by simp⟩

theorem exists_point_mem (l₁ l₂ : π.Lines) : ∃ pt : π.Points, pt ∈ l₁ ∧ pt ∈ l₂ := by
  induction l₁ using lines_induction with
  | affineLine p x =>
    induction l₂ using lines_induction with
    | affineLine q z =>
      by_cases hpq : p = q
      · exact ⟨π.dir p, by simp, by simp [hpq]⟩
      by_cases hxz : x = z
      · exact ⟨π.point x, by simp, by simp [hxz]⟩
      obtain ⟨r, hr⟩ := π.exists_rel_of_ne hxz
      by_cases hrp : p = r
      · exact ⟨π.point z, by simpa [hrp] using .inr (π.symm hr), by simp⟩
      by_cases hrq : q = r
      · exact ⟨π.point x, by simp, by simpa [hrq] using .inr hr⟩
      obtain ⟨y, hxy, hyz⟩ := π.exists_rel_rel hpq hrq hrp hr
      exact ⟨π.point y, by simpa using .inr (π.symm hxy), by simpa using .inr hyz⟩
    | infinity => exact ⟨π.dir p, by simp, by simp⟩
  | infinity =>
    induction l₂ using lines_induction with
    | affineLine q z => exact ⟨π.dir q, by simp, by simp⟩
    | infinity =>
      obtain ⟨a, -⟩ := π.exists_dir
      exact ⟨π.dir a, by simp, by simp⟩

theorem eq_or_eq {pt₁ pt₂ : π.Points} {l₁ l₂ : π.Lines} (h₁₁ : pt₁ ∈ l₁) (h₂₁ : pt₂ ∈ l₁)
    (h₁₂ : pt₁ ∈ l₂) (h₂₂ : pt₂ ∈ l₂) : pt₁ = pt₂ ∨ l₁ = l₂ := by
  induction l₁ using lines_induction with
  | infinity =>
    induction l₂ using lines_induction with
    | infinity => exact .inr rfl
    | affineLine q z =>
      induction pt₁ using points_induction with
      | point x => exact absurd h₁₁ point_notMem_infinity
      | dir a =>
        induction pt₂ using points_induction with
        | point y => exact absurd h₂₁ point_notMem_infinity
        | dir b => exact .inl (by rw [dir_mem_affineLine.mp h₁₂, dir_mem_affineLine.mp h₂₂])
  | affineLine p x =>
    induction l₂ using lines_induction with
    | infinity =>
      induction pt₁ using points_induction with
      | point x => exact absurd h₁₂ point_notMem_infinity
      | dir a =>
        induction pt₂ using points_induction with
        | point y => exact absurd h₂₂ point_notMem_infinity
        | dir b => exact .inl (by rw [dir_mem_affineLine.mp h₁₁, dir_mem_affineLine.mp h₂₁])
    | affineLine q z =>
      induction pt₁ using points_induction with
      | point u =>
        induction pt₂ using points_induction with
        | point v =>
          rw [point_mem_affineLine] at h₁₁ h₂₁ h₁₂ h₂₂
          by_cases huv : u = v
          · exact .inl (congrArg π.point huv)
          have hp : π.rel p u v := by
            have := (π.setoid p).trans h₁₁ ((π.setoid p).symm h₂₁)
            exact this.resolve_left huv
          have hq : π.rel q u v := by
            have := (π.setoid q).trans h₁₂ ((π.setoid q).symm h₂₂)
            exact this.resolve_left huv
          obtain rfl := π.eq_of_rel hp hq
          refine .inr (affineLine_eq_affineLine.mpr ⟨rfl, ?_⟩)
          exact (π.setoid p).trans ((π.setoid p).symm h₁₁) h₁₂
        | dir b =>
          rw [point_mem_affineLine] at h₁₁ h₁₂
          obtain rfl := dir_mem_affineLine.mp h₂₁
          obtain rfl := dir_mem_affineLine.mp h₂₂
          refine .inr (affineLine_eq_affineLine.mpr ⟨rfl, ?_⟩)
          exact (π.setoid b).trans ((π.setoid b).symm h₁₁) h₁₂
      | dir a =>
        induction pt₂ using points_induction with
        | point v =>
          rw [point_mem_affineLine] at h₂₁ h₂₂
          obtain rfl := dir_mem_affineLine.mp h₁₁
          obtain rfl := dir_mem_affineLine.mp h₁₂
          refine .inr (affineLine_eq_affineLine.mpr ⟨rfl, ?_⟩)
          exact (π.setoid a).trans ((π.setoid a).symm h₂₁) h₂₂
        | dir b => exact .inl (by rw [dir_mem_affineLine.mp h₁₁, dir_mem_affineLine.mp h₂₁])

include π in
/-- Every direction is avoided by one of any two distinct directions. -/
theorem exists_dir_ne (p : Dir) : ∃ q, q ≠ p := by
  obtain ⟨a, b, -, hab, -, -⟩ := π.exists_dir
  by_cases ha : a = p
  · exact ⟨b, fun hb => hab (ha.trans hb.symm)⟩
  · exact ⟨a, ha⟩

instance : Nondegenerate π.Points π.Lines where
  exists_point l := by
    induction l using lines_induction with
    | affineLine p x =>
      obtain ⟨q, hq⟩ := π.exists_dir_ne p
      exact ⟨π.dir q, by simpa using hq⟩
    | infinity =>
      obtain ⟨x⟩ := π.nonempty
      exact ⟨π.point x, point_notMem_infinity⟩
  exists_line pt := by
    induction pt using points_induction with
    | point x => exact ⟨π.infinity, point_notMem_infinity⟩
    | dir p =>
      obtain ⟨q, hq⟩ := π.exists_dir_ne p
      obtain ⟨x⟩ := π.nonempty
      exact ⟨π.affineLine q x, by simpa using hq.symm⟩
  eq_or_eq := π.eq_or_eq

/-- The projective completion of an affine plane presented by its directions. -/
noncomputable instance : ProjectivePlane π.Points π.Lines where
  mkPoint {l₁ l₂} _ := (π.exists_point_mem l₁ l₂).choose
  mkPoint_ax {l₁ l₂} _ := (π.exists_point_mem l₁ l₂).choose_spec
  mkLine h := (π.exists_line_mem _ _ h).choose
  mkLine_ax h := (π.exists_line_mem _ _ h).choose_spec
  exists_config := by
    obtain ⟨a, b, c, hab, hbc, hac⟩ := π.exists_dir
    obtain ⟨x⟩ := π.nonempty
    obtain ⟨y, hy⟩ := π.exists_rel b x
    refine ⟨π.point y, π.dir a, π.dir b, π.affineLine c x, π.infinity, π.affineLine a x,
      point_notMem_infinity, ?_, by simpa using hac, dir_mem_infinity, by simp,
      by simpa using hbc, dir_mem_infinity, by simpa using hab.symm⟩
    rw [point_mem_affineLine]
    rintro (rfl | hyx)
    · exact π.irrefl hy
    · exact hab (π.eq_of_rel (π.symm hyx) hy)

/-- The points on the line at infinity are the directions. -/
def infinityEquiv : {pt : π.Points // pt ∈ π.infinity} ≃ Dir where
  toFun pt :=
    match pt with
    | ⟨.inr p, _⟩ => p
    | ⟨.inl _, h⟩ => h.elim
  invFun p := ⟨π.dir p, dir_mem_infinity⟩
  left_inv pt :=
    match pt with
    | ⟨.inr _, _⟩ => rfl
    | ⟨.inl _, h⟩ => h.elim
  right_inv _ := rfl

section Finite

open scoped Classical in
/-- The direction of the line through two points, or `none` if the points agree. -/
private noncomputable def dirOf (o y : D) : Option Dir :=
  if h : o = y then none else some (π.exists_rel_of_ne h).choose

private theorem eq_or_rel_of_dirOf_eq {o y y' : D} (h : π.dirOf o y = π.dirOf o y') :
    y = y' ∨ ∃ p, π.rel p o y ∧ π.rel p o y' := by
  by_cases hy : o = y
  · by_cases hy' : o = y'
    · exact .inl (hy.symm.trans hy')
    · rw [dirOf, dirOf, dite_eq_left hy, dite_eq_right hy'] at h
      exact absurd h (Option.some_ne_none _).symm
  · by_cases hy' : o = y'
    · rw [dirOf, dirOf, dite_eq_right hy, dite_eq_left hy'] at h
      exact absurd h (Option.some_ne_none _)
    · rw [dirOf, dirOf, dite_eq_right hy, dite_eq_right hy', Option.some.injEq] at h
      exact .inr ⟨_, (π.exists_rel_of_ne hy).choose_spec, h ▸ (π.exists_rel_of_ne hy').choose_spec⟩

include π in
/-- An affine plane with finitely many directions has finitely many points: a point is determined
by the directions in which it is seen from three points that are not collinear. -/
theorem finite [Finite Dir] : Finite D := by
  obtain ⟨a, b, -, hab, -, -⟩ := π.exists_dir
  obtain ⟨o₁⟩ := π.nonempty
  obtain ⟨o₂, h₂⟩ := π.exists_rel a o₁
  obtain ⟨o₃, h₃⟩ := π.exists_rel b o₁
  refine Finite.of_injective (fun y => (π.dirOf o₁ y, π.dirOf o₂ y, π.dirOf o₃ y)) ?_
  intro y y' h
  rw [Prod.mk.injEq, Prod.mk.injEq] at h
  by_contra hne
  obtain ⟨p₁, h₁y, h₁y'⟩ := (π.eq_or_rel_of_dirOf_eq h.1).resolve_left hne
  obtain ⟨p₂, h₂y, h₂y'⟩ := (π.eq_or_rel_of_dirOf_eq h.2.1).resolve_left hne
  obtain ⟨p₃, h₃y, h₃y'⟩ := (π.eq_or_rel_of_dirOf_eq h.2.2).resolve_left hne
  have hp₁ := (π.trans (π.symm h₁y) h₁y').resolve_left hne
  obtain rfl := π.eq_of_rel hp₁ ((π.trans (π.symm h₂y) h₂y').resolve_left hne)
  obtain rfl := π.eq_of_rel hp₁ ((π.trans (π.symm h₃y) h₃y').resolve_left hne)
  have h₁₂ : π.rel p₁ o₁ o₂ :=
    (π.trans h₁y (π.symm h₂y)).resolve_left fun h => π.irrefl (h ▸ h₂)
  have h₁₃ : π.rel p₁ o₁ o₃ :=
    (π.trans h₁y (π.symm h₃y)).resolve_left fun h => π.irrefl (h ▸ h₃)
  exact hab ((π.eq_of_rel h₂ h₁₂).trans (π.eq_of_rel h₁₃ h₃))

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

end Parallelism

end Cslib
