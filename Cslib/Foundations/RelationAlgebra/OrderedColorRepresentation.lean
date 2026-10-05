/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.FiniteRepresentation
public import Mathlib.NumberTheory.Real.Irrational

/-!
# Representations on a dense order with finitely many dense colors

The real numbers `q + i * sqrt 2`, for rational `q` and a finite color `i`, give
disjoint dense color classes. A finite table assigning symmetric atoms to the colors
of increasing pairs specifies a representation when its composition certificates hold.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.OrderedColorRepresentation

variable {j n : ℕ}

/-- A point consists of a rational coordinate and a finite color. -/
abbrev Base (n : ℕ) := ℚ × Fin n

/-- Disjoint rational translates of multiples of an irrational number. -/
noncomputable def position (x : Base n) : ℝ := x.1 + x.2.val * Real.sqrt 2

theorem position_injective : Function.Injective (@position n) := by
  rintro ⟨q, i⟩ ⟨r, l⟩ h
  dsimp only [position] at h
  have hi : i = l := by
    by_contra hne
    have hrat : (i.val : ℚ) - l.val ≠ 0 := by
      simp only [sub_ne_zero]
      exact_mod_cast (Fin.val_ne_of_ne hne)
    have hirr := (irrational_sqrt_two.ratCast_mul hrat).ne_rat (r - q)
    apply hirr
    push_cast
    nlinarith
  subst l
  have hqr : q = r := Rat.cast_injective (show (q : ℝ) = (r : ℝ) by linarith)
  subst r
  rfl

/-- Every color meets every nonempty open interval. -/
theorem exists_between (i : Fin n) {l r : ℝ} (h : l < r) :
    ∃ x : Base n, x.2 = i ∧ l < position x ∧ position x < r := by
  obtain ⟨q, hq, hq'⟩ := exists_rat_btwn (sub_lt_sub_right h (i.val * Real.sqrt 2))
  exact ⟨(q, i), rfl, by dsimp [position]; linarith, by dsimp [position]; linarith⟩

/-- Every color occurs below any given point. -/
theorem exists_below (i : Fin n) (r : ℝ) : ∃ x : Base n, x.2 = i ∧ position x < r := by
  obtain ⟨x, hx, _, hr⟩ := exists_between i (show r - 1 < r by linarith)
  exact ⟨x, hx, hr⟩

/-- Every color occurs above any given point. -/
theorem exists_above (i : Fin n) (l : ℝ) : ∃ x : Base n, x.2 = i ∧ l < position x := by
  obtain ⟨x, hx, hl, _⟩ := exists_between i (show l < l + 1 by linarith)
  exact ⟨x, hx, hl⟩

/-- Regard a symmetric diversity atom index as an atom. -/
def atom (a : Fin j) : Atom j 0 := some (.inl a)

@[simp] theorem converse_eq (a : Atom j 0) : Atom.converse a = a := by
  cases a with
  | none => rfl
  | some a =>
    cases a with
    | inl a => rfl
    | inr a => exact Fin.elim0 a.1

/-- A finite color table and its composition certificates. -/
structure Policy (T : IntegralCycleTable j 0) (n : ℕ) where
  /-- There is at least one color. -/
  positive : 0 < n
  /-- The label on an increasing pair with these two colors. -/
  up : Fin n → Fin n → Fin j
  /-- Witnesses for a diagonal edge lie on either side or at its endpoint. -/
  diagonal (i : Fin n) (a b : Atom j 0) :
    cycleClosure T.cycles a b none ↔
      (a = none ∧ b = none) ∨ ∃ l,
        (atom (up l i) = a ∧ atom (up l i) = b) ∨
        (atom (up i l) = a ∧ atom (up i l) = b)
  /-- Witnesses for an increasing edge lie in one of its three intervals or at an endpoint. -/
  increasing (i l : Fin n) (a b : Atom j 0) :
    cycleClosure T.cycles a b (atom (up i l)) ↔
      (a = none ∧ b = atom (up i l)) ∨ (a = atom (up i l) ∧ b = none) ∨ ∃ m,
        (atom (up m i) = a ∧ atom (up m l) = b) ∨
        (atom (up i m) = a ∧ atom (up m l) = b) ∨
        (atom (up i m) = a ∧ atom (up l m) = b)

namespace Policy

variable {T : IntegralCycleTable j 0} (P : Policy T n)

/-- Symmetric edge labels read the colors from left to right. -/
noncomputable def label (x y : Base n) : Atom j 0 :=
  if position x < position y then atom (P.up x.2 y.2)
  else if position y < position x then atom (P.up y.2 x.2) else none

@[simp] theorem label_self (x : Base n) : P.label x x = none := by simp [label]

theorem label_of_lt {x y : Base n} (h : position x < position y) :
    P.label x y = atom (P.up x.2 y.2) := by simp [label, h]

theorem label_comm (x y : Base n) : P.label x y = P.label y x := by
  rcases lt_trichotomy (position x) (position y) with h | h | h
  · simp [label, h, not_lt_of_gt h]
  · simp [label, h]
  · simp [label, h, not_lt_of_gt h]

theorem label_of_gt {x y : Base n} (h : position y < position x) :
    P.label x y = atom (P.up y.2 x.2) := by
  rw [P.label_comm]
  exact P.label_of_lt h

@[simp] theorem label_eq_none (x y : Base n) : P.label x y = none ↔ x = y := by
  by_cases h : x = y
  · simp [h]
  · have h' := position_injective.ne h
    rcases lt_or_gt_of_ne h' with h' | h' <;>
      simp [label, atom, h', not_lt_of_gt h', h]

theorem composition_diagonal (a b : Atom j 0) (x : Base n) :
    cycleClosure T.cycles a b (P.label x x) ↔ ∃ z, P.label x z = a ∧ P.label z x = b := by
  rw [P.label_self, P.diagonal]
  constructor
  · rintro (⟨rfl, rfl⟩ | ⟨i, h | h⟩)
    · exact ⟨x, P.label_self x, P.label_self x⟩
    · obtain ⟨z, hz, hzx⟩ := exists_below i (position x)
      exact ⟨z, by rw [P.label_of_gt hzx, hz]; exact h.1,
        by rw [P.label_of_lt hzx, hz]; exact h.2⟩
    · obtain ⟨z, hz, hxz⟩ := exists_above i (position x)
      exact ⟨z, by rw [P.label_of_lt hxz, hz]; exact h.1,
        by rw [P.label_of_gt hxz, hz]; exact h.2⟩
  · rintro ⟨z, ha, hb⟩
    rcases lt_trichotomy (position z) (position x) with h | h | h
    · exact Or.inr ⟨z.2, Or.inl ⟨(P.label_of_gt h).symm.trans ha,
        (P.label_of_lt h).symm.trans hb⟩⟩
    · have hz := position_injective h
      subst z
      exact Or.inl ⟨ha.symm.trans (P.label_self x), hb.symm.trans (P.label_self x)⟩
    · exact Or.inr ⟨z.2, Or.inr ⟨(P.label_of_lt h).symm.trans ha,
        (P.label_of_gt h).symm.trans hb⟩⟩

theorem composition_increasing (a b : Atom j 0) {x y : Base n}
    (hxy : position x < position y) :
    cycleClosure T.cycles a b (P.label x y) ↔ ∃ z, P.label x z = a ∧ P.label z y = b := by
  rw [P.label_of_lt hxy, P.increasing]
  constructor
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨i, h | h | h⟩)
    · exact ⟨x, P.label_self x, P.label_of_lt hxy⟩
    · exact ⟨y, P.label_of_lt hxy, P.label_self y⟩
    · obtain ⟨z, hz, hzx⟩ := exists_below i (position x)
      exact ⟨z, by rw [P.label_of_gt hzx, hz]; exact h.1,
        by rw [P.label_of_lt (hzx.trans hxy), hz]; exact h.2⟩
    · obtain ⟨z, hz, hxz, hzy⟩ := exists_between i hxy
      exact ⟨z, by rw [P.label_of_lt hxz, hz]; exact h.1,
        by rw [P.label_of_lt hzy, hz]; exact h.2⟩
    · obtain ⟨z, hz, hyz⟩ := exists_above i (position y)
      exact ⟨z, by rw [P.label_of_lt (hxy.trans hyz), hz]; exact h.1,
        by rw [P.label_of_gt hyz, hz]; exact h.2⟩
  · rintro ⟨z, ha, hb⟩
    rcases lt_trichotomy (position z) (position x) with hzx | hzx | hxz
    · exact Or.inr (Or.inr ⟨z.2, Or.inl ⟨(P.label_of_gt hzx).symm.trans ha,
        (P.label_of_lt (hzx.trans hxy)).symm.trans hb⟩⟩)
    · have hz := position_injective hzx
      subst z
      exact Or.inl ⟨ha.symm.trans (P.label_self x), hb.symm.trans (P.label_of_lt hxy)⟩
    · rcases lt_trichotomy (position z) (position y) with hzy | hzy | hyz
      · exact Or.inr (Or.inr ⟨z.2, Or.inr (Or.inl
          ⟨(P.label_of_lt hxz).symm.trans ha, (P.label_of_lt hzy).symm.trans hb⟩)⟩)
      · have hz := position_injective hzy
        subst z
        exact Or.inr (Or.inl
          ⟨ha.symm.trans (P.label_of_lt hxy), hb.symm.trans (P.label_self y)⟩)
      · exact Or.inr (Or.inr ⟨z.2, Or.inr (Or.inr
          ⟨(P.label_of_lt hxz).symm.trans ha, (P.label_of_gt hyz).symm.trans hb⟩)⟩)

theorem composition (a b : Atom j 0) (x y : Base n) :
    cycleClosure T.cycles a b (P.label x y) ↔ ∃ z, P.label x z = a ∧ P.label z y = b := by
  rcases lt_trichotomy (position x) (position y) with h | h | h
  · exact P.composition_increasing a b h
  · have hxy := position_injective h
    subst y
    exact P.composition_diagonal a b x
  · constructor
    · intro hc
      have hc' : cycleClosure T.cycles b a (P.label y x) := by
        simpa only [converse_eq, P.label_comm x y] using cycleClosure_converse hc
      obtain ⟨z, hz, hz'⟩ := (P.composition_increasing b a h).mp hc'
      exact ⟨z, (P.label_comm x z).trans hz', (P.label_comm z y).trans hz⟩
    · rintro ⟨z, hz, hz'⟩
      have hc := (P.composition_increasing b a h).mpr
        ⟨z, (P.label_comm y z).trans hz', (P.label_comm z x).trans hz⟩
      simpa only [converse_eq, P.label_comm y x] using cycleClosure_converse hc

/-- The atomic representation specified by an ordered color policy. -/
noncomputable def toAtomRepresentation : AtomRepresentation T (Base n) where
  label := P.label
  surjective a := by
    let x : Base n := (0, ⟨0, P.positive⟩)
    have hc : cycleClosure T.cycles a a (P.label x x) := by
      rw [P.label_self]
      exact Or.inr (Or.inr (Or.inl ⟨rfl, (converse_eq a).symm⟩))
    obtain ⟨z, hz, _⟩ := (P.composition a a x x).mp hc
    exact ⟨(x, z), hz⟩
  identity := P.label_eq_none
  converse x y := by rw [converse_eq, P.label_comm]
  composition := P.composition

/-- Finite color certificates yield a representation on a countable dense order. -/
theorem representable (P : Policy T n) : Representable (Complex T) :=
  AtomRepresentation.representable P.toAtomRepresentation

end Policy

end Cslib.RelationAlgebra.OrderedColorRepresentation
