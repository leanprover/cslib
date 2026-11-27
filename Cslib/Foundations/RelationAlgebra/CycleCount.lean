/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.AtomStructure
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-!
# Counting diversity cycles

A directed triangle with edges labelled `a, b, c` represents the cycle `(a, b, conv c)`.
Rotation preserves the direction of the edges. Reflection reverses all three.
Burnside's lemma counts the resulting orbits of triples.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.AtomStructure

variable {α : Type*}

/-- The three edge labels of a directed triangle with converse operation `f`. -/
@[ext] structure Triangle (f : α → α) where
  /-- The edges in cyclic order. -/
  edge : ZMod 3 → α

namespace Triangle

variable {f : α → α}

instance [Finite α] : Finite (Triangle f) := Finite.of_injective edge fun _ _ => Triangle.ext

/-- Reorient the edges of a triangle. -/
def act (f : α → α) : DihedralGroup 3 → Triangle f → Triangle f
  | .r i, t => ⟨fun j => t.edge (j + i)⟩
  | .sr i, t => ⟨fun j => f (t.edge (i - j))⟩

/-- Rotations and reflections act on oriented edge labels. -/
@[instance_reducible]
def action (hf : Function.Involutive f) : MulAction (DihedralGroup 3) (Triangle f) where
  smul := act f
  one_smul t := by ext j; change t.edge (j + 0) = _; rw [add_zero]
  mul_smul := by
    intro g h t
    change act f (g * h) t = act f g (act f h t)
    rcases g with i | i <;> rcases h with j | j <;> ext k <;>
      simp [act, hf _, add_comm, add_left_comm, add_assoc, sub_eq_add_neg]

/-- Orbits of labelled triangles under rotations and reflections. -/
def Orbit (hf : Function.Involutive f) :=
  letI := action hf
  MulAction.orbitRel.Quotient (DihedralGroup 3) (Triangle f)

instance [Finite α] (hf : Function.Involutive f) : Finite (Orbit hf) :=
  letI := action hf
  inferInstanceAs (Finite (MulAction.orbitRel.Quotient (DihedralGroup 3) (Triangle f)))

private theorem card_rotation (hf : Function.Involutive f) [Finite α] (i : ZMod 3) (hi : i ≠ 0) :
    letI := action hf
    Nat.card (MulAction.fixedBy (Triangle f) (DihedralGroup.r i)) ≤ Nat.card α := by
  let _ := action hf
  apply Nat.card_le_card_of_injective (fun t => t.val.edge 0)
  intro x y he
  have hx (j : ZMod 3) : x.val.edge (j + i) = x.val.edge j := congrArg (fun t => t.edge j) x.prop
  have hy (j : ZMod 3) : y.val.edge (j + i) = y.val.edge j := congrArg (fun t => t.edge j) y.prop
  apply Subtype.ext
  ext j
  have h₁ := (hx 0).trans (he.trans (hy 0).symm)
  have h₂ := (hx i).trans (show x.val.edge i = y.val.edge i by simpa using h₁)
  have h₃ := h₂.trans (hy i).symm
  fin_cases i <;> fin_cases j <;> first | contradiction | exact he | exact h₁ | exact h₃

private theorem card_reflection (hf : Function.Involutive f) [Finite α] (i : ZMod 3) :
    letI := action hf
    Nat.card (MulAction.fixedBy (Triangle f) (DihedralGroup.sr i)) ≤ Nat.card α ^ 2 := by
  let _ := action hf
  rw [pow_two, ← Nat.card_prod]
  -- A reflection interchanges two positions and fixes the third. Keep the fixed position
  -- and one member of the interchanged pair.
  let j : ZMod 3 := if i = 1 then 2 else 1
  apply Nat.card_le_card_of_injective (fun t => (t.val.edge 0, t.val.edge j))
  intro x y he
  have hx (k : ZMod 3) : f (x.val.edge (i - k)) = x.val.edge k :=
    congrArg (fun t => t.edge k) x.prop
  have hy (k : ZMod 3) : f (y.val.edge (i - k)) = y.val.edge k :=
    congrArg (fun t => t.edge k) y.prop
  have h₀ : x.val.edge 0 = y.val.edge 0 := congrArg Prod.fst he
  have h₁ : x.val.edge j = y.val.edge j := congrArg Prod.snd he
  have flip (u v : ZMod 3) (h : x.val.edge v = y.val.edge v) (huv : i - u = v) :
      x.val.edge u = y.val.edge u := by
    rw [← hx u, ← hy u, huv, h]
  apply Subtype.ext
  ext k
  fin_cases i <;> fin_cases k <;> first
    | exact h₀
    | exact h₁
    | exact flip _ _ h₀ (by decide)
    | exact flip _ _ h₁ (by decide)

/-- The identity rotation fixes every triangle, each other rotation fixes at most `d`
triangles, and each reflection fixes at most `d²`, where `d` is the number of labels. -/
theorem six_mul_card_orbit_le (hf : Function.Involutive f) [Finite α] :
    6 * Nat.card (Orbit hf) ≤ Nat.card α ^ 3 + 3 * Nat.card α ^ 2 + 2 * Nat.card α := by
  classical
  let _ := action hf
  let _ := Fintype.ofFinite α
  let _ := Fintype.ofFinite (Triangle f)
  let c (g : DihedralGroup 3) := Fintype.card (MulAction.fixedBy (Triangle f) g)
  have hc : ∑ g, c g = Nat.card (Orbit hf) * 6 := by
    rw [MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group]
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, DihedralGroup.nat_card]
    rfl
  have h₀ : c (.r 0) ≤ Nat.card α ^ 3 := by
    have h := Nat.card_le_card_of_injective (fun t : MulAction.fixedBy (Triangle f)
      (DihedralGroup.r (0 : ZMod 3)) => t.val.edge) fun _ _ h => Subtype.ext (Triangle.ext h)
    simpa [c, Nat.card_fun, Nat.card_eq_fintype_card] using h
  have hr (i : ZMod 3) (hi : i ≠ 0) : c (.r i) ≤ Nat.card α := by
    simpa only [c, ← Nat.card_eq_fintype_card] using card_rotation hf i hi
  have hs (i : ZMod 3) : c (.sr i) ≤ Nat.card α ^ 2 := by
    simpa only [c, ← Nat.card_eq_fintype_card] using card_reflection hf i
  have hu : (Finset.univ : Finset (DihedralGroup 3)) =
      {.r 0, .r 1, .r 2, .sr 0, .sr 1, .sr 2} := by decide
  rw [hu] at hc
  simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton] at hc
  have := hr 1 (by decide)
  have := hr 2 (by decide)
  have := hs 0
  have := hs 1
  have := hs 2
  omega

/-- The number of cycle orbits is at most the number of unordered triples with repetitions. -/
theorem card_orbit_le_choose (hf : Function.Involutive f) [Finite α] :
    Nat.card (Orbit hf) ≤ (Nat.card α + 2).choose 3 := by
  let d := Nat.card α
  have h₁ := Nat.add_one_mul_choose_eq d 1
  have h₂ := Nat.add_one_mul_choose_eq (d + 1) 2
  simp only [Nat.choose_one_right] at h₁
  have h := six_mul_card_orbit_le hf
  change 6 * _ ≤ d ^ 3 + 3 * d ^ 2 + 2 * d at h
  change _ ≤ (d + 2).choose 3
  nlinarith [congrArg (fun n => (d + 2) * n) h₁]

end Triangle

variable (A : AtomStructure α) [LawfulAtomStructure A]

/-- Membership of a triangle in the cycle table is constant on its dihedral orbit. -/
theorem cycle_triangle_act (t : Triangle A.conv) (g : DihedralGroup 3) :
    let u := Triangle.act A.conv g t
    (t.edge 0, t.edge 1, A.conv (t.edge 2)) ∈ A.cycles →
      (u.edge 0, u.edge 1, A.conv (u.edge 2)) ∈ A.cycles := by
  intro u h
  have rot {a b c : α} (h : (a, b, A.conv c) ∈ A.cycles) :
      (c, a, A.conv b) ∈ A.cycles := by simpa using A.conv_cycles (A.cycle_left h)
  have refl {a b c : α} (h : (a, b, A.conv c) ∈ A.cycles) :
      (A.conv a, A.conv c, b) ∈ A.cycles := A.cycle_left h
  have r₁ := rot h
  have r₂ := rot r₁
  have z₁ : (0 : ZMod 3) - 1 = 2 := by decide
  have z₂ : (0 : ZMod 3) - 2 = 1 := by decide
  have z₃ : (1 : ZMod 3) - 2 = 2 := by decide
  have z₄ : (2 : ZMod 3) - 1 = 1 := by decide
  have cases₃ : ∀ i : ZMod 3, i = 0 ∨ i = 1 ∨ i = 2 := by decide
  rcases g with i | i <;> rcases cases₃ i with rfl | rfl | rfl <;>
    dsimp only [u, Triangle.act] <;>
    try simp only [sub_zero, sub_self, z₁, z₂, z₃, z₄, A.conv_conv]
  all_goals first
    | exact h | exact r₁ | exact r₂
    | exact refl h | exact refl r₁ | exact refl r₂

/-- An atom has a unique right identity atom. -/
theorem existsUnique_id_cycle_right (a : α) : ∃! e, e ∈ A.id ∧ (a, e, a) ∈ A.cycles := by
  obtain ⟨e, he, ha⟩ := A.exists_id_cycle_right a
  refine ⟨e, ⟨he, ha⟩, fun f ⟨hf, hb⟩ => ?_⟩
  obtain ⟨u, _, hu⟩ := A.assoc_symm ha hb
  exact (A.id_cycle_right he hu).symm.trans (A.id_cycle_left hf hu)

/-- The right identity atom of an atom. -/
noncomputable def rightId (a : α) : α := (A.existsUnique_id_cycle_right a).choose

theorem rightId_spec (a : α) : A.rightId a ∈ A.id ∧ (a, A.rightId a, a) ∈ A.cycles :=
  (A.existsUnique_id_cycle_right a).choose_spec.1

theorem cycle_id_right_iff {a e b : α} (he : e ∈ A.id) :
    (a, e, b) ∈ A.cycles ↔ b = a ∧ A.rightId a = e := by
  refine ⟨fun h => ?_, ?_⟩
  · obtain rfl := A.id_cycle_right he h
    exact ⟨rfl, ((A.existsUnique_id_cycle_right _).choose_spec.2 e ⟨he, h⟩).symm⟩
  · rintro ⟨rfl, rfl⟩
    exact (A.rightId_spec _).2

/-- The cycle predicate on a collection of labels closed under converse. -/
def orbitCycles {β : Type*} {f : β → β} (hf : Function.Involutive f) (j : β → α)
    (hj : ∀ x, j (f x) = A.conv (j x)) : Set (Triangle.Orbit hf) := by
  let _ := Triangle.action hf
  let P (t : Triangle f) := (j (t.edge 0), j (t.edge 1), A.conv (j (t.edge 2))) ∈ A.cycles
  have hP (g : DihedralGroup 3) (t : Triangle f) (h : P t) : P (g • t) := by
    have ha := A.cycle_triangle_act ⟨j ∘ t.edge⟩ g h
    cases g with
    | r i => exact ha
    | sr i =>
      change (j (f _), j (f _), A.conv (j (f _))) ∈ A.cycles
      simpa only [hj, Triangle.act, Function.comp_apply] using ha
  refine {q : MulAction.orbitRel.Quotient (DihedralGroup 3) (Triangle f) |
    Quotient.liftOn q P fun x y ⟨g, hg⟩ => propext ?_}
  subst x
  exact ⟨fun h => by simpa using hP g⁻¹ _ h, hP g y⟩

/-- The identity cycles are determined by the converse, identity set and right identities. -/
theorem ext_of_diversity {B : AtomStructure α} [LawfulAtomStructure B]
    (hf : A.conv = B.conv) (hi : A.id = B.id) (hr : A.rightId = B.rightId)
    (hd : ∀ x ∉ A.id, ∀ y ∉ A.id, ∀ z ∉ A.id,
      (x, y, z) ∈ A.cycles ↔ (x, y, z) ∈ B.cycles) : A = B := by
  apply AtomStructure.ext hf hi
  ext ⟨x, y, z⟩
  have mid {x y z : α} (hy : y ∈ A.id) : (x, y, z) ∈ A.cycles ↔ (x, y, z) ∈ B.cycles := by
    rw [A.cycle_id_right_iff hy, B.cycle_id_right_iff (hi ▸ hy), hr]
  have left (C : AtomStructure α) [LawfulAtomStructure C] {r s t : α} :
      (r, s, t) ∈ C.cycles ↔ (C.conv r, t, s) ∈ C.cycles :=
    ⟨C.cycle_left, fun h => by simpa using C.cycle_left h⟩
  have rev (C : AtomStructure α) [LawfulAtomStructure C] {r s t : α} :
      (r, s, t) ∈ C.cycles ↔ (C.conv s, C.conv r, C.conv t) ∈ C.cycles :=
    ⟨C.conv_cycles, fun h => by simpa using C.conv_cycles h⟩
  by_cases hy : y ∈ A.id
  · exact mid hy
  by_cases hx : x ∈ A.id
  · rw [rev A, rev B, ← hf, A.conv_eq_self_of_mem_id hx]
    exact mid hx
  by_cases hz : z ∈ A.id
  · rw [left A, left B, ← hf]
    exact mid hz
  exact hd x hx y hy z hz

end Cslib.RelationAlgebra.AtomStructure
