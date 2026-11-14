/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.Combinatorics.ProjectivePlane.Completion
public import Cslib.Foundations.RelationAlgebra.Lyndon.Representation
public import Mathlib.Data.Fintype.Option

/-!
# Representable Lyndon algebras and projective planes

A representation of the Lyndon algebra `𝔄(α, e)` on a set `D` that sends the atoms to relations
covering `D × D` makes `D` into an affine plane whose directions are the points `α \ {e}`: the
relation representing a point `p` relates the pairs of distinct points lying on a common line of
direction `p`. Completing this affine plane gives a projective plane in which `α \ {e}` is the
line at infinity. This is the argument of [Lyndon1961].

Every representation of a finite Lyndon algebra has this covering property, because the unit is
then a finite join of atoms. Representations of an infinite Lyndon algebra need not preserve this
join, which is why the statements below are restricted to finite Lyndon algebras.

## Main statements

* `Cslib.RelationAlgebra.exists_projectivePlane_of_representation`: Theorem D of [Monk1964] for
  finite Lyndon algebras, for representations in arbitrary universes.
* `Cslib.RelationAlgebra.exists_projectivePlane_order_of_representation`: the same, phrased in
  terms of the order of the plane.

## References

* [R. C. Lyndon, *Relation algebras and projective geometries*][Lyndon1961]
* [J. D. Monk, *On representable relation algebras*][Monk1964]

-/

@[expose] public section

universe u v w

namespace Cslib.RelationAlgebra

open AtomStructure ComplexAlgebra Configuration

/-- A homomorphism from a complex algebra with finitely many atoms into an algebra of relations
sends the atoms to relations that cover all pairs. -/
theorem ComplexAlgebra.exists_mem_map_atom {α D : Type*} [Finite α] {A : AtomStructure α}
    (g : RelationAlgebraHom (ComplexAlgebra A) (SquareRelations D)) (x y : D) :
    ∃ a, (x, y) ∈ g (atom A a) := by
  by_contra hcon
  have hall : ∀ s : Set α, s.Finite → (x, y) ∉ g ⟨s⟩ := fun s hs => by
    induction s, hs using Set.Finite.induction_on with
    | empty =>
      have h : (⟨∅⟩ : ComplexAlgebra A) = ⊥ := rfl
      rw [h, map_bot]
      exact SquareRelations.notMem_bot
    | @insert a s _ _ ih =>
      have h : (⟨insert a s⟩ : ComplexAlgebra A) = atom A a ⊔ ⟨s⟩ := rfl
      rw [h, map_sup, SquareRelations.mem_sup]
      exact fun h => h.elim (fun h => hcon ⟨a, h⟩) ih
  have h : (⟨Set.univ⟩ : ComplexAlgebra A) = ⊤ := rfl
  exact hall Set.univ Set.finite_univ (by rw [h, map_top]; exact SquareRelations.mem_top)

namespace Lyndon

variable {α : Type u} {e : α} {h : 5 ≤ ENat.card α}

theorem atom_eq_one : atom (lyndon e h) e = 1 := rfl

theorem atom_mul_atom_self {p : α} (hp : p ≠ e) :
    atom (lyndon e h) p * atom (lyndon e h) p = atom (lyndon e h) p ⊔ 1 := by
  ext c
  rw [mem_atom_mul_atom, lyndon_cycles, mem_lyndonCycles, mem_sup, mem_atom, mem_one, lyndon_id,
    Set.mem_singleton_iff]
  grind

theorem atom_le_atom_mul_atom {p q r : α} (hpq : p ≠ q) (hqr : q ≠ r) (hpr : p ≠ r)
    (hp : p ≠ e) (hq : q ≠ e) (hr : r ≠ e) :
    atom (lyndon e h) r ≤ atom (lyndon e h) p * atom (lyndon e h) q := by
  rw [atom_le_iff, mem_atom_mul_atom]
  exact .inr <| .inr <| .inr <| .inr ⟨hpq, hqr, hpr, hp, hq, hr⟩

variable (e h) in
include h in
/-- A Lyndon algebra has at least three points. -/
theorem exists_three_ne : ∃ a b c : {a // a ≠ e}, a ≠ b ∧ b ≠ c ∧ a ≠ c := by
  obtain ⟨a, ha, -⟩ := ENat.exists_ne_of_five_le_card h e e e e
  obtain ⟨b, hb, hba, -⟩ := ENat.exists_ne_of_five_le_card h e a a a
  obtain ⟨c, hc, hca, hcb, -⟩ := ENat.exists_ne_of_five_le_card h e a b b
  exact ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, fun hab => hba (congrArg Subtype.val hab).symm,
    fun hbc => hcb (congrArg Subtype.val hbc).symm,
    fun hac => hca (congrArg Subtype.val hac).symm⟩

variable {D : Type w} [Finite α] [Nonempty D]

/-- A representation of a finite Lyndon algebra on a nonempty set makes the set into an affine
plane whose directions are the points of the Lyndon algebra. -/
def parallelism (g : RelationAlgebraHom (ComplexAlgebra (lyndon e h)) (SquareRelations D)) :
    Parallelism D {a // a ≠ e} where
  rel p x y := (x, y) ∈ g (atom _ p)
  symm {p x y} hxy := by
    have hstar := map_star g (atom (lyndon e h) p)
    rw [star_trivial] at hstar
    rw [hstar, SquareRelations.mem_star]
    exact hxy
  irrefl {p x} hx := by
    have hmem : (x, x) ∈ g (atom (lyndon e h) p ⊓ atom (lyndon e h) e) := by
      rw [map_inf, atom_eq_one, map_one]
      exact ⟨hx, rfl⟩
    rw [atom_inf_atom_of_ne p.property, map_bot] at hmem
    exact SquareRelations.notMem_bot hmem
  exists_rel_of_ne {x y} hxy := by
    obtain ⟨a, ha⟩ := exists_mem_map_atom g x y
    refine ⟨⟨a, ?_⟩, ha⟩
    rintro rfl
    rw [atom_eq_one, map_one] at ha
    exact hxy ha
  eq_of_rel {p q x y} hp hq := by
    by_contra hne
    have hmem : (x, y) ∈ g (atom (lyndon e h) p ⊓ atom (lyndon e h) q) := by
      rw [map_inf]
      exact ⟨hp, hq⟩
    rw [atom_inf_atom_of_ne (fun hpq => hne (Subtype.ext hpq)), map_bot] at hmem
    exact SquareRelations.notMem_bot hmem
  trans {p x y z} hxy hyz := by
    have hmem : (x, z) ∈ g (atom (lyndon e h) p * atom (lyndon e h) p) := by
      rw [map_mul]
      exact ⟨y, hxy, hyz⟩
    rw [atom_mul_atom_self p.property, map_sup, map_one] at hmem
    exact hmem.symm
  exists_rel p x := by
    have hmem : (x, x) ∈ g (atom (lyndon e h) p * atom (lyndon e h) p) := by
      rw [atom_mul_atom_self p.property, map_sup, map_one]
      exact .inr rfl
    rw [map_mul] at hmem
    obtain ⟨y, hxy, -⟩ := hmem
    exact ⟨y, hxy⟩
  exists_rel_rel {p q r x z} hpq hqr hpr hr := by
    have hle := OrderHomClass.mono g (atom_le_atom_mul_atom (h := h)
      (fun hpq' => hpq (Subtype.ext hpq')) (fun hqr' => hqr (Subtype.ext hqr'))
      (fun hpr' => hpr (Subtype.ext hpr')) p.property q.property r.property)
    rw [map_mul] at hle
    exact SquareRelations.le_def.mp hle x z hr
  nonempty := inferInstance
  exists_dir := exists_three_ne e h

end Lyndon

open Lyndon

variable {α : Type u} [Finite α] (e : α) (h : 5 ≤ ENat.card α)

omit [Finite α] in
/-- Every representation of a Lyndon algebra has a component on a nonempty set. -/
theorem exists_nonempty_of_representation {ι : Type v} {β : ι → Type w}
    (ρ : Representation (ComplexAlgebra (lyndon e h)) ι β) : ∃ i, Nonempty (β i) := by
  by_contra hcon
  have hempty : ∀ i, IsEmpty (β i) := fun i => not_nonempty_iff.mp fun hi => hcon ⟨i, hi⟩
  refine (isIntegral_lyndon (e := e) h).top_ne_bot (ρ.injective ?_)
  funext i
  ext x
  exact (hempty i).elim x

/-- **Theorem D** of [Monk1964] for finite Lyndon algebras: if the Lyndon algebra `𝔄(α, e)` has a
representation, then `α \ {e}` is a line of a projective plane. -/
theorem exists_projectivePlane_of_representation {ι : Type v} {β : ι → Type w}
    (ρ : Representation (ComplexAlgebra (lyndon e h)) ι β) :
    ∃ (P L : Type (max u w)) (_ : Membership P L) (_ : ProjectivePlane P L) (l : L),
      Nonempty ({a // a ≠ e} ≃ {p : P // p ∈ l}) := by
  obtain ⟨i, hi⟩ := exists_nonempty_of_representation e h ρ
  let π := parallelism ((RelationAlgebraHom.eval (fun i => SquareRelations (β i)) i).comp ρ.hom)
  exact ⟨π.Points, π.Lines, inferInstance, inferInstance, π.infinity, ⟨π.infinityEquiv.symm⟩⟩

/-- **Theorem D** of [Monk1964] for finite Lyndon algebras, in terms of orders: if the Lyndon
algebra with `n + 2` atoms has a representation, then there is a projective plane of order `n`. -/
theorem exists_projectivePlane_order_of_representation {ι : Type v} {β : ι → Type w}
    (ρ : Representation (ComplexAlgebra (lyndon e h)) ι β) :
    ∃ (P L : Type (max u w)) (_ : Membership P L) (_ : ProjectivePlane P L) (_ : Finite P)
      (_ : Finite L), ProjectivePlane.order P L + 2 = Nat.card α := by
  obtain ⟨i, hi⟩ := exists_nonempty_of_representation e h ρ
  let π := parallelism ((RelationAlgebraHom.eval (fun i => SquareRelations (β i)) i).comp ρ.hom)
  refine ⟨π.Points, π.Lines, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  classical
  have := Fintype.ofFinite {a // a ≠ e}
  have hcard : Nat.card α = Nat.card {a // a ≠ e} + 1 := by
    rw [← Nat.card_congr (Equiv.optionSubtypeNe e), Nat.card_eq_fintype_card,
      Fintype.card_option, Nat.card_eq_fintype_card]
  rw [hcard, ← π.order_add_one]

end Cslib.RelationAlgebra
