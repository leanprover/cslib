/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.Combinatorics.ProjectivePlane.Completion
public import Cslib.Foundations.RelationAlgebra.AtomStructure
public import Cslib.Foundations.RelationAlgebra.Group
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Set.Card
public import Mathlib.FieldTheory.Cardinality
public import Mathlib.Tactic.LinearCombination

/-!
# Lyndon algebras

Given a type `α` with a distinguished element `e`, Lyndon's construction makes `α` into an atom
structure in which `e` is the only identity atom, every atom is its own converse, and for
`p, q ≠ e`

* `p ; p = p + e`, and
* `p ; q` is the sum of all atoms other than `p`, `q` and `e` when `p ≠ q`.

This is an atom structure exactly when `α` has one, two, or at least five elements; we follow
[Monk1964] in requiring at least five. The complex algebra of this atom structure is the
*Lyndon algebra* `𝔄(α, e)`. Geometrically, `α \ {e}` is the set of points of a projective line
and `𝔄(α, e)` is the complex algebra of this one-dimensional geometry in the sense of
[Givant2017a], Section 3.6.

The terminology varies in the literature. In [Monk1964] the "Lyndon algebras" are the algebras
satisfying a list of axioms (composition is associative, commutative, additive and has `1'` as an
identity, converse is trivial, and `1' ≤ x ; y` if and only if `x · y ≠ 0`), which characterize the
integral relation algebras with trivial converse, and `𝔄(α, e)` is shown to be one of them. We
follow the modern usage, in which the name refers to the construction.

## Representations and projective planes

Following [Lyndon1961], representations of `𝔄(α, e)` correspond to projective planes having
`α \ {e}` as a line.

In one direction, if the points `α \ {e}` form the projective line `Option K` over a field `K`,
then `𝔄(α, e)` is representable over the additive group of the plane `K × K`: a point is sent to
the punctured line through the origin with the corresponding slope.

In the other direction, a representation of `𝔄(α, e)` on a set `D` that sends the atoms to
relations covering `D × D` makes `D` into an affine plane whose directions are the points
`α \ {e}`: the relation representing a point `p` relates the pairs of distinct points lying on a
common line of direction `p`. Completing this affine plane gives a projective plane in which
`α \ {e}` is the line at infinity. Every representation of a finite Lyndon algebra has this
covering property, because the unit is then a finite join of atoms. Representations of an infinite
Lyndon algebra need not preserve this join, which is why these statements are restricted to finite
Lyndon algebras.

## Ultraproducts

Lyndon's atom structure is defined from equality and the distinguished element alone, so an
ultraproduct of Lyndon atom structures is again a Lyndon atom structure. Consequently an
ultraproduct of Lyndon algebras embeds into a Lyndon algebra, and is representable over a group as
soon as the ultraproduct of the types of atoms is infinite. This is the positive half of the proof
of Theorem 1 of [Monk1964].

## Main definitions

* `Cslib.RelationAlgebra.lyndonCycles`: the cycles of Lyndon's atom structure.
* `Cslib.RelationAlgebra.AtomStructure.lyndon`: Lyndon's atom structure.

## Main statements

* `Cslib.RelationAlgebra.ComplexAlgebra.isIntegral_lyndon` and the `TrivialStar` instance:
  Theorem A of [Monk1964], that `𝔄(α, e)` is an integral relation algebra with trivial converse.
* `Cslib.RelationAlgebra.groupRepresentable_lyndon_of_field`: a Lyndon algebra whose points form
  the projective line over a field is representable over a group.
* `Cslib.RelationAlgebra.groupRepresentable_lyndon`: Theorem C of [Monk1964], that `𝔄(α, e)` is
  representable over a group when `α` is infinite.
* `Cslib.RelationAlgebra.exists_projectivePlane_of_representation`: Theorem D of [Monk1964] for
  finite Lyndon algebras, for representations in arbitrary universes.
* `Cslib.RelationAlgebra.exists_projectivePlane_order_of_representation`: the same, phrased in
  terms of the order of the plane.
* `Cslib.RelationAlgebra.groupRepresentable_product_lyndon`: an ultraproduct of Lyndon algebras is
  representable over a group when the ultraproduct of the types of atoms is infinite.

## References

* [R. C. Lyndon, *Relation algebras and projective geometries*][Lyndon1961]
* [J. D. Monk, *On representable relation algebras*][Monk1964]
* [Steven Givant, *Introduction to Relation Algebras*][Givant2017a]

-/

@[expose] public section

universe u v w

namespace Cslib.RelationAlgebra

/-! ### Lyndon's atom structure -/

section Basic

variable {α : Type*} {e r s t : α}

/-- The cycles of Lyndon's atom structure on a type with a distinguished element `e`: the triples
`(r, s, t)` such that one of the three is `e` and the other two agree, or all three agree, or
`r`, `s`, `t` and `e` are pairwise distinct. -/
def lyndonCycles (e : α) : Set (α × α × α) :=
  {(r, s, t) | r = e ∧ s = t ∨ s = e ∧ r = t ∨ t = e ∧ r = s ∨ r = s ∧ s = t ∨
    r ≠ s ∧ s ≠ t ∧ r ≠ t ∧ r ≠ e ∧ s ≠ e ∧ t ≠ e}

theorem mem_lyndonCycles : (r, s, t) ∈ lyndonCycles e ↔
    r = e ∧ s = t ∨ s = e ∧ r = t ∨ t = e ∧ r = s ∨ r = s ∧ s = t ∨
      r ≠ s ∧ s ≠ t ∧ r ≠ t ∧ r ≠ e ∧ s ≠ e ∧ t ≠ e := .rfl

/-- A type with at least five elements has an element distinct from any four given ones. -/
theorem _root_.ENat.exists_ne_of_five_le_card (h : 5 ≤ ENat.card α) (a b c d : α) :
    ∃ x, x ≠ a ∧ x ≠ b ∧ x ≠ c ∧ x ≠ d := by
  by_contra hcon
  have hsub : (Set.univ : Set α) ⊆ {a, b, c, d} := fun x _ => by
    by_contra hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hx
    exact hcon ⟨x, hx⟩
  have hle : ENat.card α ≤ 4 := by
    rw [← Set.encard_univ]
    calc (Set.univ : Set α).encard
      _ ≤ ({a, b, c, d} : Set α).encard := Set.encard_le_encard hsub
      _ ≤ ({b, c, d} : Set α).encard + 1 := Set.encard_insert_le _ _
      _ ≤ ({c, d} : Set α).encard + 1 + 1 := by gcongr; exact Set.encard_insert_le _ _
      _ ≤ ({d} : Set α).encard + 1 + 1 + 1 := by gcongr; exact Set.encard_insert_le _ _
      _ = 4 := by rw [Set.encard_singleton]; rfl
  exact absurd (h.trans hle) (by decide)

/-- Lyndon's cycles are associative on a type with at least five elements. -/
theorem lyndonCycles_assoc (h : 5 ≤ ENat.card α) {r q p s t : α}
    (h₁ : (r, q, p) ∈ lyndonCycles e) (h₂ : (s, t, q) ∈ lyndonCycles e) :
    ∃ q', (q', t, p) ∈ lyndonCycles e ∧ (r, s, q') ∈ lyndonCycles e := by
  obtain ⟨x, hx⟩ := ENat.exists_ne_of_five_le_card h e r s t
  obtain ⟨y, hy⟩ := ENat.exists_ne_of_five_le_card h e r p s
  simp only [mem_lyndonCycles] at h₁ h₂ ⊢
  by_contra hcon
  have he := not_exists.mp hcon e
  have hr := not_exists.mp hcon r
  have hs := not_exists.mp hcon s
  have ht := not_exists.mp hcon t
  have hp := not_exists.mp hcon p
  have hq := not_exists.mp hcon q
  have hx' := not_exists.mp hcon x
  have hy' := not_exists.mp hcon y
  grind (splits := 40)

namespace AtomStructure

/-- Lyndon's atom structure on a type with at least five elements and a distinguished element `e`,
denoted `𝔄(α, e)` in [Monk1964]. -/
def lyndon (e : α) (h : 5 ≤ ENat.card α) : AtomStructure α where
  conv a := a
  id := {e}
  cycles := lyndonCycles e
  assoc := lyndonCycles_assoc h
  id_cycle_right {s r p} (hs : s = e) hc := by
    rw [mem_lyndonCycles] at hc
    grind
  exists_id_cycle_right r := ⟨e, rfl, .inr (.inl ⟨rfl, rfl⟩)⟩
  cycle_left {r s t} hc := by
    rw [mem_lyndonCycles] at hc ⊢
    grind

variable (h : 5 ≤ ENat.card α)

@[simp]
theorem lyndon_conv (a : α) : (lyndon e h).conv a = a := rfl

@[simp]
theorem lyndon_id : (lyndon e h).id = {e} := rfl

@[simp]
theorem lyndon_cycles : (lyndon e h).cycles = lyndonCycles e := rfl

end AtomStructure

namespace ComplexAlgebra

open AtomStructure

variable (h : 5 ≤ ENat.card α)

/-- **Theorem A** of [Monk1964], first half: the Lyndon algebra is integral. -/
theorem isIntegral_lyndon : IsIntegral (ComplexAlgebra (lyndon e h)) :=
  (isIntegral_iff _).mpr ⟨e, rfl⟩

/-- **Theorem A** of [Monk1964], second half: the converse of the Lyndon algebra is trivial. -/
instance : TrivialStar (ComplexAlgebra (lyndon e h)) where
  star_trivial x := by
    ext a
    rw [mem_star, lyndon_conv]

end ComplexAlgebra

end Basic

/-! ### Representation over a group -/

section GroupRepresentation

open AtomStructure

namespace Lyndon

variable {α : Type*} {K : Type*} [Field K] {e : α} (φ : {a // a ≠ e} ≃ Option K)

open scoped Classical in
/-- The direction of a vector of the plane `K × K`, as an atom of the Lyndon algebra whose points
are identified with the projective line `Option K`: the zero vector is sent to the identity atom
`e`, and a nonzero vector to the point corresponding to its slope. -/
noncomputable def slope (v : K × K) : α :=
  if v = 0 then e else φ.symm (if v.1 = 0 then none else some (v.2 / v.1))

variable {φ} {u v w : K × K}

@[simp]
theorem slope_zero : slope φ 0 = e := ite_eq_left rfl

@[simp]
theorem slope_eq_iff : slope φ v = e ↔ v = 0 := by
  refine ⟨fun h => ?_, fun h => h ▸ slope_zero⟩
  by_contra hv
  rw [slope, ite_eq_right hv] at h
  exact (φ.symm _).property h

theorem slope_eq_slope_iff (hu : u ≠ 0) (hv : v ≠ 0) :
    slope φ u = slope φ v ↔ u.1 * v.2 = u.2 * v.1 := by
  rw [slope, slope, ite_eq_right hu, ite_eq_right hv, Subtype.coe_inj, φ.symm.apply_eq_iff_eq]
  by_cases hu1 : u.1 = 0 <;> by_cases hv1 : v.1 = 0
  · simp [hu1, hv1]
  · have hu2 : u.2 ≠ 0 := fun h => hu (Prod.ext hu1 h)
    simp [hu1, hv1, hu2]
  · have hv2 : v.2 ≠ 0 := fun h => hv (Prod.ext hv1 h)
    simp [hu1, hv1, hv2]
  · rw [ite_eq_right hu1, ite_eq_right hv1, Option.some.injEq, div_eq_div_iff hu1 hv1, eq_comm,
      mul_comm v.2]

theorem slope_smul {c : K} (hc : c ≠ 0) (v : K × K) : slope φ (c • v) = slope φ v := by
  by_cases hv : v = 0
  · rw [hv, smul_zero]
  · have hcv : c • v ≠ 0 := fun h => hv (by rw [← inv_smul_smul₀ hc v, h, smul_zero])
    rw [slope_eq_slope_iff hcv hv, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, smul_eq_mul]
    ring

theorem slope_neg (v : K × K) : slope φ (-v) = slope φ v := by
  rw [← neg_one_smul K v, slope_smul (neg_ne_zero.mpr one_ne_zero)]

/-- Every point is the direction of some nonzero vector. -/
theorem exists_slope_eq {a : α} (ha : a ≠ e) : ∃ v : K × K, v ≠ 0 ∧ slope φ v = a := by
  cases hd : φ ⟨a, ha⟩ with
  | none =>
    refine ⟨(0, 1), by simp, ?_⟩
    rw [slope, ite_eq_right (by simp), ite_eq_left rfl, ← hd, Equiv.symm_apply_apply]
  | some k =>
    refine ⟨(1, k), by simp, ?_⟩
    rw [slope, ite_eq_right (by simp), ite_eq_right one_ne_zero, div_one, ← hd,
      Equiv.symm_apply_apply]

theorem slope_surjective : Function.Surjective (slope φ) := by
  intro a
  by_cases ha : a = e
  · exact ⟨(0 : K × K), by rw [slope_zero, ha]⟩
  · obtain ⟨v, -, hv⟩ := exists_slope_eq (φ := φ) ha
    exact ⟨v, hv⟩

/-- The directions of two vectors and of their sum form a cycle of Lyndon's atom structure. -/
theorem slope_mem_lyndonCycles (u w : K × K) :
    (slope φ u, slope φ w, slope φ (u + w)) ∈ lyndonCycles e := by
  rw [mem_lyndonCycles]
  by_cases hu : u = 0
  · exact .inl ⟨hu ▸ slope_zero, by rw [hu, zero_add]⟩
  by_cases hw : w = 0
  · exact .inr <| .inl ⟨hw ▸ slope_zero, by rw [hw, add_zero]⟩
  by_cases ht : u + w = 0
  · refine .inr <| .inr <| .inl ⟨ht ▸ slope_zero, ?_⟩
    rw [eq_neg_of_add_eq_zero_left ht, slope_neg]
  have hut : slope φ u = slope φ (u + w) ↔ u.1 * w.2 = u.2 * w.1 := by
    rw [slope_eq_slope_iff hu ht, Prod.fst_add, Prod.snd_add]
    constructor <;> intro h <;> linear_combination h
  have hwt : slope φ w = slope φ (u + w) ↔ u.1 * w.2 = u.2 * w.1 := by
    rw [slope_eq_slope_iff hw ht, Prod.fst_add, Prod.snd_add]
    constructor <;> intro h <;> linear_combination -h
  by_cases hp : u.1 * w.2 = u.2 * w.1
  · exact .inr <| .inr <| .inr <| .inl ⟨(slope_eq_slope_iff hu hw).mpr hp, hwt.mpr hp⟩
  · exact .inr <| .inr <| .inr <| .inr ⟨mt (slope_eq_slope_iff hu hw).mp hp, mt hwt.mp hp,
      mt hut.mp hp, mt slope_eq_iff.mp hu, mt slope_eq_iff.mp hw, mt slope_eq_iff.mp ht⟩

/-- Every cycle of Lyndon's atom structure ending in the direction of `t` arises from a
decomposition of `t` as a sum of two vectors. This needs a scalar other than `0` and `1`. -/
theorem exists_add_of_mem_lyndonCycles (hK : ∃ c : K, c ≠ 0 ∧ c ≠ 1) {r s : α} {t : K × K}
    (h : (r, s, slope φ t) ∈ lyndonCycles e) :
    ∃ u w, slope φ u = r ∧ slope φ w = s ∧ u + w = t := by
  rw [mem_lyndonCycles] at h
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨ht, rfl⟩ | ⟨rfl, rfl⟩ | ⟨hrs, hst, hrt, hr, hs, ht⟩ := h
  · exact ⟨0, t, slope_zero, rfl, zero_add t⟩
  · exact ⟨t, 0, rfl, slope_zero, add_zero t⟩
  · obtain ⟨v, hv⟩ := slope_surjective (φ := φ) r
    exact ⟨v, -v, hv, by rw [slope_neg, hv], by rw [add_neg_cancel, slope_eq_iff.mp ht]⟩
  · obtain ⟨c, hc0, hc1⟩ := hK
    exact ⟨c • t, (1 - c) • t, slope_smul hc0 t, slope_smul (sub_ne_zero.mpr hc1.symm) t,
      by rw [← add_smul, add_sub_cancel, one_smul]⟩
  · obtain ⟨u, hu, rfl⟩ := exists_slope_eq (φ := φ) hr
    obtain ⟨w, hw, rfl⟩ := exists_slope_eq (φ := φ) hs
    have ht0 : t ≠ 0 := mt slope_eq_iff.mpr ht
    have hD : u.1 * w.2 - u.2 * w.1 ≠ 0 :=
      sub_ne_zero.mpr (mt (slope_eq_slope_iff hu hw).mpr hrs)
    have hx : t.1 * w.2 - t.2 * w.1 ≠ 0 :=
      sub_ne_zero.mpr (mt (slope_eq_slope_iff ht0 hw).mpr (Ne.symm hst))
    have hy : u.1 * t.2 - u.2 * t.1 ≠ 0 :=
      sub_ne_zero.mpr (mt (slope_eq_slope_iff hu ht0).mpr hrt)
    refine ⟨((t.1 * w.2 - t.2 * w.1) / (u.1 * w.2 - u.2 * w.1)) • u,
      ((u.1 * t.2 - u.2 * t.1) / (u.1 * w.2 - u.2 * w.1)) • w,
      slope_smul (div_ne_zero hx hD) u, slope_smul (div_ne_zero hy hD) w, Prod.ext ?_ ?_⟩
    · rw [Prod.fst_add, Prod.smul_fst, Prod.smul_fst, smul_eq_mul, smul_eq_mul,
        div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hD]
      ring
    · rw [Prod.snd_add, Prod.smul_snd, Prod.smul_snd, smul_eq_mul, smul_eq_mul,
        div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hD]
      ring

variable (φ) in
/-- The embedding of a Lyndon algebra into the complex algebra of the additive group of the plane
`K × K`: a set of atoms is sent to the set of vectors whose direction lies in it. -/
noncomputable def slopeHom (h : 5 ≤ ENat.card α) (hK : ∃ c : K, c ≠ 0 ∧ c ≠ 1) :
    RelationAlgebraHom (ComplexAlgebra (lyndon e h))
      (ComplexAlgebra (ofGroup (Multiplicative (K × K)))) :=
  RelationAlgebraHom.mk' (fun x => ⟨{v | slope φ v.toAdd ∈ x}⟩)
    (fun _ _ => rfl)
    (fun _ => rfl)
    (fun x y => by
      ext t
      constructor
      · rintro ⟨r, hr, s, hs, hc⟩
        obtain ⟨u, w, rfl, rfl, huw⟩ := exists_add_of_mem_lyndonCycles hK hc
        exact ⟨.ofAdd u, hr, .ofAdd w, hs, congrArg Multiplicative.ofAdd huw⟩
      · rintro ⟨u, hu, w, hw, rfl⟩
        exact ⟨_, hu, _, hw, slope_mem_lyndonCycles u.toAdd w.toAdd⟩)
    (by ext v; exact slope_eq_iff)
    (fun x => by
      ext v
      rw [ComplexAlgebra.mem_star]
      change slope φ v.toAdd ∈ star x ↔ slope φ (-v.toAdd) ∈ x
      rw [ComplexAlgebra.mem_star, slope_neg, lyndon_conv])

theorem slopeHom_injective (h : 5 ≤ ENat.card α) (hK : ∃ c : K, c ≠ 0 ∧ c ≠ 1) :
    Function.Injective (slopeHom φ h hK) := by
  intro x y hxy
  ext a
  obtain ⟨v, rfl⟩ := slope_surjective (φ := φ) a
  exact iff_of_eq (congrArg (fun z => Multiplicative.ofAdd v ∈ z) hxy)

/-- A field whose projective line is in bijection with the points of a Lyndon algebra has a scalar
other than `0` and `1`. -/
theorem exists_ne_zero_ne_one (h : 5 ≤ ENat.card α) (φ : {a // a ≠ e} ≃ Option K) :
    ∃ c : K, c ≠ 0 ∧ c ≠ 1 := by
  obtain ⟨x, hxe, hx⟩ :=
    ENat.exists_ne_of_five_le_card h e (φ.symm none) (φ.symm (some 0)) (φ.symm (some 1))
  cases hc : φ ⟨x, hxe⟩ with
  | none => exact absurd (by rw [← hc, Equiv.symm_apply_apply]) hx.1
  | some c =>
    refine ⟨c, fun h0 => hx.2.1 ?_, fun h1 => hx.2.2 ?_⟩
    · rw [← h0, ← hc, Equiv.symm_apply_apply]
    · rw [← h1, ← hc, Equiv.symm_apply_apply]

end Lyndon

open Lyndon

/-- A Lyndon algebra whose points are in bijection with the projective line over a field is
representable over a group. -/
theorem groupRepresentable_lyndon_of_field {α : Type u} (e : α) (h : 5 ≤ ENat.card α)
    (K : Type u) [Field K] (φ : {a // a ≠ e} ≃ Option K) :
    GroupRepresentable (ComplexAlgebra (lyndon e h)) :=
  ⟨Multiplicative (K × K), inferInstance, slopeHom φ h (exists_ne_zero_ne_one h φ),
    slopeHom_injective h (exists_ne_zero_ne_one h φ)⟩

/-- **Theorem C** of [Monk1964]: a Lyndon algebra on an infinite type is representable over a
group. -/
theorem groupRepresentable_lyndon {α : Type u} [Infinite α] (e : α) (h : 5 ≤ ENat.card α) :
    GroupRepresentable (ComplexAlgebra (lyndon e h)) := by
  obtain ⟨_⟩ := Infinite.nonempty_field (α := α)
  have hcard : Cardinal.mk {a // a ≠ e} = Cardinal.mk (Option α) := by
    rw [Cardinal.mk_option, Cardinal.mk_add_one_eq]
    refine Cardinal.mk_compl_of_infinite {e} ?_
    rw [Cardinal.mk_singleton]
    exact Cardinal.one_lt_aleph0.trans_le (Cardinal.aleph0_le_mk α)
  obtain ⟨φ⟩ := Cardinal.eq.mp hcard
  exact groupRepresentable_lyndon_of_field e h α φ

end GroupRepresentation

/-! ### Representations and projective planes -/

section Plane

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

end Plane

/-! ### Ultraproducts -/

section Ultraproduct

open AtomStructure Filter.Product

variable {ι : Type v} {α : ι → Type u} (e : ∀ i, α i) (h : ∀ i, 5 ≤ ENat.card (α i))
  (U : Ultrafilter ι)

/-- An ultraproduct of Lyndon atom structures is the Lyndon atom structure on the ultraproduct of
the types of atoms. -/
theorem AtomStructure.filterProduct_lyndon (h' : 5 ≤ ENat.card ((U : Filter ι).Product α)) :
    filterProduct (fun i => lyndon (e i) (h i)) (U : Filter ι) =
      lyndon (Filter.Product.mk (U : Filter ι) e) h' := by
  apply AtomStructure.ext
  · funext x
    induction x using induction_on with | h f
    rfl
  · ext x
    induction x using induction_on with | h f
    refine (mk_mem_filterProductId _ _).trans ?_
    simp only [lyndon_id, Set.mem_singleton_iff, mk_eq_mk]
  · ext ⟨x, y, z⟩
    induction x using induction_on with | h f
    induction y using induction_on with | h g
    induction z using induction_on with | h k
    refine (mk_mem_filterProductCycles _ _).trans ?_
    simp only [lyndon_cycles, mem_lyndonCycles, ne_eq, mk_eq_mk, Ultrafilter.eventually_or,
      Filter.eventually_and, Ultrafilter.eventually_not]

/-- An ultraproduct of Lyndon algebras is representable over a group when the ultraproduct of the
types of atoms is infinite. -/
theorem groupRepresentable_product_lyndon [Infinite ((U : Filter ι).Product α)] :
    GroupRepresentable ((U : Filter ι).Product fun i => ComplexAlgebra (lyndon (e i) (h i))) := by
  have : ∀ i, Nonempty (α i) := fun i => ⟨e i⟩
  have h' : 5 ≤ ENat.card ((U : Filter ι).Product α) := by
    rw [ENat.card_eq_top_of_infinite]
    exact le_top
  refine .of_injective (ComplexAlgebra.productHom _ U) (ComplexAlgebra.productHom_injective _ U) ?_
  rw [filterProduct_lyndon e h U h']
  exact groupRepresentable_lyndon _ h'

end Ultraproduct

end Cslib.RelationAlgebra
