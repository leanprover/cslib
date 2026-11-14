/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Group
public import Cslib.Foundations.RelationAlgebra.Lyndon.Basic
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.FieldTheory.Cardinality
public import Mathlib.Tactic.LinearCombination

/-!
# Representations of Lyndon algebras

This module shows that the Lyndon algebra `𝔄(α, e)` is representable over a group when its points
`α \ {e}` form the projective line over a field, following [Lyndon1961].

## Main statements

* `Cslib.RelationAlgebra.groupRepresentable_lyndon_of_field`: if the points `α \ {e}` are in
  bijection with the projective line `Option K` over a field `K`, then `𝔄(α, e)` is representable
  over the additive group of the plane `K × K`. A point is sent to the punctured line through the
  origin with the corresponding slope.
* `Cslib.RelationAlgebra.groupRepresentable_lyndon`: Theorem C of [Monk1964], that `𝔄(α, e)` is
  representable over a group when `α` is infinite.

## References

* [R. C. Lyndon, *Relation algebras and projective geometries*][Lyndon1961]
* [J. D. Monk, *On representable relation algebras*][Monk1964]

-/

@[expose] public section

universe u

namespace Cslib.RelationAlgebra

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

end Cslib.RelationAlgebra
