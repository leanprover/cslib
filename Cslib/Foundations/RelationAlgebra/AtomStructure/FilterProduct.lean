/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.AtomStructure
public import Cslib.Foundations.RelationAlgebra.FilterProduct

/-!
# Reduced products and ultraproducts of atom structures

For a filter `l` on `ι` and a family `S i` of atom structures on types `α i`, the reduced product
`l.Product α` of the types of atoms carries an atom structure in which a triple of classes is a
cycle when its representatives form a cycle on a set in `l`.

When `l` is an ultrafilter, the ultraproduct of the complex algebras of the `S i` embeds into the
complex algebra of the ultraproduct of the `S i`. This is the general form of Lemma 1 of
[Monk1964] together with the computation at the end of the proof of Theorem 1 there. The embedding
need not be surjective.

## Main definitions

* `Cslib.RelationAlgebra.AtomStructure.filterProduct`: the reduced product of a family of atom
  structures.
* `Cslib.RelationAlgebra.ComplexAlgebra.productHom`: the embedding of an ultraproduct of complex
  algebras into the complex algebra of the ultraproduct of the atom structures.

## References

* [J. D. Monk, *On representable relation algebras*][Monk1964]

-/

@[expose] public section

namespace Cslib.RelationAlgebra

open Filter

variable {ι : Type*} {α : ι → Type*}

namespace AtomStructure

/-- Two atom structures with the same converse, identity atoms and cycles are equal. -/
protected theorem ext {α : Type*} {A B : AtomStructure α} (hconv : A.conv = B.conv)
    (hid : A.id = B.id) (hcycles : A.cycles = B.cycles) : A = B := by
  cases A
  cases B
  congr

variable (S : ∀ i, AtomStructure (α i)) (l : Filter ι)

local notation "π" => Filter.Product.mk l

/-- The identity atoms of the reduced product of a family of atom structures. -/
def filterProductId : Set (l.Product α) :=
  {x | ∃ f, π f = x ∧ ∀ᶠ i in l, f i ∈ (S i).id}

/-- The cycles of the reduced product of a family of atom structures. -/
def filterProductCycles : Set (l.Product α × l.Product α × l.Product α) :=
  {x | ∃ f g h, (π f, π g, π h) = x ∧ ∀ᶠ i in l, (f i, g i, h i) ∈ (S i).cycles}

theorem mk_mem_filterProductId {f : ∀ i, α i} :
    π f ∈ filterProductId S l ↔ ∀ᶠ i in l, f i ∈ (S i).id := by
  refine ⟨fun ⟨f', hf, h⟩ => ?_, fun h => ⟨f, rfl, h⟩⟩
  filter_upwards [h, Filter.Product.mk_eq_mk.mp hf] with i h hf
  rwa [← hf]

theorem mk_mem_filterProductCycles {f g h : ∀ i, α i} :
    (π f, π g, π h) ∈ filterProductCycles S l ↔ ∀ᶠ i in l, (f i, g i, h i) ∈ (S i).cycles := by
  refine ⟨fun ⟨f', g', h', heq, hc⟩ => ?_, fun hc => ⟨f, g, h, rfl, hc⟩⟩
  rw [Prod.mk.injEq, Prod.mk.injEq] at heq
  filter_upwards [hc, Filter.Product.mk_eq_mk.mp heq.1, Filter.Product.mk_eq_mk.mp heq.2.1,
    Filter.Product.mk_eq_mk.mp heq.2.2]
    with i hc hf hg hh
  rwa [← hf, ← hg, ← hh]

open scoped Classical in
/-- The reduced product of a family of atom structures. When the filter is an ultrafilter this is
their ultraproduct as first-order structures. -/
noncomputable def filterProduct : AtomStructure (l.Product α) where
  conv := Quotient.map (fun f i => (S i).conv (f i)) fun f g h => h.mono fun i hi => by
    simp only [hi]
  id := filterProductId S l
  cycles := filterProductCycles S l
  assoc {r q p s t} := by
    induction r using Filter.Product.induction_on with | h r
    induction q using Filter.Product.induction_on with | h q
    induction p using Filter.Product.induction_on with | h p
    induction s using Filter.Product.induction_on with | h s
    induction t using Filter.Product.induction_on with | h t
    intro h₁ h₂
    rw [mk_mem_filterProductCycles] at h₁ h₂
    refine ⟨π fun i => if h : ∃ x, (x, t i, p i) ∈ (S i).cycles ∧ (r i, s i, x) ∈ (S i).cycles
      then h.choose else r i, ?_, ?_⟩
    · rw [mk_mem_filterProductCycles]
      filter_upwards [h₁, h₂] with i h₁ h₂
      have hex := (S i).assoc h₁ h₂
      rw [dite_eq_left hex]
      exact hex.choose_spec.1
    · rw [mk_mem_filterProductCycles]
      filter_upwards [h₁, h₂] with i h₁ h₂
      have hex := (S i).assoc h₁ h₂
      rw [dite_eq_left hex]
      exact hex.choose_spec.2
  id_cycle_right {s r p} := by
    induction s using Filter.Product.induction_on with | h s
    induction r using Filter.Product.induction_on with | h r
    induction p using Filter.Product.induction_on with | h p
    intro hs hc
    rw [mk_mem_filterProductId] at hs
    rw [mk_mem_filterProductCycles] at hc
    refine Filter.Product.mk_eq_mk.mpr ?_
    filter_upwards [hs, hc] with i hs hc using (S i).id_cycle_right hs hc
  exists_id_cycle_right r := by
    induction r using Filter.Product.induction_on with | h r
    refine ⟨π fun i => ((S i).exists_id_cycle_right (r i)).choose, ?_, ?_⟩
    · rw [mk_mem_filterProductId]
      exact .of_forall fun i => ((S i).exists_id_cycle_right (r i)).choose_spec.1
    · rw [mk_mem_filterProductCycles]
      exact .of_forall fun i => ((S i).exists_id_cycle_right (r i)).choose_spec.2
  cycle_left {r s t} := by
    induction r using Filter.Product.induction_on with | h r
    induction s using Filter.Product.induction_on with | h s
    induction t using Filter.Product.induction_on with | h t
    intro hc
    rw [mk_mem_filterProductCycles] at hc
    exact (mk_mem_filterProductCycles S l).mpr (hc.mono fun i hc => (S i).cycle_left hc)

@[simp]
theorem filterProduct_conv_mk (f : ∀ i, α i) :
    (filterProduct S l).conv (π f) = π fun i => (S i).conv (f i) := rfl

@[simp]
theorem mk_mem_filterProduct_id {f : ∀ i, α i} :
    π f ∈ (filterProduct S l).id ↔ ∀ᶠ i in l, f i ∈ (S i).id :=
  mk_mem_filterProductId S l

@[simp]
theorem mk_mem_filterProduct_cycles {f g h : ∀ i, α i} :
    (π f, π g, π h) ∈ (filterProduct S l).cycles ↔
      ∀ᶠ i in l, (f i, g i, h i) ∈ (S i).cycles :=
  mk_mem_filterProductCycles S l

end AtomStructure

namespace ComplexAlgebra

open AtomStructure Filter.Product

variable (S : ∀ i, AtomStructure (α i)) (U : Ultrafilter ι)

local notation "π" => Filter.Product.mk (U : Filter ι)

/-- The function underlying `ComplexAlgebra.productHom`. -/
noncomputable def productFun (x : (U : Filter ι).Product fun i => ComplexAlgebra (S i)) :
    ComplexAlgebra (filterProduct S (U : Filter ι)) :=
  Quotient.liftOn x (fun X => ⟨{a | ∃ f, π f = a ∧ ∀ᶠ i in U, f i ∈ X i}⟩) fun X Y hXY => by
    congr 1
    ext a
    constructor
    · rintro ⟨f, rfl, hf⟩
      exact ⟨f, rfl, by filter_upwards [hf, hXY] with i hf hXY using hXY ▸ hf⟩
    · rintro ⟨f, rfl, hf⟩
      exact ⟨f, rfl, by filter_upwards [hf, hXY] with i hf hXY using hXY ▸ hf⟩

theorem mk_mem_productFun {X : ∀ i, ComplexAlgebra (S i)} {f : ∀ i, α i} :
    π f ∈ productFun S U (mkHom _ _ X) ↔ ∀ᶠ i in U, f i ∈ X i := by
  refine ⟨fun ⟨f', hf, h⟩ => ?_, fun h => ⟨f, rfl, h⟩⟩
  filter_upwards [h, Filter.Product.mk_eq_mk.mp hf] with i h hf
  rwa [← hf]

/-- The embedding of an ultraproduct of complex algebras into the complex algebra of the
ultraproduct of the atom structures: the class of a family of sets `X i` is sent to the set of
classes of families of atoms that lie in `X i` for almost all `i`. -/
noncomputable def productHom :
    RelationAlgebraHom ((U : Filter ι).Product fun i => ComplexAlgebra (S i))
      (ComplexAlgebra (filterProduct S (U : Filter ι))) :=
  RelationAlgebraHom.mk' (productFun S U)
    (fun x y => by
      induction x using mkHom_induction_on with | h X
      induction y using mkHom_induction_on with | h Y
      rw [← SupHomClass.map_sup]
      ext a
      induction a using Filter.Product.induction_on with | h f
      rw [mem_sup, mk_mem_productFun, mk_mem_productFun, mk_mem_productFun,
        ← Ultrafilter.eventually_or]
      rfl)
    (fun x => by
      induction x using mkHom_induction_on with | h X
      rw [← map_compl']
      ext a
      induction a using Filter.Product.induction_on with | h f
      rw [mem_compl, mk_mem_productFun, mk_mem_productFun, ← Ultrafilter.eventually_not]
      rfl)
    (fun x y => by
      induction x using mkHom_induction_on with | h X
      induction y using mkHom_induction_on with | h Y
      rw [← map_mul]
      ext a
      induction a using Filter.Product.induction_on with | h f
      rw [mk_mem_productFun, mem_mul]
      constructor
      · intro h
        have : ∀ i, Nonempty (α i × α i) := fun i => ⟨(f i, f i)⟩
        obtain ⟨rs, hrs⟩ := (Filter.skolem (P := fun i (rs : α i × α i) =>
          rs.1 ∈ X i ∧ rs.2 ∈ Y i ∧ (rs.1, rs.2, f i) ∈ (S i).cycles)).mp
          (h.mono fun i ⟨r, hr, s, hs, hc⟩ => ⟨(r, s), hr, hs, hc⟩)
        exact ⟨π fun i => (rs i).1, (mk_mem_productFun S U).mpr (hrs.mono fun i h => h.1),
          π fun i => (rs i).2, (mk_mem_productFun S U).mpr (hrs.mono fun i h => h.2.1),
          (mk_mem_filterProduct_cycles S _).mpr (hrs.mono fun i h => h.2.2)⟩
      · rintro ⟨r, hr, s, hs, hc⟩
        induction r using Filter.Product.induction_on with | h r
        induction s using Filter.Product.induction_on with | h s
        rw [mk_mem_productFun] at hr hs
        rw [mk_mem_filterProduct_cycles] at hc
        filter_upwards [hr, hs, hc] with i hr hs hc using ⟨r i, hr, s i, hs, hc⟩)
    (by
      rw [← map_one (mkHom (fun i => ComplexAlgebra (S i)) (U : Filter ι))]
      ext a
      induction a using Filter.Product.induction_on with | h f
      rw [mk_mem_productFun, mem_one, mk_mem_filterProduct_id]
      rfl)
    (fun x => by
      induction x using mkHom_induction_on with | h X
      rw [← map_star]
      ext a
      induction a using Filter.Product.induction_on with | h f
      rw [mem_star, filterProduct_conv_mk, mk_mem_productFun, mk_mem_productFun]
      exact Filter.eventually_congr (.of_forall fun i => mem_star))

@[simp]
theorem mk_mem_productHom {X : ∀ i, ComplexAlgebra (S i)} {f : ∀ i, α i} :
    π f ∈ productHom S U (Filter.Product.mk (U : Filter ι) X) ↔ ∀ᶠ i in U, f i ∈ X i :=
  mk_mem_productFun S U

/-- An ultraproduct of complex algebras embeds into the complex algebra of the ultraproduct of the
atom structures. -/
theorem productHom_injective [∀ i, Nonempty (α i)] : Function.Injective (productHom S U) := by
  intro x y hxy
  induction x using mkHom_induction_on with | h X
  induction y using mkHom_induction_on with | h Y
  rw [mkHom_eq_mkHom]
  by_contra hne
  rw [← Ultrafilter.eventually_not] at hne
  obtain ⟨f, hf⟩ := (Filter.skolem (P := fun i (a : α i) => ¬(a ∈ X i ↔ a ∈ Y i))).mp
    (hne.mono fun i hne => by
      by_contra hall
      exact hne (ComplexAlgebra.ext fun a => not_not.mp (not_exists.mp hall a)))
  have hiff : (∀ᶠ i in U, f i ∈ X i) ↔ ∀ᶠ i in U, f i ∈ Y i := by
    rw [← mk_mem_productFun S U, ← mk_mem_productFun S U]
    exact iff_of_eq (congrArg (fun x => π f ∈ x) hxy)
  by_cases hX : ∀ᶠ i in U, f i ∈ X i
  · exact (hf.and (hX.and (hiff.mp hX))).exists.elim fun i h => h.1 (iff_of_true h.2.1 h.2.2)
  · have hY := mt hiff.mpr hX
    rw [← Ultrafilter.eventually_not] at hX hY
    exact (hf.and (hX.and hY)).exists.elim fun i h => h.1 (iff_of_false h.2.1 h.2.2)

end ComplexAlgebra

end Cslib.RelationAlgebra
