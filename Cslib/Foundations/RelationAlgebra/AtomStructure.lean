/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.ModelTheory
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Order.BooleanAlgebra.Set

/-!
# Atom structures

This module defines atom structures and their complex relation algebras. It also constructs the
atom structure of an atomic relation algebra and reconstructs a complete atomic relation algebra
from its atom structure.

## Reduced products and ultraproducts

For a filter `l` on `ι` and a family `S i` of atom structures on types `α i`, the reduced product
`l.Product α` of the types of atoms carries an atom structure in which a triple of classes is a
cycle when its representatives form a cycle on a set in `l`
(`Cslib.RelationAlgebra.AtomStructure.filterProduct`).

When `l` is an ultrafilter, the ultraproduct of the complex algebras of the `S i` embeds into the
complex algebra of the ultraproduct of the `S i`
(`Cslib.RelationAlgebra.ComplexAlgebra.productHom`). This is the general form of Lemma 1 of
[Monk1964] together with the computation at the end of the proof of Theorem 1 there. The embedding
need not be surjective.

## References

* [Steven Givant, *Advanced Topics in Relation Algebras*][Givant2017b]
* [J. D. Monk, *On representable relation algebras*][Monk1964]

-/

@[expose] public section

namespace Cslib.RelationAlgebra

/--
An axiomatic atom structure, used to construct a `RelationAlgebra` from its cycles.
-/
structure AtomStructure (α : Type*) where
  /-- The converse operation, presented as a function for stating the cycle rules. -/
  conv : α → α
  /-- The set of identity atoms. -/
  id : Set α
  /-- The set of atom cycles, where `(r, s, t)` represents `t ≤ r * s`. -/
  cycles : Set (α × α × α)
  assoc : (r, q, p) ∈ cycles → (s, t, q) ∈ cycles → ∃ q', (q', t, p) ∈ cycles ∧ (r, s, q') ∈ cycles
  id_cycle_right : s ∈ id → (r, s, p) ∈ cycles → p = r
  exists_id_cycle_right (r) : ∃ s ∈ id, (r, s, r) ∈ cycles
  cycle_left : (r, s, t) ∈ cycles → (conv r, t, s) ∈ cycles

namespace AtomStructure

variable {α : Type*} (A : AtomStructure α)

@[simp, grind =]
theorem conv_conv (r : α) : A.conv (A.conv r) = r := by
  grind [A.id_cycle_right, => A.cycle_left, A.exists_id_cycle_right r]

theorem conv_cycles {r s t : α} (h : (r, s, t) ∈ A.cycles) :
    (A.conv s, A.conv r, A.conv t) ∈ A.cycles := by
  obtain ⟨e, he, hs⟩ := A.exists_id_cycle_right s
  obtain ⟨q, hq, hsq⟩ := A.assoc (A.cycle_left hs) (A.cycle_left h)
  grind [A.id_cycle_right he (A.cycle_left hq)]

theorem assoc_symm {r s t p q : α} (h₁ : (q, t, p) ∈ A.cycles) (h₂ : (r, s, q) ∈ A.cycles) :
    ∃ q', (r, q', p) ∈ A.cycles ∧ (s, t, q') ∈ A.cycles := by
  obtain ⟨u, hu₁, hu₂⟩ := A.assoc (A.conv_cycles h₁) (A.conv_cycles h₂)
  exact ⟨A.conv u, by simpa using A.conv_cycles hu₁, by simpa using A.conv_cycles hu₂⟩

theorem conv_eq_self_of_mem_id {r : α} (hr : r ∈ A.id) : A.conv r = r := by
  grind [A.id_cycle_right, => A.cycle_left, A.exists_id_cycle_right r, A.conv_cycles]

theorem id_cycle_left {s r p : α} (hs : s ∈ A.id) (h : (s, r, p) ∈ A.cycles) : p = r :=
  Function.Involutive.injective A.conv_conv <|
    A.id_cycle_right hs (A.conv_eq_self_of_mem_id hs ▸ A.conv_cycles h)

theorem exists_id_cycle_left (r : α) : ∃ s ∈ A.id, (s, r, r) ∈ A.cycles := by
  obtain ⟨s, hs, h⟩ := A.exists_id_cycle_right (A.conv r)
  exact ⟨s, hs, by simpa [A.conv_eq_self_of_mem_id hs] using A.conv_cycles h⟩

end AtomStructure

/-- The complex relation algebra of an atom structure. "Complex" here means a subset of atoms. -/
structure ComplexAlgebra {α : Type*} (A : AtomStructure α) where
  /-- The underlying set. -/
  carrier : Set α

namespace ComplexAlgebra

variable {α : Type*} (A : AtomStructure α)

/-- Equivalence with the powerset of the atom type. -/
def equivSet : ComplexAlgebra A ≃ Set α where
  toFun := carrier
  invFun := mk
  left_inv _ := rfl
  right_inv _ := rfl

instance : SetLike (ComplexAlgebra A) α where
  coe := carrier
  coe_injective := (equivSet A).injective

instance : CompleteAtomicBooleanAlgebra (ComplexAlgebra A) :=
  (equivSet A).completeAtomicBooleanAlgebra

instance : IsConcreteLE (ComplexAlgebra A) α where
  le_iff := .rfl

instance [Finite α] : Finite (ComplexAlgebra A) := Finite.of_equiv (Set α) (equivSet A).symm

/-- Order isomorphism with the powerset of the atom type. -/
def orderIsoSet : ComplexAlgebra A ≃o Set α where
  toEquiv := equivSet A
  map_rel_iff' := Iff.rfl

instance : One (ComplexAlgebra A) where
  one := ⟨A.id⟩

instance : Mul (ComplexAlgebra A) where
  mul x y := ⟨{t | ∃ r ∈ x, ∃ s ∈ y, (r, s, t) ∈ A.cycles}⟩

instance : Star (ComplexAlgebra A) where
  star x := ⟨A.conv '' x.carrier⟩

section

variable {A} {x y : ComplexAlgebra A} {a : α}

@[ext]
theorem ext (h : ∀ a, a ∈ x ↔ a ∈ y) : x = y := SetLike.ext h

@[simp]
theorem mem_mk {s : Set α} : a ∈ (⟨s⟩ : ComplexAlgebra A) ↔ a ∈ s := .rfl

theorem mem_carrier : a ∈ x.carrier ↔ a ∈ x := .rfl

@[simp, grind =]
theorem mem_sup : a ∈ x ⊔ y ↔ a ∈ x ∨ a ∈ y := .rfl

@[simp, grind =]
theorem mem_compl : a ∈ xᶜ ↔ a ∉ x := .rfl

@[simp, grind =]
theorem mem_one : a ∈ (1 : ComplexAlgebra A) ↔ a ∈ A.id := .rfl

@[grind =]
theorem mem_mul : a ∈ x * y ↔ ∃ r ∈ x, ∃ s ∈ y, (r, s, a) ∈ A.cycles := .rfl

@[simp, grind =]
theorem mem_star : a ∈ star x ↔ A.conv a ∈ x :=
  Set.mem_image_iff_of_inverse A.conv_conv A.conv_conv

end

instance : RelationAlgebra (ComplexAlgebra A) where
  mul_assoc a b c := by ext p; grind [A.assoc, A.assoc_symm]
  one_mul x := by ext t; grind [A.id_cycle_left, A.exists_id_cycle_left t]
  mul_one x := by ext t; grind [A.id_cycle_right, A.exists_id_cycle_right t]
  star_involutive x := by ext; simp
  star_mul x y := by ext; grind [=> A.conv_cycles]
  sup_mul a b c := by ext; grind
  star_sup a b := by ext; simp
  tarski x y := by grind [IsConcreteLE.le_iff, => A.cycle_left]

instance : CompleteAtomicRelationAlgebra (ComplexAlgebra A) where

/-- The atom of a complex algebra given by an atom of the atom structure. -/
def atom (a : α) : ComplexAlgebra A := ⟨{a}⟩

variable {A} in
@[simp, grind =]
theorem mem_atom {a b : α} : b ∈ atom A a ↔ b = a := .rfl

variable {A} in
theorem atom_le_iff {a : α} {x : ComplexAlgebra A} : atom A a ≤ x ↔ a ∈ x :=
  ⟨fun h => h rfl, fun h _ hb => hb ▸ h⟩

variable {A} in
theorem mem_atom_mul_atom {a b c : α} : c ∈ atom A a * atom A b ↔ (a, b, c) ∈ A.cycles :=
  ⟨fun ⟨_, hr, _, hs, h⟩ => hr ▸ hs ▸ h, fun h => ⟨a, rfl, b, rfl, h⟩⟩

variable {A} in
theorem atom_inf_atom_of_ne {a b : α} (h : a ≠ b) : atom A a ⊓ atom A b = ⊥ := by
  ext c
  exact ⟨fun ⟨ha, hb⟩ => h (ha.symm.trans hb), False.elim⟩

/-- A complex algebra is integral exactly when its identity set is a singleton. -/
theorem isIntegral_iff : IsIntegral (ComplexAlgebra A) ↔ ∃ a, A.id = {a} :=
  ((orderIsoSet A).isAtom_iff (1 : ComplexAlgebra A)).symm.trans Set.isAtom_iff

end ComplexAlgebra

/-- The atom structure formed by the atoms of an atomic relation algebra. -/
def atomStructure (α : Type*) [RelationAlgebra α] [IsAtomic α] :
    AtomStructure {a : α // IsAtom a} where
  conv a := ⟨star a.val, isAtom_star_iff.mpr a.property⟩
  id := {a | a.val ≤ 1}
  cycles := {(r, s, t) | (t : α) ≤ r * s}
  assoc {r q p s t} h₁ h₂ := by
    have hp : (p : α) ≤ r * s * t := by
      rw [mul_assoc]
      exact h₁.trans (mul_le_mul_right h₂ _)
    obtain ⟨q', hq', hq'rs, hpq'⟩ := exists_atom_le_mul_left p.property hp
    exact ⟨⟨q', hq'⟩, hpq', hq'rs⟩
  id_cycle_right {s r p} hs h := by
    ext
    apply (r.property.le_iff_eq p.property.ne_bot).mp
    simpa using h.trans (mul_le_mul_right hs _)
  exists_id_cycle_right r := by
    obtain ⟨s, hs, hs1, hrs⟩ := exists_atom_le_mul_right r.property (le_of_eq (mul_one r.val).symm)
    exact ⟨⟨s, hs⟩, hs1, hrs⟩
  cycle_left {r s t} h := atom_cycle_left s.property t.property.ne_bot h

/-- The isomorphism from a complete atomic relation algebra to the complex algebra of its
atom structure. -/
noncomputable def complexAlgebraEquiv {α : Type*} [CompleteAtomicRelationAlgebra α] :
    RelationAlgebraEquiv α (ComplexAlgebra (atomStructure α)) where
  toOrderIso := CompleteAtomicBooleanAlgebra.toSetOfIsAtom.trans
    (ComplexAlgebra.orderIsoSet (atomStructure α)).symm
  map_mul' x y := by
    ext p
    rw [ComplexAlgebra.mem_mul]
    constructor
    · intro hp
      obtain ⟨r, hr, hrx, hpr⟩ := exists_atom_le_mul_left p.property hp
      obtain ⟨s, hs, hsy, hps⟩ := exists_atom_le_mul_right p.property hpr
      exact ⟨⟨r, hr⟩, hrx, ⟨s, hs⟩, hsy, hps⟩
    · rintro ⟨r, hr, s, hs, h⟩
      exact h.trans (mul_le_mul' hr hs)
  map_star' x := by
    ext p
    rw [ComplexAlgebra.mem_star]
    exact le_star_iff

theorem complexAlgebraEquiv_apply {α : Type*} [CompleteAtomicRelationAlgebra α] (x : α) :
    complexAlgebraEquiv x = ⟨{a | a.val ≤ x}⟩ := rfl

/-! ### Reduced products and ultraproducts of atom structures -/

section FilterProduct

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
      (ComplexAlgebra (filterProduct S (U : Filter ι))) where
  toFun := productFun S U
  map_sup' x y := by
    induction x using mkHom_induction_on with | h X
    induction y using mkHom_induction_on with | h Y
    rw [← SupHomClass.map_sup]
    ext a
    induction a using Filter.Product.induction_on with | h f
    rw [mem_sup, mk_mem_productFun, mk_mem_productFun, mk_mem_productFun,
      ← Ultrafilter.eventually_or]
    rfl
  map_inf' x y := by
    induction x using mkHom_induction_on with | h X
    induction y using mkHom_induction_on with | h Y
    rw [← InfHomClass.map_inf]
    ext a
    induction a using Filter.Product.induction_on with | h f
    rw [mk_mem_productFun]
    exact Filter.eventually_and.trans
      (and_congr (mk_mem_productFun S U).symm (mk_mem_productFun S U).symm)
  map_top' := by
    rw [← TopHomClass.map_top (mkHom (fun i => ComplexAlgebra (S i)) (U : Filter ι))]
    ext a
    induction a using Filter.Product.induction_on with | h f
    rw [mk_mem_productFun]
    exact iff_of_true (.of_forall fun _ => trivial) trivial
  map_bot' := by
    rw [← BotHomClass.map_bot (mkHom (fun i => ComplexAlgebra (S i)) (U : Filter ι))]
    ext a
    induction a using Filter.Product.induction_on with | h f
    rw [mk_mem_productFun]
    exact iff_of_false (fun h => h.exists.elim fun _ => id) id
  map_mul' x y := by
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
        (mk_mem_filterProductCycles S _).mpr (hrs.mono fun i h => h.2.2)⟩
    · rintro ⟨r, hr, s, hs, hc⟩
      induction r using Filter.Product.induction_on with | h r
      induction s using Filter.Product.induction_on with | h s
      rw [mk_mem_productFun] at hr hs
      replace hc := (mk_mem_filterProductCycles S _).mp hc
      filter_upwards [hr, hs, hc] with i hr hs hc using ⟨r i, hr, s i, hs, hc⟩
  map_one' := by
    rw [← map_one (mkHom (fun i => ComplexAlgebra (S i)) (U : Filter ι))]
    ext a
    induction a using Filter.Product.induction_on with | h f
    rw [mk_mem_productFun, mem_one]
    exact (mk_mem_filterProductId S _).symm
  map_star' x := by
    induction x using mkHom_induction_on with | h X
    rw [← map_star]
    ext a
    induction a using Filter.Product.induction_on with | h f
    rw [mem_star, filterProduct_conv_mk, mk_mem_productFun, mk_mem_productFun]
    exact Filter.eventually_congr (.of_forall fun i => mem_star)

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

end FilterProduct

end Cslib.RelationAlgebra
