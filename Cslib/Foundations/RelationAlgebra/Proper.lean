/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Representation
public import Mathlib.MeasureTheory.SetSemiring

/-!
# Proper relation algebras

-/

@[expose] public section

universe u v w

namespace Cslib.RelationAlgebra

class ProperRelationAlgebra {α : Type u} (carrier : Set (SetRel α α))
    (unit : outParam (SetRel α α)) : Prop extends MeasureTheory.IsSetRing carrier where
  subset_unit {R} : R ∈ carrier → R ⊆ unit
  unit_mem : unit ∈ carrier
  id_mem : SetRel.id ∈ carrier
  inv_mem {R} : R ∈ carrier → SetRel.inv R ∈ carrier
  comp_mem {R S} : R ∈ carrier → S ∈ carrier → SetRel.comp R S ∈ carrier

namespace ProperRelationAlgebra

variable {α : Type u} {carrier : Set (SetRel α α)} {unit : SetRel α α}

/-- The carrier of a proper relation algebra uniquely determines its unit. -/
theorem unit_unique [h : ProperRelationAlgebra carrier unit] {unit' : SetRel α α}
    (h' : ProperRelationAlgebra carrier unit') : unit = unit' :=
  Set.Subset.antisymm (h'.subset_unit h.unit_mem) (h.subset_unit h'.unit_mem)

variable [ProperRelationAlgebra carrier unit]

include carrier in
/-- The unit of a proper relation algebra is an equivalence relation. -/
theorem unit_equivalence : Equivalence (fun x y => (x, y) ∈ unit) where
  refl _ := subset_unit (carrier := carrier) id_mem rfl
  symm hxy := subset_unit (carrier := carrier) (inv_mem unit_mem) hxy
  trans hxy hyz := subset_unit (carrier := carrier) (comp_mem unit_mem unit_mem) ⟨_, hxy, hyz⟩

/-- The relation algebra on a family of relations satisfying the proper relation algebra axioms. -/
instance relationAlgebra : RelationAlgebra carrier where
  __ := Subtype.distribLattice (fun _ _ hR hS => toIsSetRing.union_mem hR hS)
    (fun _ _ hR hS => toIsSetRing.inter_mem hR hS)
  top := ⟨unit, unit_mem⟩
  bot := ⟨∅, toIsSetRing.empty_mem⟩
  compl R := ⟨unit \ R.val, toIsSetRing.sdiff_mem unit_mem R.property⟩
  le_top R := subset_unit R.property
  bot_le _ := Set.empty_subset _
  inf_compl_le_bot _ _ h := h.2.2 h.1
  top_le_sup_compl R p hp := by
    classical
    exact (em (p ∈ R.val)).elim Or.inl (fun h => Or.inr ⟨hp, h⟩)
  sdiff_eq _ _ := rfl
  himp_eq _ _ := rfl

  one := ⟨SetRel.id, id_mem⟩
  mul R S := ⟨SetRel.comp R.val S.val, comp_mem R.property S.property⟩
  mul_assoc _ _ _ := Subtype.ext (SetRel.comp_assoc _ _ _)
  one_mul _ := Subtype.ext (SetRel.id_comp _)
  mul_one _ := Subtype.ext (SetRel.comp_id _)

  star R := ⟨SetRel.inv R.val, inv_mem R.property⟩
  star_involutive _ := Subtype.ext SetRel.inv_inv
  star_mul _ _ := Subtype.ext (SetRel.inv_comp _ _)

  sup_mul _ _ _ := by
    apply Subtype.ext
    ext ⟨x, z⟩
    exact (exists_congr fun y => or_and_right).trans exists_or
  star_sup _ _ := rfl
  tarski R S p hp := by
    refine ⟨subset_unit
      (comp_mem (inv_mem R.property)
        (toIsSetRing.sdiff_mem unit_mem (comp_mem R.property S.property))) hp, ?_⟩
    rcases hp with ⟨y, hyx, hyz⟩
    exact fun hxz => hyz.2 ⟨p.1, hyx, hxz⟩

/-- Restrict each relation to the equivalence class containing `x`. -/
def restrictHom (x : α) :
    RelationAlgebraHom carrier (SquareRelations {y : α // (x, y) ∈ unit}) :=
  { toFun R := {p | (p.1.val, p.2.val) ∈ R.val}
    map_sup' _ _ := rfl
    map_inf' _ _ := rfl
    map_bot' := rfl
    map_top' := by
      apply Set.eq_univ_of_forall
      intro p
      exact (unit_equivalence (carrier := carrier)).trans
        ((unit_equivalence (carrier := carrier)).symm p.1.property) p.2.property
    map_one' := by
      apply Set.ext
      intro p
      change p.1.val = p.2.val ↔ p.1 = p.2
      exact ⟨Subtype.ext, congrArg Subtype.val⟩
    map_star' _ := rfl
    map_mul' R S := by
      apply Set.ext
      rintro ⟨y, z⟩
      change (∃ m : α, (y.val, m) ∈ R.val ∧ (m, z.val) ∈ S.val) ↔
        ∃ m : {m : α // (x, m) ∈ unit}, (y.val, m.val) ∈ R.val ∧ (m.val, z.val) ∈ S.val
      constructor
      · rintro ⟨m, hym, hmz⟩
        refine ⟨⟨m, ?_⟩, hym, hmz⟩
        exact (unit_equivalence (carrier := carrier)).trans y.property (subset_unit R.property hym)
      · rintro ⟨m, hym, hmz⟩
        exact ⟨m.val, hym, hmz⟩ }

@[simp]
theorem restrictHom_apply (x : α) (R : carrier) :
    restrictHom x R =
      ({p | (p.1.val, p.2.val) ∈ R.val} :
        SetRel {y : α // (x, y) ∈ unit} {y : α // (x, y) ∈ unit}) := rfl

/-- A proper relation algebra is represented by restriction to its equivalence classes.
The classes are indexed by base points, so the same class may occur more than once. -/
def toRepresentation :
    Representation carrier α (fun x => {y : α // (x, y) ∈ unit}) :=
  { hom := RelationAlgebraHom.pi restrictHom
    injective := by
      intro R S hRS
      apply Subtype.ext
      apply Set.ext
      rintro ⟨x, y⟩
      constructor
      · intro hxy
        have hE := subset_unit R.property hxy
        have heq := congrFun hRS x
        exact (Set.ext_iff.mp heq
          (⟨x, (unit_equivalence (carrier := carrier)).refl x⟩, ⟨y, hE⟩)).mp hxy
      · intro hxy
        have hE := subset_unit S.property hxy
        have heq := congrFun hRS x
        exact (Set.ext_iff.mp heq
          (⟨x, (unit_equivalence (carrier := carrier)).refl x⟩, ⟨y, hE⟩)).mpr hxy }

@[simp]
theorem toRepresentation_hom_apply (R : carrier) (x : α) :
    toRepresentation.hom R x = restrictHom x R := rfl

end ProperRelationAlgebra

section Pi

variable {ι : Type v} (β : ι → Type w)

/-- The same-component relation on the disjoint union. -/
def sigmaUnit : SetRel (Σ i, β i) (Σ i, β i) := {p | p.1.1 = p.2.1}

/-- The full proper relation algebra with same-component unit. -/
instance pi_proper : ProperRelationAlgebra {R | R ⊆ sigmaUnit β} (sigmaUnit β) where
  empty_mem := Set.empty_subset _
  union_mem _ _ hR hS := Set.union_subset hR hS
  sdiff_mem _ _ hR _ := Set.Subset.trans Set.sdiff_subset hR
  subset_unit := fun h => h
  unit_mem := Set.Subset.refl _
  id_mem := by rintro ⟨x, y⟩ h; exact congrArg Sigma.fst h
  inv_mem hR := fun _ h => (hR h).symm
  comp_mem hR hS := by
    rintro ⟨x, z⟩ ⟨y, hxy, hyz⟩
    exact (hR hxy).trans (hS hyz)

variable {β}

/-- Join a family of square relations on a disjoint union. -/
private def piRelation (R : ∀ i, SquareRelations (β i)) : SetRel (Σ i, β i) (Σ i, β i) :=
  {p | ∃ (i : ι) (x y : β i), p = (⟨i, x⟩, ⟨i, y⟩) ∧
    (let r : SetRel (β i) (β i) := R i; (x, y) ∈ r)}

private theorem piRelation_subset (R : ∀ i, SquareRelations (β i)) :
    piRelation R ⊆ sigmaUnit β := by
  rintro _ ⟨i, x, y, rfl, _⟩
  rfl

private theorem mem_piRelation (R : ∀ i, SquareRelations (β i)) (i : ι) (x y : β i) :
    (⟨i, x⟩, ⟨i, y⟩) ∈ piRelation R ↔
      (let r : SetRel (β i) (β i) := R i; (x, y) ∈ r) := by
  constructor
  · rintro ⟨j, u, v, hp, huv⟩
    have hij : i = j := congrArg (fun p => p.1.1) hp
    subst j
    have hx : x = u := eq_of_heq (Sigma.mk.inj_iff.mp (congrArg Prod.fst hp)).2
    have hy : y = v := eq_of_heq (Sigma.mk.inj_iff.mp (congrArg Prod.snd hp)).2
    cases hx
    cases hy
    exact huv
  · intro h
    exact ⟨i, x, y, rfl, h⟩

/-- Restrict a relation on the disjoint union to each component. -/
private def piRestrict (S : SetRel (Σ i, β i) (Σ i, β i)) : ∀ i, SquareRelations (β i) :=
  fun i => {p : β i × β i | (⟨i, p.1⟩, ⟨i, p.2⟩) ∈ S}

private theorem piRestrict_piRelation (R : ∀ i, SquareRelations (β i)) :
    piRestrict (piRelation R) = R := by
  funext i
  apply Set.ext
  rintro ⟨x, y⟩
  exact mem_piRelation R i x y

private theorem piRelation_piRestrict (S : SetRel (Σ i, β i) (Σ i, β i))
    (hS : S ⊆ sigmaUnit β) : piRelation (piRestrict S) = S := by
  ext ⟨⟨i, x⟩, ⟨j, y⟩⟩
  by_cases hij : i = j
  · subst j
    exact mem_piRelation (piRestrict S) i x y
  · constructor
    · intro hp
      exact (hij (piRelation_subset _ hp)).elim
    · intro hp
      exact (hij (hS hp)).elim

private theorem piRelation_le_iff (R S : ∀ i, SquareRelations (β i)) :
    piRelation R ⊆ piRelation S ↔ R ≤ S := by
  constructor
  · intro h i p hp
    exact (mem_piRelation S i p.1 p.2).1 (h ((mem_piRelation R i p.1 p.2).2 hp))
  · rintro h _ ⟨i, x, y, rfl, hxy⟩
    exact ⟨i, x, y, rfl, h i hxy⟩

private theorem piRelation_star (R : ∀ i, SquareRelations (β i)) :
    piRelation (star R) = SetRel.inv (piRelation R) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨i, x, y, rfl, h⟩
    exact ⟨i, y, x, rfl, h⟩
  · rintro ⟨a, b⟩ ⟨i, x, y, hp, h⟩
    exact ⟨i, y, x, congrArg Prod.swap hp, h⟩

private theorem piRelation_mul (R S : ∀ i, SquareRelations (β i)) :
    piRelation (R * S) = SetRel.comp (piRelation R) (piRelation S) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨i, x, z, rfl, y, hxy, hyz⟩
    exact ⟨⟨i, y⟩, ⟨i, x, y, rfl, hxy⟩, ⟨i, y, z, rfl, hyz⟩⟩
  · rintro ⟨a, c⟩ ⟨b, ⟨i, x, y, hxy, hr⟩, ⟨j, u, v, huv, hs⟩⟩
    rcases Prod.mk.inj hxy with ⟨rfl, rfl⟩
    have hij : i = j := congrArg (fun p => p.1.1) huv
    subst j
    have hyu : y = u := eq_of_heq (Sigma.mk.inj_iff.mp (congrArg Prod.fst huv)).2
    subst u
    have hc : c = ⟨i, v⟩ := congrArg Prod.snd huv
    subst c
    exact ⟨i, x, v, rfl, y, hr, hs⟩

/-- A product of square relation algebras is the full proper relation algebra on its
disjoint union. See Ian Hodkinson, *An application of first-order compactness in canonicity of
relation algebras* (2019), §2.2, https://www.doc.ic.ac.uk/~imh/papers/mara.pdf#page=4. -/
def piEquivProper (β : ι → Type w) :
    RelationAlgebraEquiv (∀ i, SquareRelations (β i)) {R | R ⊆ sigmaUnit β} :=
  private_decl% {
    toFun R := ⟨piRelation R, piRelation_subset R⟩
    invFun S := piRestrict S.val
    left_inv := piRestrict_piRelation
    right_inv := fun S => Subtype.ext (piRelation_piRestrict S.val S.property)
    map_rel_iff' := fun {R S} => piRelation_le_iff R S
    map_mul' := fun R S => Subtype.ext (piRelation_mul R S)
    map_star' := fun R => Subtype.ext (piRelation_star R)
  }

/-- The product isomorphism sends component relations to their tagged copies. -/
@[simp]
theorem mem_piEquivProper (R : ∀ i, SquareRelations (β i)) (i : ι) (x y : β i) :
    (⟨i, x⟩, ⟨i, y⟩) ∈ (piEquivProper β R).val ↔
      (let r : SetRel (β i) (β i) := R i; (x, y) ∈ r) :=
  mem_piRelation R i x y

end Pi

namespace Representation

variable {α : Type u} [RelationAlgebra α] {ι : Type v} {β : ι → Type w}
  (ρ : Representation α ι β)

/-- The concrete relation assigned by a representation on the disjoint union of its bases. -/
def relation (a : α) : SetRel (Σ i, β i) (Σ i, β i) :=
  (piEquivProper β (ρ.hom a)).val

@[simp]
theorem mem_relation (a : α) (i : ι) (x y : β i) :
    (⟨i, x⟩, ⟨i, y⟩) ∈ ρ.relation a ↔
      (let R : SetRel (β i) (β i) := ρ.hom a i; (x, y) ∈ R) :=
  mem_piEquivProper (ρ.hom a) i x y

/-- The image of a representation is a proper relation algebra. -/
instance proper : ProperRelationAlgebra (Set.range ρ.relation) (sigmaUnit β) := by
  let f := (piEquivProper β).toHom.comp ρ.hom
  change ProperRelationAlgebra (Set.range fun a => (f a).val) (sigmaUnit β)
  refine
    { empty_mem := ⟨⊥, congrArg Subtype.val (map_bot f)⟩
      union_mem := ?_
      sdiff_mem := ?_
      subset_unit := ?_
      unit_mem := ⟨⊤, congrArg Subtype.val (map_top f)⟩
      id_mem := ⟨1, congrArg Subtype.val (map_one f)⟩
      inv_mem := ?_
      comp_mem := ?_ }
  · rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a ⊔ b, congrArg Subtype.val (map_sup f a b)⟩
  · rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    refine ⟨a ⊓ bᶜ, ?_⟩
    change (f (a ⊓ bᶜ)).val = _
    rw [map_inf, map_compl']
    ext p
    exact ⟨fun hp => ⟨hp.1, hp.2.2⟩, fun hp => ⟨hp.1, (f a).property hp.1, hp.2⟩⟩
  · rintro _ ⟨a, rfl⟩
    exact (f a).property
  · rintro _ ⟨a, rfl⟩
    exact ⟨star a, congrArg Subtype.val (map_star f a)⟩
  · rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a * b, congrArg Subtype.val (map_mul f a b)⟩

/-- A representation is an isomorphism onto its proper relation algebra of concrete relations. -/
noncomputable def equivProper : RelationAlgebraEquiv α (Set.range ρ.relation) := by
  let f := (piEquivProper β).toHom.comp ρ.hom
  have hf : Function.Injective f := (piEquivProper β).injective.comp ρ.injective
  have hr : Function.Injective ρ.relation := fun _ _ hab => hf (Subtype.ext hab)
  refine
    { Equiv.ofInjective ρ.relation hr with
      map_rel_iff' := ?_
      map_mul' := ?_
      map_star' := ?_ }
  · change ∀ {a b}, (f a).val ⊆ (f b).val ↔ a ≤ b
    exact (orderEmbeddingOfInjective f hf).map_rel_iff
  · intro a b
    apply Subtype.ext
    change (f (a * b)).val = (f a * f b).val
    exact congrArg Subtype.val (map_mul f a b)
  · intro a
    apply Subtype.ext
    change (f (star a)).val = (star (f a)).val
    exact congrArg Subtype.val (map_star f a)

@[simp]
theorem equivProper_apply (a : α) :
    (ρ.equivProper a).val = ρ.relation a := rfl

end Representation

/-- Representability is equivalent to being isomorphic to a proper relation algebra. -/
theorem representable_iff_exists_proper {α : Type u} [RelationAlgebra α] :
    Representable α ↔
      ∃ (X : Type u) (carrier : Set (SetRel X X)) (unit : SetRel X X)
        (_ : ProperRelationAlgebra carrier unit),
        Nonempty (RelationAlgebraEquiv α carrier) := by
  constructor
  · rintro ⟨ι, β, ⟨ρ⟩⟩
    exact ⟨Σ i, β i, Set.range ρ.relation, sigmaUnit β, ρ.proper, ⟨ρ.equivProper⟩⟩
  · rintro ⟨X, carrier, unit, _, ⟨e⟩⟩
    exact ⟨X, (fun x => {y : X // (x, y) ∈ unit}),
      ⟨{ hom := ProperRelationAlgebra.toRepresentation.hom.comp e.toHom
         injective := ProperRelationAlgebra.toRepresentation.injective.comp e.injective }⟩⟩

end Cslib.RelationAlgebra
