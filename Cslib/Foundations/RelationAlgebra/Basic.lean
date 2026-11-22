/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.Order.Huntington
public import Cslib.Init
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Quantale
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Rel
public import Mathlib.Order.Atoms

/-!
# Relation algebras

A relation algebra in the sense of Tarski (not to be confused with a relational algebra) is an
extension of Boolean algebras that are designed to form an algebraic analysis of relations,
`α → α → Prop` in Lean. They have applications in computer science such as the theory of constraint
satisfaction as well as mathematical connections such as combinatorics.

## References

* [R. Maddux, *Relation Algebras*][Maddux2006]

-/

@[expose] public section

namespace Cslib

/-- The class of relation algebras. Note the notational differences from the literature. In addition
to inheriting Mathlib's notations for Boolean algebras, `star` is used for converse, and the monoid
reduct for composition uses multiplicative notation. -/
class RelationAlgebra (α : Type*) extends BooleanAlgebra α, Monoid α, StarMul α where
  sup_mul (a b c : α) : (a ⊔ b) * c = a * c ⊔ b * c
  star_sup (a b : α) : star (a ⊔ b) = star a ⊔ star b
  tarski (a b : α) : star a * (a * b)ᶜ ≤ bᶜ

attribute [simp] RelationAlgebra.star_sup
attribute [push] RelationAlgebra.star_sup StarMul.star_mul star_star

/-- The relation algebra of a complete Boolean algebra. -/
class CompleteRelationAlgebra (α : Type*) extends RelationAlgebra α, CompleteBooleanAlgebra α

/-- The relation algebra of a complete and atomic Boolean algebra. -/
class CompleteAtomicRelationAlgebra (α : Type*) extends CompleteRelationAlgebra α,
    CompleteAtomicBooleanAlgebra α

namespace RelationAlgebra

/-- A `RelationAlgebra` can be constructed using Tarski's original ten axioms. -/
@[instance_reducible]
def ofTarski {α : Type*} [Max α] [Compl α] [Mul α] [One α] [Star α]
    (sup_comm : ∀ a b : α, a ⊔ b = b ⊔ a)
    (sup_assoc : ∀ a b c : α, (a ⊔ b) ⊔ c = a ⊔ (b ⊔ c))
    (huntington : ∀ a b : α, (aᶜ ⊔ b)ᶜ ⊔ (aᶜ ⊔ bᶜ)ᶜ = a)
    (mul_assoc : ∀ a b c : α, (a * b) * c = a * (b * c))
    (mul_one : ∀ a : α, a * 1 = a)
    (star_involutive : ∀ a : α, star (star a) = a)
    (star_mul : ∀ a b : α, star (a * b) = star b * star a)
    (sup_mul : ∀ a b c : α, (a ⊔ b) * c = a * c ⊔ b * c)
    (star_sup : ∀ a b : α, star (a ⊔ b) = star a ⊔ star b)
    (tarski : ∀ a b : α, star a * (a * b)ᶜ ⊔ bᶜ = bᶜ) : RelationAlgebra α where
  __ := @HuntingtonAlgebra.instBooleanAlgebra α {
    default := 1
    assoc := sup_assoc
    comm := sup_comm
    huntington := huntington
  }
  mul_assoc := mul_assoc
  mul_one := mul_one
  one_mul a := by
    suffices star (1 : α) = 1 by
      rw [← star_involutive (1 * a), star_mul, this, mul_one, star_involutive]
    rw [← star_involutive (star 1), ← mul_one (star 1), star_mul, star_involutive, mul_one,
      star_involutive]
  star_involutive := star_involutive
  star_mul := star_mul
  sup_mul := sup_mul
  star_sup := star_sup
  tarski := tarski

variable {α : Type*} [RelationAlgebra α]

@[gcongr]
theorem star_mono : Monotone (star : α → α) := by
  intro a b h
  rw [← sup_eq_right, ← star_sup, sup_of_le_right h]

/-- Converse as an automorphism of a relation algebra. -/
@[simps! apply symm_apply]
def starOrderIso : α ≃o α := Equiv.Perm.star.toOrderIso star_mono star_mono

attribute [to_dual existing] BooleanAlgebra.toBot

@[to_dual (attr := simp, push)]
theorem star_bot : star (⊥ : α) = ⊥ := (starOrderIso : α ≃o α).map_bot

@[simp, to_dual self]
theorem star_le_star_iff {a b : α} : star a ≤ star b ↔ a ≤ b := starOrderIso.le_iff_le

@[simp, to_dual self]
theorem star_lt_star_iff {a b : α} : star a < star b ↔ a < b := starOrderIso.lt_iff_lt

@[to_dual star_le_iff]
theorem le_star_iff {a b : α} : a ≤ star b ↔ star a ≤ b := starOrderIso.le_symm_apply

@[to_dual existing (attr := simp, push)]
theorem star_inf (a b : α) : star (a ⊓ b) = star a ⊓ star b := starOrderIso.map_inf a b

@[simp, push]
theorem star_compl (a : α) : star aᶜ = (star a)ᶜ :=
  (starOrderIso.isCompl isCompl_compl).compl_eq.symm

@[simp, push]
theorem star_sdiff (a b : α) : star (a \ b) = star a \ star b := by
  rw [sdiff_eq, star_inf, star_compl, sdiff_eq]

@[to_dual (attr := simp, push)]
theorem star_sSup {α : Type*} [CompleteRelationAlgebra α] (s : Set α) :
    star (sSup s) = ⨆ a ∈ s, star a := starOrderIso.map_sSup s

theorem mul_sup (a b c : α) : a * (b ⊔ c) = a * b ⊔ a * c := by
  apply star_injective
  simp [star_sup, sup_mul]

instance : MulLeftMono α where
  elim a b c h := by simp [← sup_eq_right, ← mul_sup, sup_of_le_right h]

instance : MulRightMono α where
  elim a b c h := by simp [← sup_eq_right, ← sup_mul, sup_of_le_right h]

@[simp]
theorem mul_bot (a : α) : a * ⊥ = ⊥ :=
  eq_bot_mono (mul_le_mul_right bot_le a) (by simpa using tarski (star a) ⊤)

theorem inf_mul_le (a b c : α) : (a ⊓ b) * c ≤ a * c ⊓ b * c := by
  nth_grw 1 [le_inf_iff, inf_le_left, inf_le_right]
  exact ⟨le_rfl, le_rfl⟩

theorem mul_inf_le (a b c : α) : a * (b ⊓ c) ≤ a * b ⊓ a * c := by
  nth_grw 1 [le_inf_iff, inf_le_left, inf_le_right]
  exact ⟨le_rfl, le_rfl⟩

@[to_dual (attr := simp)]
theorem isAtom_star_iff {a : α} : IsAtom (star a) ↔ IsAtom a :=
  starOrderIso.isAtom_iff a

theorem left_modular (a b c : α) : a * b ⊓ c ≤ a * (b ⊓ star a * c) :=
  calc
    a * b ⊓ c = (a * (b ⊓ star a * c) ⊔ a * (b ⊓ (star a * c)ᶜ)) ⊓ c := by
      rw [← mul_sup, ← inf_sup_left, sup_compl_eq_top, inf_top_eq]
    _ ≤ (a * (b ⊓ star a * c) ⊔ a * (star a * c)ᶜ) ⊓ c := by gcongr; exact inf_le_right
    _ ≤ (a * (b ⊓ star a * c) ⊔ cᶜ) ⊓ c := by grw [← tarski (star a) c, star_star]
    _ = a * (b ⊓ star a * c) ⊓ c := by rw [inf_sup_right, compl_inf_self, sup_bot_eq]
    _ ≤ a * (b ⊓ star a * c) := inf_le_left

theorem right_modular (a b c : α) : a * b ⊓ c ≤ (a ⊓ c * star b) * b := by
  rw [← star_le_star_iff]
  simpa using left_modular (star b) (star a) (star c)

theorem mul_le_compl_right (a b c : α) : a * b ≤ cᶜ ↔ star a * c ≤ bᶜ := by
  have h (x y z : α) (h : x * y ≤ zᶜ) : star x * z ≤ yᶜ := by grw [← tarski x y, h, compl_compl]
  refine ⟨h a b c, ?_⟩
  simpa using h (star a) c b

theorem mul_le_compl_left (a b c : α) : a * b ≤ cᶜ ↔ c * star b ≤ aᶜ := by
  refine (star_le_star_iff.symm.trans ?_).trans star_le_star_iff
  simpa using mul_le_compl_right (star b) (star a) (star c)

theorem mul_le_compl_star_tfae {a b c : α} :
    [a * b ≤ (star c)ᶜ, b * c ≤ (star a)ᶜ, c * a ≤ (star b)ᶜ].TFAE := by
  tfae_have 1 ↔ 2 := by
    rw [← star_compl, le_star_iff, star_mul, mul_le_compl_right, star_star]
  tfae_have 2 ↔ 3 := by
    rw [← star_compl, le_star_iff, star_mul, mul_le_compl_right, star_star]
  tfae_finish

/-- The right residual, defined so that `a ≤ leftResidual b c ↔ a * b ≤ c`. -/
def leftResidual (a b : α) : α := (bᶜ * star a)ᶜ

theorem le_leftResidual_iff {a b c : α} : a ≤ leftResidual b c ↔ a * b ≤ c := by
  rw [leftResidual, le_compl_comm, ← mul_le_compl_left, compl_compl]

/-- The left residual, defined so that `a ≤ rightResidual b c ↔ b * a ≤ c`. -/
def rightResidual (a b : α) : α := (star a * bᶜ)ᶜ

theorem le_rightResidual_iff {a b c : α} : a ≤ rightResidual b c ↔ b * a ≤ c := by
  rw [rightResidual, le_compl_comm, ← mul_le_compl_right, compl_compl]

@[simp, push]
theorem star_leftResidual {a b : α} :
    star (leftResidual a b) = rightResidual (star a) (star b) := by
  rw [leftResidual, rightResidual]
  push star
  rfl

@[simp, push]
theorem star_rightResidual {a b : α} :
    star (rightResidual a b) = leftResidual (star a) (star b) := by
  rw [rightResidual, leftResidual]
  push star
  rfl

theorem mul_sSup {α : Type*} [CompleteRelationAlgebra α] {a : α} {s : Set α} :
    a * sSup s = ⨆ b ∈ s, a * b := by
  apply eq_of_forall_ge_iff
  simp [← le_rightResidual_iff]

theorem sSup_mul {α : Type*} [CompleteRelationAlgebra α] {s : Set α} {b : α} :
    sSup s * b = ⨆ a ∈ s, a * b := by
  apply eq_of_forall_ge_iff
  simp [← le_leftResidual_iff]

instance instQuantale (α : Type*) [CompleteRelationAlgebra α] : IsQuantale α where
  mul_sSup_distrib _ _ := mul_sSup
  sSup_mul_distrib _ _ := sSup_mul

open Quantale in
theorem leftMulResiduation_eq_leftResidual {α : Type*} [CompleteRelationAlgebra α]
    {a b : α} : a ⇨ₗ b = leftResidual a b := by
  apply eq_of_forall_le_iff
  simp [leftMulResiduation_le_iff_mul_le, le_leftResidual_iff]

open Quantale in
theorem rightMulResiduation_eq_rightResidual {α : Type*} [CompleteRelationAlgebra α]
    {a b : α} : a ⇨ᵣ b = rightResidual a b := by
  apply eq_of_forall_le_iff
  simp [rightMulResiduation_le_iff_mul_le, le_rightResidual_iff]

/-- If a nonzero element lies below a product, the right factor meets its converse image. -/
theorem inf_star_mul_ne_bot {r s p : α} (hp : p ≠ ⊥) (h : p ≤ r * s) : s ⊓ star r * p ≠ ⊥ :=
  fun hbot => hp <| eq_bot_mono ((le_inf h le_rfl).trans (left_modular r s p)) (hbot ▸ mul_bot r)

theorem atom_cycle_left {r s p : α} (hs : IsAtom s) (hp : p ≠ ⊥) (h : p ≤ r * s) :
    s ≤ star r * p :=
  hs.not_disjoint_iff_le.mp <| disjoint_iff.not.mpr <| inf_star_mul_ne_bot hp h

/-- For atoms, the cycle law is an equivalence. -/
theorem atom_cycle_left_iff {r s p : α} (hs : IsAtom s) (hp : IsAtom p) :
    p ≤ r * s ↔ s ≤ star r * p :=
  ⟨atom_cycle_left hs hp.ne_bot, fun h => by simpa using atom_cycle_left hp hs.ne_bot h⟩

/-- If an atom lies below a product, its right factor can be replaced by an atom below it. -/
theorem exists_atom_le_mul_right [IsAtomic α] {a b p : α} (hp : IsAtom p) (h : p ≤ a * b) :
    ∃ s, IsAtom s ∧ s ≤ b ∧ p ≤ a * s := by
  obtain ⟨s, hs, hsb⟩ :=
    (eq_bot_or_exists_atom_le _).resolve_left (inf_star_mul_ne_bot hp.ne_bot h)
  exact ⟨s, hs, hsb.trans inf_le_left, (atom_cycle_left_iff hs hp).mpr (hsb.trans inf_le_right)⟩

/-- If an atom lies below a product, its left factor can be replaced by an atom below it. -/
theorem exists_atom_le_mul_left [IsAtomic α] {a b p : α} (hp : IsAtom p) (h : p ≤ a * b) :
    ∃ r, IsAtom r ∧ r ≤ a ∧ p ≤ r * b := by
  obtain ⟨s, hs, hsa, hps⟩ :=
    exists_atom_le_mul_right (isAtom_star_iff.mpr hp) (by simpa using star_mono h)
  exact ⟨star s, isAtom_star_iff.mpr hs, by simpa using star_mono hsa, by simpa using star_mono hps⟩

/-- A relation algebra is *integral* when its identity is an atom. -/
def IsIntegral (α : Type*) [RelationAlgebra α] : Prop := IsAtom (1 : α)

/-- The set of identity atoms. -/
def identityAtoms (α : Type*) [RelationAlgebra α] : Set α := {a : α | IsAtom a ∧ a ≤ 1}

/-- The set of symmetric diversity atoms, those below the complement of identity. -/
def symmetricDiversityAtoms (α : Type*) [RelationAlgebra α] : Set α :=
  {a : α | IsAtom a ∧ a ≤ 1ᶜ ∧ star a = a}

/-- The set of nonsymmetric diversity atoms. The diversity condition follows from
`le_compl_one_of_mem_nonsymmetricDiversityAtoms`. -/
def nonsymmetricDiversityAtoms (α : Type*) [RelationAlgebra α] : Set α :=
  {a : α | IsAtom a ∧ star a ≠ a}

/-- Every nonsymmetric atom lies below the complement of identity. -/
theorem le_compl_one_of_mem_nonsymmetricDiversityAtoms {a : α}
    (h : a ∈ nonsymmetricDiversityAtoms α) : a ≤ 1ᶜ := by
  rw [le_compl_iff_disjoint_right, ← h.1.not_le_iff_disjoint]
  intro ha
  have hstar : a ≤ star a := by calc
     a = a * 1 ⊓ 1 := by rw [mul_one, inf_eq_left.mpr ha]
     _ ≤ a * (1 ⊓ star a * 1) := left_modular a 1 1
     _ ≤ 1 * (1 ⊓ star a * 1) := mul_le_mul_left ha _
     _ = 1 ⊓ star a := by rw [one_mul, mul_one]
     _ ≤ star a := inf_le_right
  have : star a ≤ a := by calc
    star a ≤ star (star a) := star_mono hstar
    _ = a := star_star a
  cases h
  grind

/-- The relation algebra of all binary relations on a type `α`. This is scoped so that other
instances, such as those under `Pointwise`, can be used elsewhere. -/
scoped instance (α : Type u) : CompleteAtomicRelationAlgebra (SetRel α α) where
  one := SetRel.id
  mul := SetRel.comp
  mul_assoc := SetRel.comp_assoc
  one_mul := SetRel.id_comp
  mul_one := SetRel.comp_id
  star := SetRel.inv
  star_involutive _ := SetRel.inv_inv
  star_mul := SetRel.inv_comp
  sup_mul a b c := by
    ext ⟨x, z⟩
    exact (exists_congr fun y => or_and_right).trans exists_or
  star_sup _ _ := rfl
  tarski a b := by
    rintro ⟨x, z⟩ ⟨y, hxy, hyz⟩ hxz
    exact hyz ⟨x, hxy, hxz⟩

variable {α : Type u} {R S : SetRel α α} {a b c : α}

theorem _root_.SetRel.mul_eq_comp : R * S = R.comp S := rfl

theorem _root_.SetRel.one_eq_id : (1 : SetRel α α) = SetRel.id := rfl

theorem _root_.SetRel.star_eq_inv : star R = R.inv := rfl

@[simp]
theorem _root_.SetRel.mem_mul : (a, c) ∈ R * S ↔ ∃ b, (a, b) ∈ R ∧ (b, c) ∈ S := .rfl

@[simp]
theorem _root_.SetRel.mem_one : (a, b) ∈ (1 : SetRel α α) ↔ a = b := .rfl

@[simp]
theorem _root_.SetRel.mem_star : (a, b) ∈ star R ↔ (b, a) ∈ R := .rfl

theorem _root_.SetRel.mem_leftResidual :
    (a, b) ∈ leftResidual R S ↔ ∀ c, (b, c) ∈ R → (a, c) ∈ S := by
  simp [leftResidual, not_imp_not]

theorem _root_.SetRel.mem_rightResidual :
    (a, b) ∈ rightResidual R S ↔ ∀ c, (c, a) ∈ R → (c, b) ∈ S := by
  simp [rightResidual]

end RelationAlgebra

end Cslib
