/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Cslib.Logics.Modal.Lean.Basic

/-! # Modal Logic for scalar multiplication (SMul)

Any scalar multiplication operation `•` induces an accessibility relation where two elements are
related if the latter is the result of applying a scalar multiplication to the former.

Properties of the operator translate to properties of the relation, for example a semigroup action
on a commutative semigroup yields a relation with the `Diamond` property. This bridge allows for
studying properties of the operation using modal logic.
-/

@[expose] public section

namespace Relation

/-- The accessibility relation induced by a scalar multiplication operation: `x` is related to `y`
when there exists `m` such that `m • x = y`. -/
def ofSMul (M α : Type*) [SMul M α] (x y : α) : Prop := ∃ m : M, m • x = y

/-- The relation induced by a monoid action is reflexive. -/
instance [Monoid M] [MulAction M α] : Std.Refl (ofSMul M α) where
  refl x := by
    use 1
    simp

/-- The relation induced by a semigroup action is transitive. -/
instance [Semigroup M] [SemigroupAction M α] : IsTrans α (ofSMul M α) where
  trans := by
    rintro x _ _ ⟨m, rfl⟩ ⟨n, rfl⟩
    use n * m
    rw [mul_smul]

/-- The relation induced by a group action is symmetric. -/
instance [Group G] [MulAction G α] : Std.Symm (ofSMul G α) where
  symm := by
    rintro x _ ⟨g, rfl⟩
    use g⁻¹
    simp

/-- The relation induced by an action of a nonempty type is serial. -/
instance [SMul M α] [Nonempty M] : Serial (ofSMul M α) where
  serial x := ⟨Classical.arbitrary M • x, Classical.arbitrary M, rfl⟩

/-- TODO: upstream this generalisation of Mathlib's `smulCommClass_self`, which applies only to
monoids `M`. -/
instance {M α} [CommSemigroup M] [SemigroupAction M α] : SMulCommClass M M α where
  smul_comm m n a := by rw [←mul_smul, mul_comm, mul_smul]

/-- The relation induced by an action commuting with itself has the diamond property. -/
@[scoped grind .]
theorem ofSMul_diamond [SMul M α] [SMulCommClass M M α] : Diamond (ofSMul M α) := by
  rintro x _ _ ⟨m, rfl⟩ ⟨n, rfl⟩
  use! n • m • x, n, m, smul_comm ..

/-- Preservation by an action-induced relation is exactly closure under the action. -/
@[scoped grind =]
theorem ofSMul_preserves_iff [SMul M α] {P : α → Prop} :
    Preserves (ofSMul M α) P ↔ ∀ m : M, ∀ x, P x → P (m • x) := by
  constructor
  case mp =>
    intro h m x hx
    exact h ⟨m, rfl⟩ hx
  case mpr =>
    rintro h x y ⟨m, rfl⟩ hx
    exact h m x hx

/-- Membership in a type closed under a scalar action is preserved by the relation induced by the
action. -/
@[scoped grind .]
theorem ofSMul_preserves_mem [SMul M α] [SetLike S α] [SMulMemClass S M α]
    (s : S) : Preserves (ofSMul M α) (· ∈ s) := by
  rw [Relation.ofSMul_preserves_iff]
  apply SMulMemClass.smul_mem

end Relation

namespace Cslib.Logic.Modal.Proposition

/-- Characterisation of the denotation of a `◇p` under `ofSMul`. -/
theorem ofSMul_diamond_denotation [SMul M α] [Membership α β] (p : β) :
    (◇p : Proposition β).denotation (Model.ofContainers (Relation.ofSMul M α)) =
      {x | ∃ m : M, m • x ∈ p} := by
  ext x
  change (∃ y, (∃ m : M, m • x = y) ∧ y ∈ p) ↔ ∃ m : M, m • x ∈ p
  grind

/-- For `SetLike` objects closed under a commutative semigroup action, simultaneous reachability is
equivalent to separate reachability. -/
theorem ofSMul_diamond_and_equiv [CommSemigroup M] [SemigroupAction M α] [SetLike S α]
    [SMulMemClass S M α] (p q : S) :
    ◇(p ∧ q : Proposition S) ≡[Equiv.OfContainers (Relation.ofSMul M α)] (◇p ∧ ◇q) :=
  diamond_and_equiv_of_preserves Relation.ofSMul_diamond
    (Relation.ofSMul_preserves_mem p)
    (Relation.ofSMul_preserves_mem q)

end Cslib.Logic.Modal.Proposition
