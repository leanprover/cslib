/-
Copyright (c) 2026 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/

module

public import Cslib.Init
public import Mathlib.Order.BooleanAlgebra.Basic

/-!
# Huntington's axioms for Boolean Algebras

In this file we derive an instance of Mathlib's `BooleanAlgebra` on an inhabited type, starting
from operations of binary supremum `· ⊔ ·` and complementation `·ᶜ`, obeying the three axioms
laid out in [Huntington1933a] and [Huntington1933b]:

* Supremum is associative: `a ⊔ b ⊔ c = a ⊔ (b ⊔ c)`,
* Supremum is commutative: `a ⊔ b = b ⊔ a`, and
* Huntington's axiom: `(aᶜ ⊔ b)ᶜ ⊔ (aᶜ ⊔ bᶜ)ᶜ = a`.

These axioms are packaged in the class `HuntingtonAlgebra`, which should only be used for its
instance `HuntingtonAlgebra.instBooleanAlgebra`.

## References

* [E. V. Huntington, "New Sets of Independent Postulates for the Algebra of Logic, With Special
  Reference to Whitehead and Russell's Principia Mathematica"][Huntington1933a]
* [E. V. Huntington, "Boolean Algebra. A Correction"][Huntington1933b]

-/

/-- A class for types obeying Huntington's axioms for Boolean algebras. -/
public class HuntingtonAlgebra (α : Type*) extends Max α, Compl α, Inhabited α,
    Std.Associative (α := α) (· ⊔ ·), Std.Commutative (α := α) (· ⊔ ·) where
  /-- Huntington's axiom. -/
  huntington (a b : α) : (aᶜ ⊔ b)ᶜ ⊔ (aᶜ ⊔ bᶜ)ᶜ = a

namespace HuntingtonAlgebra

variable {α : Type*} [HuntingtonAlgebra α]

public instance : Top α := ⟨default ⊔ defaultᶜ⟩
public instance : Bot α := ⟨⊤ᶜ⟩
public instance : Min α where
  min a b := (aᶜ ⊔ bᶜ)ᶜ

lemma compl_top : (⊤ : α)ᶜ = ⊥ := rfl

lemma sup_compl (a : α) : a ⊔ aᶜ = ⊤ := calc
  a ⊔ aᶜ = (aᶜ ⊔ defaultᶜ)ᶜ ⊔ (aᶜ ⊔ defaultᶜᶜ)ᶜ ⊔ ((aᶜᶜ ⊔ defaultᶜ)ᶜ ⊔ (aᶜᶜ ⊔ defaultᶜᶜ)ᶜ) := by
      simp [huntington]
  _ = (defaultᶜ ⊔ aᶜ)ᶜ ⊔ (defaultᶜ ⊔ aᶜᶜ)ᶜ ⊔ ((defaultᶜᶜ ⊔ aᶜ)ᶜ ⊔ (defaultᶜᶜ ⊔ aᶜᶜ)ᶜ) := by ac_rfl
  _ = default ⊔ defaultᶜ := by simp [huntington]

lemma sup_comm (a b : α) : a ⊔ b = b ⊔ a := Std.Commutative.comm ..

lemma sup_assoc (a b c : α) : a ⊔ b ⊔ c = a ⊔ (b ⊔ c) := Std.Associative.assoc ..

lemma compl_sup (a : α) : aᶜ ⊔ a = ⊤ := by rw [sup_comm, sup_compl]

lemma compl_compl (a : α) : aᶜᶜ = a := by calc
  aᶜᶜ = (aᶜ ⊔ aᶜᶜᶜ)ᶜ ⊔ ⊤ᶜ := by nth_rw 1 [← huntington aᶜᶜ aᶜ, ← sup_compl aᶜᶜ]; ac_rfl
  _ = a := by rw [← sup_compl aᶜ, sup_comm, huntington]

lemma compl_inj : Function.Injective (·ᶜ : α → α) := by
  intro a b (h : aᶜ = bᶜ)
  rw [← compl_compl a, h, compl_compl b]

lemma huntington' (a b : α) : (a ⊔ b)ᶜ ⊔ (a ⊔ bᶜ)ᶜ = aᶜ := by
    rw [← huntington aᶜ b, compl_compl a]

lemma top_sup_top : (⊤ : α) ⊔ ⊤ = ⊤ := by
  have : (⊤ : α)ᶜ = (⊤ ⊔ ⊤)ᶜ ⊔ ⊤ᶜ := by nth_rw 1 [← huntington' ⊤ ⊤, sup_compl ⊤]
  calc
    ⊤ ⊔ ⊤ = ⊤ ⊔ ⊤ ⊔ ⊤ᶜ := by rw [sup_assoc, sup_compl]
    _ = ⊤ ⊔ ⊤ ⊔ (⊤ ⊔ ⊤)ᶜ ⊔ ⊤ᶜ := by nth_rw 1 [this, ← sup_assoc]
    _ = ⊤ := by rw [sup_compl, sup_compl]

lemma bot_sup_bot : (⊥ : α) ⊔ ⊥ = ⊥ := calc
  ⊤ᶜ ⊔ ⊤ᶜ = (⊤ ⊔ ⊤)ᶜ ⊔ (⊤ ⊔ ⊤ᶜ)ᶜ := by rw [top_sup_top, sup_compl]
  _ = ⊤ᶜ := huntington' ⊤ ⊤

lemma bot_sup (a : α) : ⊥ ⊔ a = a :=
  compl_inj <| calc
    (⊤ᶜ ⊔ a)ᶜ = (a ⊔ ⊤ᶜ ⊔ ⊤)ᶜ ⊔ (a ⊔ ⊤ᶜ ⊔ ⊤ᶜ)ᶜ := by nth_rw 1 [← huntington' (⊤ᶜ ⊔ a) ⊤]; ac_rfl
    _ = (a ⊔ ⊤)ᶜ ⊔ (a ⊔ ⊤ᶜ)ᶜ := by rw [sup_assoc, compl_sup, compl_top, sup_assoc, bot_sup_bot]
    _ = aᶜ := huntington' ..

lemma sup_idem (a : α) : a ⊔ a = a :=
  compl_inj <| calc
    (a ⊔ a)ᶜ = (a ⊔ a)ᶜ ⊔ (a ⊔ aᶜ)ᶜ := by rw [sup_compl, compl_top, sup_comm _ ⊥, bot_sup]
    _ = aᶜ := huntington' a a

instance : Std.IdempotentOp (α := α) (· ⊔ ·) := ⟨sup_idem⟩

lemma sup_top (a : α) : a ⊔ ⊤ = ⊤ := by
  nth_rw 1 [← sup_compl a, ← sup_assoc, sup_idem a, sup_compl]

lemma sup_compl_eq (a b : α) : a ⊔ bᶜ = a ⊔ (a ⊔ b)ᶜ := calc
  a ⊔ bᶜ = (aᶜ ⊔ b)ᶜ ⊔ (aᶜ ⊔ bᶜ)ᶜ ⊔ (b ⊔ a)ᶜ ⊔ (b ⊔ aᶜ)ᶜ := by
      rw [huntington, sup_assoc, huntington']
  _ = (aᶜ ⊔ b)ᶜ ⊔ (aᶜ ⊔ bᶜ)ᶜ ⊔ (a ⊔ b)ᶜ := by grind
  _ = a ⊔ (a ⊔ b)ᶜ := by rw [huntington]

lemma inf_eq (a b : α) : a ⊓ b = (aᶜ ⊔ bᶜ)ᶜ := rfl

lemma inf_assoc (a b c : α) : a ⊓ b ⊓ c = a ⊓ (b ⊓ c) := by simp [inf_eq, compl_compl, sup_assoc]

lemma inf_comm (a b : α) : a ⊓ b = b ⊓ a := congr($(sup_comm aᶜ bᶜ)ᶜ)

lemma sup_inf_self (a b : α) : a ⊔ (a ⊓ b) = a := by
  rw [inf_eq, sup_compl_eq, ← sup_assoc, sup_compl, sup_comm ⊤, sup_top,
    compl_top, sup_comm, bot_sup]

lemma inf_sup_self (a b : α) : a ⊓ (a ⊔ b) = a := calc
  a ⊓ (a ⊔ b) = (aᶜ ⊔ (aᶜ ⊓ bᶜ))ᶜ := by simp [inf_eq, compl_compl]
  _ = a := by rw [sup_inf_self, compl_compl]

lemma inf_compl (a : α) : a ⊓ aᶜ = ⊥ := by rw [inf_eq, compl_compl, compl_sup, compl_top]

/-- Huntington algebras are Boolean algebras. -/
public instance : BooleanAlgebra α where
  __ := Lattice.mk' (α := α) (private_decl% sup_comm) (private_decl% sup_assoc)
    (private_decl% inf_comm) (private_decl% inf_assoc) (private_decl% sup_inf_self)
    (private_decl% inf_sup_self)
  le_sup_inf a b c := by
    suffices a ⊔ b ⊓ c = a ⊔ (a ⊔ b) ⊓ (a ⊔ c) from this ▸ le_sup_right
    calc
      a ⊔ (bᶜ ⊔ cᶜ)ᶜ = a ⊔ (a ⊔ bᶜ ⊔ cᶜ)ᶜ := by rw [sup_compl_eq, sup_assoc]
      _ = a ⊔ (a ⊔ bᶜ ⊔ (a ⊔ cᶜ))ᶜ := by ac_rfl
      _ = a ⊔ (a ⊔ (a ⊔ b)ᶜ ⊔ (a ⊔ c)ᶜ)ᶜ := by rw [sup_compl_eq a b, sup_compl_eq a c]; grind
      _ = a ⊔ (a ⊔ b) ⊓ (a ⊔ c) := by rw [sup_assoc, ← sup_compl_eq, inf_eq]
  inf_compl_le_bot a := private_decl% (inf_compl a).le
  top_le_sup_compl a := private_decl% (sup_compl a).ge
  le_top := private_decl% sup_top
  bot_le := private_decl% bot_sup

end HuntingtonAlgebra

/-- Conversely, Boolean Algebras obey Huntington's axiom. -/
theorem huntington {α : Type*} [BooleanAlgebra α] (a b : α) : (aᶜ ⊔ b)ᶜ ⊔ (aᶜ ⊔ bᶜ)ᶜ = a := by
  simp [← inf_sup_left]
