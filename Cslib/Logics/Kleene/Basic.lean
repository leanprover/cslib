/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

module

public import Cslib.Init
public import Mathlib.Order.BoundedOrder.Lattice
public import Mathlib.Order.Lattice
public import Mathlib.Tactic.DeriveFintype

/-! # Truth values of Kleene's strong three-valued logic

The truth values of Kleene's strong three-valued logic (K3) [Kleene1952], as an algebra: a bounded
linear order `false < unknown < true`, the truth order, with a complement. Meet `⊓`, join `⊔` and
complement `ᶜ` are Kleene's conjunction, disjunction and negation.

These are also the truth values of SQL [Codd1979], where a comparison involving `NULL` evaluates
to `unknown`, and `AND`, `OR` and `NOT` are the meet, join and complement defined here.

## Main definitions

- `Kleene.Value`: the three truth values.
- `Compl Kleene.Value`: the complement, which swaps `true` and `false` and fixes `unknown`.
- `Kleene.Value.ofBool`: the embedding of `Bool`.

## Main results

- `LinearOrder Kleene.Value`, `BoundedOrder Kleene.Value`: the truth order.
- `Kleene.Value.compl_inf`, `Kleene.Value.compl_sup`: the De Morgan laws.
- `Kleene.Value.ofBool_and` and friends: `ofBool` commutes with the operations.

## References

- [Kleene1952] S. C. Kleene, *Introduction to Metamathematics*, §64.
- [Codd1979] E. F. Codd, *Extending the database relational model to capture more meaning*.
-/

@[expose] public section

namespace Cslib.Logic.Kleene

-- Needed by the `Fintype` derive handler, as for Mathlib's `SignType`.
set_option backward.isDefEq.respectTransparency false in
/-- A truth value of Kleene's strong three-valued logic. -/
inductive Value where
  | true
  | false
  | unknown
  deriving DecidableEq, Repr, Fintype

namespace Value

/-! ### The truth order -/

/-- The truth order `false < unknown < true`. -/
instance : LE Value := ⟨fun a b => a = b ∨ a = .false ∨ b = .true⟩

theorem le_def {a b : Value} : a ≤ b ↔ a = b ∨ a = .false ∨ b = .true := Iff.rfl

instance : DecidableLE Value := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

instance : LinearOrder Value where
  le_refl _ := Or.inl rfl
  le_trans := by decide
  le_antisymm := by decide
  le_total := by decide
  toDecidableLE := inferInstance
  toDecidableEq := inferInstance

instance : BoundedOrder Value where
  top := .true
  le_top _ := Or.inr (Or.inr rfl)
  bot := .false
  bot_le _ := Or.inr (Or.inl rfl)

@[simp, scoped grind =] theorem top_eq_true : (⊤ : Value) = .true := rfl
@[simp, scoped grind =] theorem bot_eq_false : (⊥ : Value) = .false := rfl

theorem false_lt_unknown : (.false : Value) < .unknown := by decide

theorem unknown_lt_true : (.unknown : Value) < .true := by decide

/-! ### Meet and join -/

@[simp, scoped grind =] theorem false_inf (a : Value) : .false ⊓ a = .false := bot_inf_eq a
@[simp, scoped grind =] theorem inf_false (a : Value) : a ⊓ .false = .false := inf_bot_eq a
@[simp, scoped grind =] theorem true_inf (a : Value) : .true ⊓ a = a := top_inf_eq a
@[simp, scoped grind =] theorem inf_true (a : Value) : a ⊓ .true = a := inf_top_eq a

@[simp, scoped grind =] theorem true_sup (a : Value) : .true ⊔ a = .true := top_sup_eq a
@[simp, scoped grind =] theorem sup_true (a : Value) : a ⊔ .true = .true := sup_top_eq a
@[simp, scoped grind =] theorem false_sup (a : Value) : .false ⊔ a = a := bot_sup_eq a
@[simp, scoped grind =] theorem sup_false (a : Value) : a ⊔ .false = a := sup_bot_eq a

@[simp] theorem inf_eq_true_iff {a b : Value} : a ⊓ b = .true ↔ a = .true ∧ b = .true :=
  inf_eq_top_iff

@[simp] theorem sup_eq_true_iff {a b : Value} : a ⊔ b = .true ↔ a = .true ∨ b = .true :=
  max_eq_top

@[simp] theorem sup_eq_false_iff {a b : Value} : a ⊔ b = .false ↔ a = .false ∧ b = .false :=
  sup_eq_bot_iff

/-! ### Complement -/

/-- The complement swaps `true` and `false` and fixes `unknown`. -/
instance : Compl Value where
  compl
    | .true => .false
    | .false => .true
    | .unknown => .unknown

@[simp, scoped grind =] theorem compl_true : (Value.true)ᶜ = .false := rfl
@[simp, scoped grind =] theorem compl_false : (Value.false)ᶜ = .true := rfl
@[simp, scoped grind =] theorem compl_unknown : (Value.unknown)ᶜ = .unknown := rfl

@[simp, scoped grind =] protected theorem compl_compl (a : Value) : aᶜᶜ = a := by decide +revert

@[simp] theorem compl_eq_true_iff {a : Value} : aᶜ = .true ↔ a = .false := by decide +revert

@[simp] theorem compl_eq_false_iff {a : Value} : aᶜ = .false ↔ a = .true := by decide +revert

/-- The complement reverses the truth order. -/
theorem compl_antitone : Antitone fun a : Value => aᶜ := by decide

protected theorem compl_inf (a b : Value) : (a ⊓ b)ᶜ = aᶜ ⊔ bᶜ := compl_antitone.map_min
protected theorem compl_sup (a b : Value) : (a ⊔ b)ᶜ = aᶜ ⊓ bᶜ := compl_antitone.map_max

/-! ### The embedding of `Bool` -/

/-- The embedding of `Bool`. -/
def ofBool : Bool → Value
  | Bool.true => .true
  | Bool.false => .false

@[simp, scoped grind =] theorem ofBool_true : ofBool Bool.true = .true := rfl
@[simp, scoped grind =] theorem ofBool_false : ofBool Bool.false = .false := rfl

theorem ofBool_injective : Function.Injective ofBool := by decide

@[simp] theorem ofBool_inj {a b : Bool} : ofBool a = ofBool b ↔ a = b := ofBool_injective.eq_iff

@[simp] theorem ofBool_ne_unknown (b : Bool) : ofBool b ≠ .unknown := by decide +revert

@[simp, scoped grind =]
theorem ofBool_not (b : Bool) : ofBool (!b) = (ofBool b)ᶜ := by decide +revert

@[simp, scoped grind =]
theorem ofBool_and (a b : Bool) : ofBool (a && b) = ofBool a ⊓ ofBool b := by decide +revert

@[simp, scoped grind =]
theorem ofBool_or (a b : Bool) : ofBool (a || b) = ofBool a ⊔ ofBool b := by decide +revert

end Value

end Cslib.Logic.Kleene
