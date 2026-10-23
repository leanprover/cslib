/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

module

public import Cslib.Init
public import Cslib.Foundations.Logic.Operators
public import Mathlib.Tactic.DeriveFintype

/-! # Truth values of Kleene's strong three-valued logic

The truth values and connectives of Kleene's strong three-valued logic (K3) [Kleene1952], with the
truth order `false < unknown < true`. These are the semantic domain for the propositions in
`Cslib.Logics.Kleene.Semantics`.

## Main definitions

- `Kleene.Value`: the three truth values.
- `Kleene.Value.not`, `Kleene.Value.and`, `Kleene.Value.or`, `Kleene.Value.imp`,
  `Kleene.Value.iff`: the connectives.
- `Kleene.Value.ofBool`: the embedding of `Bool`.

## Main results

- `LinearOrder Kleene.Value`, `BoundedOrder Kleene.Value`: the truth order, with `∧` as meet and
  `∨` as join.
- `Kleene.Value.ofBool_and` and friends: `ofBool` commutes with the connectives.

## References

- [Kleene1952] S. C. Kleene, *Introduction to Metamathematics*, §64.
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

/-- Kleene negation. -/
def not : Value → Value
  | .true => .false
  | .false => .true
  | .unknown => .unknown

/-- Kleene conjunction. -/
def and : Value → Value → Value
  | .true, b => b
  | .false, _ => .false
  | .unknown, .false => .false
  | .unknown, _ => .unknown

/-- Kleene disjunction. -/
def or : Value → Value → Value
  | .true, _ => .true
  | .false, b => b
  | .unknown, .true => .true
  | .unknown, _ => .unknown

instance : HasNot Value := ⟨not⟩
instance : HasAnd Value := ⟨and⟩
instance : HasOr Value := ⟨or⟩

/-- Kleene implication, `¬a ∨ b`. -/
def imp (a b : Value) : Value := ¬a ∨ b

instance : HasImp Value := ⟨imp⟩

/-- Bi-implication, `(a → b) ∧ (b → a)`. -/
def iff (a b : Value) : Value := (a → b) ∧ (b → a)

instance : HasIff Value := ⟨iff⟩

@[simp, scoped grind =] protected theorem not_def (a : Value) : not a = ¬a := rfl
@[simp, scoped grind =] protected theorem and_def (a b : Value) : and a b = (a ∧ b) := rfl
@[simp, scoped grind =] protected theorem or_def (a b : Value) : or a b = (a ∨ b) := rfl
@[simp, scoped grind =] protected theorem imp_def (a b : Value) : imp a b = (a → b) := rfl
@[simp, scoped grind =] protected theorem iff_def (a b : Value) : iff a b = (a ↔ b) := rfl

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
  min := and
  max := or
  min_def := by decide
  max_def := by decide

instance : BoundedOrder Value where
  top := .true
  le_top _ := Or.inr (Or.inr rfl)
  bot := .false
  bot_le _ := Or.inr (Or.inl rfl)

@[simp, scoped grind =] theorem top_eq_true : (⊤ : Value) = .true := rfl
@[simp, scoped grind =] theorem bot_eq_false : (⊥ : Value) = .false := rfl

@[simp, scoped grind =] theorem inf_eq_and (a b : Value) : a ⊓ b = (a ∧ b) := rfl

@[simp, scoped grind =] theorem sup_eq_or (a b : Value) : a ⊔ b = (a ∨ b) := rfl

theorem false_lt_unknown : (.false : Value) < .unknown := by decide

theorem unknown_lt_true : (.unknown : Value) < .true := by decide

/-- Negation reverses the truth order. -/
theorem not_antitone : Antitone fun a : Value => ¬a := by decide

/-! ### Truth tables -/

@[simp, scoped grind =] protected theorem not_true : (¬Value.true) = .false := rfl
@[simp, scoped grind =] protected theorem not_false : (¬Value.false) = .true := rfl
@[simp, scoped grind =] theorem not_unknown : (¬Value.unknown) = .unknown := rfl

@[simp, scoped grind =] protected theorem false_and (a : Value) : (Value.false ∧ a) = .false :=
  rfl
@[simp, scoped grind =] protected theorem and_false (a : Value) : (a ∧ Value.false) = .false :=
  inf_bot_eq a
@[simp, scoped grind =] protected theorem true_and (a : Value) : (Value.true ∧ a) = a := rfl
@[simp, scoped grind =] protected theorem and_true (a : Value) : (a ∧ Value.true) = a :=
  inf_top_eq a

@[simp, scoped grind =] protected theorem true_or (a : Value) : (Value.true ∨ a) = .true := rfl
@[simp, scoped grind =] protected theorem or_true (a : Value) : (a ∨ Value.true) = .true :=
  sup_top_eq a
@[simp, scoped grind =] protected theorem false_or (a : Value) : (Value.false ∨ a) = a := rfl
@[simp, scoped grind =] protected theorem or_false (a : Value) : (a ∨ Value.false) = a :=
  sup_bot_eq a

/-! ### Laws -/

@[simp, scoped grind =] protected theorem not_not (a : Value) : (¬¬a) = a := by decide +revert

@[simp, scoped grind =] protected theorem and_self (a : Value) : (a ∧ a) = a := inf_idem a
@[simp, scoped grind =] protected theorem or_self (a : Value) : (a ∨ a) = a := sup_idem a

protected theorem and_comm (a b : Value) : (a ∧ b) = (b ∧ a) := inf_comm a b
protected theorem or_comm (a b : Value) : (a ∨ b) = (b ∨ a) := sup_comm a b

protected theorem and_assoc (a b c : Value) : ((a ∧ b) ∧ c) = (a ∧ b ∧ c) := inf_assoc a b c
protected theorem or_assoc (a b c : Value) : ((a ∨ b) ∨ c) = (a ∨ b ∨ c) := sup_assoc a b c

protected theorem and_or_left (a b c : Value) : (a ∧ (b ∨ c)) = (a ∧ b ∨ a ∧ c) :=
  inf_sup_left a b c
protected theorem or_and_left (a b c : Value) : (a ∨ b ∧ c) = ((a ∨ b) ∧ (a ∨ c)) :=
  sup_inf_left a b c

protected theorem not_and (a b : Value) : (¬(a ∧ b)) = (¬a ∨ ¬b) := not_antitone.map_min
protected theorem not_or (a b : Value) : (¬(a ∨ b)) = (¬a ∧ ¬b) := not_antitone.map_max

/-! ### Implication -/

@[scoped grind =]
theorem imp_eq_not_or (a b : Value) : (a → b) = (¬a ∨ b) := rfl

@[simp, scoped grind =] protected theorem false_imp (a : Value) : (Value.false → a) = .true :=
  rfl
@[simp, scoped grind =] protected theorem imp_true (a : Value) : (a → Value.true) = .true :=
  sup_top_eq _
@[simp, scoped grind =] protected theorem true_imp (a : Value) : (Value.true → a) = a := rfl
@[simp, scoped grind =] protected theorem imp_false (a : Value) : (a → Value.false) = ¬a :=
  sup_bot_eq _

@[simp, scoped grind =]
theorem unknown_imp_unknown : (Value.unknown → Value.unknown) = .unknown := rfl

@[simp, scoped grind =] protected theorem true_iff (a : Value) : (Value.true ↔ a) = a := by
  decide +revert
@[simp, scoped grind =] protected theorem iff_true (a : Value) : (a ↔ Value.true) = a := by
  decide +revert
@[simp, scoped grind =] protected theorem false_iff (a : Value) : (Value.false ↔ a) = ¬a := by
  decide +revert
@[simp, scoped grind =] protected theorem iff_false (a : Value) : (a ↔ Value.false) = ¬a := by
  decide +revert

@[simp, scoped grind =]
theorem unknown_iff_unknown : (Value.unknown ↔ Value.unknown) = .unknown := rfl

/-! ### Testing against `true` and `false` -/

@[simp] theorem and_eq_true_iff {a b : Value} : (a ∧ b) = .true ↔ a = .true ∧ b = .true :=
  inf_eq_top_iff

@[simp] theorem or_eq_true_iff {a b : Value} : (a ∨ b) = .true ↔ a = .true ∨ b = .true :=
  max_eq_top

@[simp] theorem or_eq_false_iff {a b : Value} : (a ∨ b) = .false ↔ a = .false ∧ b = .false :=
  sup_eq_bot_iff

@[simp] theorem not_eq_true_iff {a : Value} : (¬a) = .true ↔ a = .false := by grind

@[simp] theorem not_eq_false_iff {a : Value} : (¬a) = .false ↔ a = .true := by grind

/-! ### The embedding of `Bool` -/

/-- The embedding of `Bool`. -/
def ofBool : Bool → Value
  | Bool.true => .true
  | Bool.false => .false

@[simp, scoped grind =] theorem ofBool_true : ofBool Bool.true = .true := rfl
@[simp, scoped grind =] theorem ofBool_false : ofBool Bool.false = .false := rfl

theorem ofBool_injective : Function.Injective ofBool := by decide

@[simp] theorem ofBool_inj {a b : Bool} : ofBool a = ofBool b ↔ a = b := ofBool_injective.eq_iff

@[simp] theorem ofBool_ne_unknown (b : Bool) : ofBool b ≠ .unknown := by grind [cases Bool]

@[simp, scoped grind =]
theorem ofBool_not (b : Bool) : ofBool (!b) = ¬ofBool b := by grind [cases Bool]

@[simp, scoped grind =]
theorem ofBool_and (a b : Bool) : ofBool (a && b) = (ofBool a ∧ ofBool b) := by grind [cases Bool]

@[simp, scoped grind =]
theorem ofBool_or (a b : Bool) : ofBool (a || b) = (ofBool a ∨ ofBool b) := by grind [cases Bool]

end Value

end Cslib.Logic.Kleene
