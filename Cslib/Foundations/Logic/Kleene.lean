/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

module

public import Cslib.Init
public import Cslib.Foundations.Logic.Operators
public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Order.Lattice
public import Mathlib.Order.BoundedOrder.Basic

/-! # Kleene's strong three-valued logic

The truth values and connectives of Kleene's strong three-valued logic (K3) [Kleene1952], with the
truth order `false < unknown < true`.

## Main definitions

- `Kleene`: the three truth values.
- `Kleene.not`, `Kleene.and`, `Kleene.or`, `Kleene.imp`, `Kleene.iff`: the connectives.

## Main results

- `LinearOrder Kleene`, `BoundedOrder Kleene`: the truth order, with `∧` as meet and `∨` as join.

## References

- [Kleene1952] S. C. Kleene, *Introduction to Metamathematics*, §64.
-/

@[expose] public section

namespace Cslib.Logic

-- Needed by the `Fintype` derive handler, as for Mathlib's `SignType`.
set_option backward.isDefEq.respectTransparency false in
/-- A truth value of Kleene's strong three-valued logic. -/
inductive Kleene where
  | true
  | false
  | unknown
  deriving DecidableEq, Repr, Fintype

namespace Kleene

instance : Inhabited Kleene := ⟨.unknown⟩

/-- Kleene negation. -/
def not : Kleene → Kleene
  | .true => .false
  | .false => .true
  | .unknown => .unknown

/-- Kleene conjunction. -/
def and : Kleene → Kleene → Kleene
  | .true, b => b
  | .false, _ => .false
  | .unknown, .false => .false
  | .unknown, _ => .unknown

/-- Kleene disjunction. -/
def or : Kleene → Kleene → Kleene
  | .true, _ => .true
  | .false, b => b
  | .unknown, .true => .true
  | .unknown, _ => .unknown

instance : HasNot Kleene := ⟨not⟩
instance : HasAnd Kleene := ⟨and⟩
instance : HasOr Kleene := ⟨or⟩

/-- Kleene implication, `¬a ∨ b`. -/
def imp (a b : Kleene) : Kleene := ¬a ∨ b

instance : HasImp Kleene := ⟨imp⟩

/-- Bi-implication, `(a → b) ∧ (b → a)`. -/
def iff (a b : Kleene) : Kleene := (a → b) ∧ (b → a)

instance : HasIff Kleene := ⟨iff⟩

@[simp, scoped grind =] protected theorem not_eq (a : Kleene) : not a = ¬a := rfl
@[simp, scoped grind =] protected theorem and_eq (a b : Kleene) : and a b = (a ∧ b) := rfl
@[simp, scoped grind =] protected theorem or_eq (a b : Kleene) : or a b = (a ∨ b) := rfl
@[simp, scoped grind =] protected theorem imp_eq (a b : Kleene) : imp a b = (a → b) := rfl
@[simp, scoped grind =] protected theorem iff_eq (a b : Kleene) : iff a b = (a ↔ b) := rfl

/-! ### The truth order -/

/-- The truth order `false < unknown < true`. -/
instance : LE Kleene := ⟨fun a b => a = b ∨ a = .false ∨ b = .true⟩

theorem le_def {a b : Kleene} : a ≤ b ↔ a = b ∨ a = .false ∨ b = .true := Iff.rfl

instance : DecidableLE Kleene := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

instance : LinearOrder Kleene where
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

instance : BoundedOrder Kleene where
  top := .true
  le_top _ := Or.inr (Or.inr rfl)
  bot := .false
  bot_le _ := Or.inr (Or.inl rfl)

@[simp, scoped grind =] theorem top_eq_true : (⊤ : Kleene) = .true := rfl
@[simp, scoped grind =] theorem bot_eq_false : (⊥ : Kleene) = .false := rfl

@[simp, scoped grind =] theorem inf_eq_and (a b : Kleene) : a ⊓ b = (a ∧ b) := rfl

@[simp, scoped grind =] theorem sup_eq_or (a b : Kleene) : a ⊔ b = (a ∨ b) := rfl

theorem false_lt_unknown : (.false : Kleene) < .unknown := by decide

theorem unknown_lt_true : (.unknown : Kleene) < .true := by decide

/-- Negation reverses the truth order. -/
theorem not_antitone : Antitone fun a : Kleene => ¬a := by decide

/-! ### Truth tables -/

@[simp, scoped grind =] protected theorem not_true : (¬Kleene.true) = .false := rfl
@[simp, scoped grind =] protected theorem not_false : (¬Kleene.false) = .true := rfl
@[simp, scoped grind =] theorem not_unknown : (¬Kleene.unknown) = .unknown := rfl

@[simp, scoped grind =] protected theorem false_and (a : Kleene) : (Kleene.false ∧ a) = .false :=
  rfl
@[simp, scoped grind =] protected theorem and_false (a : Kleene) : (a ∧ Kleene.false) = .false :=
  inf_bot_eq a
@[simp, scoped grind =] protected theorem true_and (a : Kleene) : (Kleene.true ∧ a) = a := rfl
@[simp, scoped grind =] protected theorem and_true (a : Kleene) : (a ∧ Kleene.true) = a :=
  inf_top_eq a

@[simp, scoped grind =] protected theorem true_or (a : Kleene) : (Kleene.true ∨ a) = .true := rfl
@[simp, scoped grind =] protected theorem or_true (a : Kleene) : (a ∨ Kleene.true) = .true :=
  sup_top_eq a
@[simp, scoped grind =] protected theorem false_or (a : Kleene) : (Kleene.false ∨ a) = a := rfl
@[simp, scoped grind =] protected theorem or_false (a : Kleene) : (a ∨ Kleene.false) = a :=
  sup_bot_eq a

/-! ### Laws -/

@[simp, scoped grind =] protected theorem not_not (a : Kleene) : (¬¬a) = a := by
  grind [cases Kleene]

@[simp, scoped grind =] protected theorem and_self (a : Kleene) : (a ∧ a) = a := inf_idem a
@[simp, scoped grind =] protected theorem or_self (a : Kleene) : (a ∨ a) = a := sup_idem a

protected theorem and_comm (a b : Kleene) : (a ∧ b) = (b ∧ a) := inf_comm a b
protected theorem or_comm (a b : Kleene) : (a ∨ b) = (b ∨ a) := sup_comm a b

protected theorem and_assoc (a b c : Kleene) : ((a ∧ b) ∧ c) = (a ∧ b ∧ c) := inf_assoc a b c
protected theorem or_assoc (a b c : Kleene) : ((a ∨ b) ∨ c) = (a ∨ b ∨ c) := sup_assoc a b c

protected theorem and_or_left (a b c : Kleene) : (a ∧ (b ∨ c)) = (a ∧ b ∨ a ∧ c) :=
  inf_sup_left a b c
protected theorem or_and_left (a b c : Kleene) : (a ∨ b ∧ c) = ((a ∨ b) ∧ (a ∨ c)) :=
  sup_inf_left a b c

protected theorem not_and (a b : Kleene) : (¬(a ∧ b)) = (¬a ∨ ¬b) := not_antitone.map_min
protected theorem not_or (a b : Kleene) : (¬(a ∨ b)) = (¬a ∧ ¬b) := not_antitone.map_max

/-! ### Implication -/

@[scoped grind =]
theorem imp_eq_not_or (a b : Kleene) : (a → b) = (¬a ∨ b) := rfl

@[simp, scoped grind =] protected theorem false_imp (a : Kleene) : (Kleene.false → a) = .true :=
  rfl
@[simp, scoped grind =] protected theorem imp_true (a : Kleene) : (a → Kleene.true) = .true :=
  sup_top_eq _
@[simp, scoped grind =] protected theorem true_imp (a : Kleene) : (Kleene.true → a) = a := rfl
@[simp, scoped grind =] protected theorem imp_false (a : Kleene) : (a → Kleene.false) = ¬a :=
  sup_bot_eq _

@[simp, scoped grind =]
theorem unknown_imp_unknown : (Kleene.unknown → Kleene.unknown) = .unknown := rfl

@[simp, scoped grind =] protected theorem true_iff (a : Kleene) : (Kleene.true ↔ a) = a := by
  decide +revert
@[simp, scoped grind =] protected theorem iff_true (a : Kleene) : (a ↔ Kleene.true) = a := by
  decide +revert
@[simp, scoped grind =] protected theorem false_iff (a : Kleene) : (Kleene.false ↔ a) = ¬a := by
  decide +revert
@[simp, scoped grind =] protected theorem iff_false (a : Kleene) : (a ↔ Kleene.false) = ¬a := by
  decide +revert

@[simp, scoped grind =]
theorem unknown_iff_unknown : (Kleene.unknown ↔ Kleene.unknown) = .unknown := rfl

/-- `a → a` is not valid. -/
theorem not_forall_imp_self_eq_true : ¬∀ a : Kleene, (a → a) = .true := by decide

/-- Excluded middle is not valid. -/
theorem not_forall_or_not_eq_true : ¬∀ a : Kleene, (a ∨ ¬a) = .true := by decide

end Kleene

end Cslib.Logic
