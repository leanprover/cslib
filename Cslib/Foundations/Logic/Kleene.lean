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
truth order `false < unknown < true` and the information order `unknown ⊑ true`,
`unknown ⊑ false`.

The truth order is the `LE` instance: `∧` and `∨` are its meet and join, and negation reverses
it. In the information order `⊑`, `unknown` lies below both definite values; every connective
is monotone in it.

## Main definitions

- `Kleene`: the three truth values.
- `Kleene.not`, `Kleene.and`, `Kleene.or`, `Kleene.imp`, `Kleene.iff`: the connectives.
- `Kleene.ofBool`: the embedding of `Bool`.
- `Kleene.InfoLE`, written `⊑`: the information order.

## Main results

- `LinearOrder Kleene`, `BoundedOrder Kleene`: the truth order, with `∧` as meet and `∨` as join.
- `Kleene.ofBool_and` and friends: `ofBool` commutes with the connectives.
- `IsPartialOrder Kleene Kleene.InfoLE`, `Kleene.InfoLE.and` and friends: the information
  order is a partial order in which every connective is monotone.

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

/-! ### The embedding of `Bool` -/

/-- The embedding of `Bool`. -/
def ofBool : Bool → Kleene
  | Bool.true => .true
  | Bool.false => .false

@[simp, scoped grind =] theorem ofBool_true : ofBool Bool.true = .true := rfl
@[simp, scoped grind =] theorem ofBool_false : ofBool Bool.false = .false := rfl

theorem ofBool_injective : Function.Injective ofBool := by decide

@[simp] theorem ofBool_inj {a b : Bool} : ofBool a = ofBool b ↔ a = b := ofBool_injective.eq_iff

@[simp] theorem ofBool_ne_unknown (b : Bool) : ofBool b ≠ .unknown := by grind [cases Bool]
@[simp] theorem unknown_ne_ofBool (b : Bool) : .unknown ≠ ofBool b := (ofBool_ne_unknown b).symm

@[simp, scoped grind =]
theorem ofBool_not (b : Bool) : ofBool (!b) = ¬ofBool b := by grind [cases Bool]

@[simp, scoped grind =]
theorem ofBool_and (a b : Bool) : ofBool (a && b) = (ofBool a ∧ ofBool b) := by grind [cases Bool]

@[simp, scoped grind =]
theorem ofBool_or (a b : Bool) : ofBool (a || b) = (ofBool a ∨ ofBool b) := by grind [cases Bool]

/-! ### Testing against `true` and `false` -/

@[simp] theorem and_beq_true (a b : Kleene) :
    ((a ∧ b) == .true) = (a == .true && b == .true) := by grind [cases Kleene]

@[simp] theorem or_beq_false (a b : Kleene) :
    ((a ∨ b) == .false) = (a == .false && b == .false) := by grind [cases Kleene]

@[simp] theorem not_beq_true (a : Kleene) : ((¬a) == .true) = (a == .false) := by grind

@[simp] theorem not_beq_false (a : Kleene) : ((¬a) == .false) = (a == .true) := by grind

@[simp] theorem ofBool_beq_true (b : Bool) : (ofBool b == .true) = b := by grind [cases Bool]

@[simp] theorem ofBool_beq_false (b : Bool) : (ofBool b == .false) = !b := by grind [cases Bool]

@[simp] theorem and_eq_true_iff {a b : Kleene} : (a ∧ b) = .true ↔ a = .true ∧ b = .true :=
  inf_eq_top_iff

@[simp] theorem or_eq_false_iff {a b : Kleene} : (a ∨ b) = .false ↔ a = .false ∧ b = .false :=
  sup_eq_bot_iff

@[simp] theorem not_eq_true_iff {a : Kleene} : (¬a) = .true ↔ a = .false := by grind

@[simp] theorem not_eq_false_iff {a : Kleene} : (¬a) = .false ↔ a = .true := by grind

/-! ### The information order -/

/-- The information order: `unknown` lies below every value, and the definite values are
incomparable. It is distinct from the truth order `≤`. -/
def InfoLE (a b : Kleene) : Prop := a = .unknown ∨ a = b

@[inherit_doc] scoped infix:50 " ⊑ " => InfoLE

theorem infoLE_def {a b : Kleene} : a ⊑ b ↔ a = .unknown ∨ a = b := Iff.rfl

instance : DecidableRel InfoLE := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

protected theorem InfoLE.refl (a : Kleene) : a ⊑ a := Or.inr rfl

protected theorem InfoLE.trans {a b c : Kleene} : a ⊑ b → b ⊑ c → a ⊑ c := by decide +revert

protected theorem InfoLE.antisymm {a b : Kleene} : a ⊑ b → b ⊑ a → a = b := by decide +revert

instance : IsPartialOrder Kleene InfoLE where
  refl := InfoLE.refl
  trans _ _ _ := InfoLE.trans
  antisymm _ _ := InfoLE.antisymm

/-- `unknown` is the least informative value. -/
@[simp] theorem unknown_infoLE (a : Kleene) : .unknown ⊑ a := Or.inl rfl

@[simp] theorem infoLE_unknown_iff {a : Kleene} : a ⊑ .unknown ↔ a = .unknown := by
  decide +revert

/-- Definite values are maximal in the information order. -/
@[simp] theorem ofBool_infoLE_iff {x : Bool} {b : Kleene} : ofBool x ⊑ b ↔ b = ofBool x := by
  decide +revert

@[simp] theorem true_infoLE_iff {b : Kleene} : .true ⊑ b ↔ b = .true := by decide +revert
@[simp] theorem false_infoLE_iff {b : Kleene} : .false ⊑ b ↔ b = .false := by decide +revert

/-! ### Monotonicity in the information order -/

protected theorem InfoLE.not {a a' : Kleene} (h : a ⊑ a') : (¬a) ⊑ (¬a') := by decide +revert

protected theorem InfoLE.and {a a' b b' : Kleene} (ha : a ⊑ a') (hb : b ⊑ b') :
    (a ∧ b) ⊑ (a' ∧ b') := by decide +revert

protected theorem InfoLE.or {a a' b b' : Kleene} (ha : a ⊑ a') (hb : b ⊑ b') :
    (a ∨ b) ⊑ (a' ∨ b') := by decide +revert

protected theorem InfoLE.imp {a a' b b' : Kleene} (ha : a ⊑ a') (hb : b ⊑ b') :
    (a → b) ⊑ (a' → b') := ha.not.or hb

protected theorem InfoLE.iff {a a' b b' : Kleene} (ha : a ⊑ a') (hb : b ⊑ b') :
    (a ↔ b) ⊑ (a' ↔ b') := (ha.imp hb).and (hb.imp ha)

end Kleene

end Cslib.Logic
