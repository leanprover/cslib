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

In the information order `⊑`, `unknown` lies below both definite values, which are incomparable.
Every operation is monotone in it, and `⊓`, `⊔` and `ᶜ` are the greatest monotone extensions of
`&&`, `||` and `!`. Under `⊑`, `Kleene.Value` is the flat domain on `Bool`, so these results could
be subsumed under a general development of domain theory.

## Main definitions

- `Kleene.Value`: the three truth values.
- `Compl Kleene.Value`: the complement, which swaps `true` and `false` and fixes `unknown`.
- `Kleene.Value.ofBool`: the embedding of `Bool`.
- `Kleene.Value.InfoLE`, written `⊑`: the information order.
- `Kleene.Value.equivOptionBool`: the equivalence with `Option Bool`, `unknown` as `none`.

## Main results

- `LinearOrder Kleene.Value`, `BoundedOrder Kleene.Value`: the truth order.
- `Kleene.Value.compl_inf`, `Kleene.Value.compl_sup`: the De Morgan laws.
- `Kleene.Value.ofBool_and` and friends: `ofBool` commutes with the operations.
- `IsPartialOrder Kleene.Value Kleene.Value.InfoLE`, `Kleene.Value.InfoLE.inf` and friends: the
  information order is a partial order in which every operation is monotone.
- `Kleene.Value.infoLE_inf_of_extends` and friends: `⊓`, `⊔` and `ᶜ` are the greatest monotone
  extensions of `&&`, `||` and `!`.
- `Kleene.Value.eq_compl_of_extends`: `ᶜ` is the only monotone extension of `!`.

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
@[simp] theorem unknown_ne_ofBool (b : Bool) : .unknown ≠ ofBool b := (ofBool_ne_unknown b).symm

@[simp, scoped grind =]
theorem ofBool_not (b : Bool) : ofBool (!b) = (ofBool b)ᶜ := by decide +revert

@[simp, scoped grind =]
theorem ofBool_and (a b : Bool) : ofBool (a && b) = ofBool a ⊓ ofBool b := by decide +revert

@[simp, scoped grind =]
theorem ofBool_or (a b : Bool) : ofBool (a || b) = ofBool a ⊔ ofBool b := by decide +revert

/-! ### The information order -/

/-- The information order: `unknown` lies below every value, and the definite values are
incomparable. It is distinct from the truth order `≤`. -/
def InfoLE (a b : Value) : Prop := a = .unknown ∨ a = b

@[inherit_doc] scoped infix:50 " ⊑ " => InfoLE

theorem infoLE_def {a b : Value} : a ⊑ b ↔ a = .unknown ∨ a = b := Iff.rfl

instance : DecidableRel InfoLE := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

protected theorem InfoLE.refl (a : Value) : a ⊑ a := Or.inr rfl

protected theorem InfoLE.trans {a b c : Value} : a ⊑ b → b ⊑ c → a ⊑ c := by decide +revert

protected theorem InfoLE.antisymm {a b : Value} : a ⊑ b → b ⊑ a → a = b := by decide +revert

instance : IsPartialOrder Value InfoLE where
  refl := InfoLE.refl
  trans _ _ _ := InfoLE.trans
  antisymm _ _ := InfoLE.antisymm

/-- `unknown` is the least informative value. -/
@[simp] theorem unknown_infoLE (a : Value) : .unknown ⊑ a := Or.inl rfl

@[simp] theorem infoLE_unknown_iff {a : Value} : a ⊑ .unknown ↔ a = .unknown := by
  decide +revert

/-- Definite values are maximal in the information order. -/
@[simp] theorem ofBool_infoLE_iff {x : Bool} {b : Value} : ofBool x ⊑ b ↔ b = ofBool x := by
  decide +revert

@[simp] theorem true_infoLE_iff {b : Value} : .true ⊑ b ↔ b = .true := by decide +revert
@[simp] theorem false_infoLE_iff {b : Value} : .false ⊑ b ↔ b = .false := by decide +revert

/-! ### Monotonicity in the information order -/

protected theorem InfoLE.compl {a a' : Value} (h : a ⊑ a') : aᶜ ⊑ a'ᶜ := by decide +revert

protected theorem InfoLE.inf {a a' b b' : Value} (ha : a ⊑ a') (hb : b ⊑ b') :
    a ⊓ b ⊑ a' ⊓ b' := by decide +revert

protected theorem InfoLE.sup {a a' b b' : Value} (ha : a ⊑ a') (hb : b ⊑ b') :
    a ⊔ b ⊑ a' ⊔ b' := by decide +revert

/-! ### Greatest monotone extensions -/

/-- The complement is the greatest extension of Boolean negation that is monotone in the
information order. -/
theorem infoLE_compl_of_extends {f : Value → Value}
    (mono : ∀ {a a'}, a ⊑ a' → f a ⊑ f a')
    (ext : ∀ x : Bool, f (ofBool x) = ofBool (!x)) (a : Value) : f a ⊑ aᶜ := by
  have key (x : Bool) (ha : a ⊑ ofBool x) : f a ⊑ ofBool (!x) := ext x ▸ mono ha
  cases a <;> simp [infoLE_def, Bool.forall_bool] at key ⊢ <;> grind

/-- The complement is the only extension of Boolean negation that is monotone in the information
order. -/
theorem eq_compl_of_extends {f : Value → Value}
    (mono : ∀ {a a'}, a ⊑ a' → f a ⊑ f a')
    (ext : ∀ x : Bool, f (ofBool x) = ofBool (!x)) (a : Value) : f a = aᶜ := by
  have h := infoLE_compl_of_extends mono ext a
  cases a <;> simp_all

/-- The meet is the greatest extension of Boolean conjunction that is monotone in the information
order. -/
theorem infoLE_inf_of_extends {f : Value → Value → Value}
    (mono : ∀ {a a' b b'}, a ⊑ a' → b ⊑ b' → f a b ⊑ f a' b')
    (ext : ∀ x y : Bool, f (ofBool x) (ofBool y) = ofBool (x && y))
    (a b : Value) : f a b ⊑ a ⊓ b := by
  have key (x y : Bool) (ha : a ⊑ ofBool x) (hb : b ⊑ ofBool y) : f a b ⊑ ofBool (x && y) :=
    ext x y ▸ mono ha hb
  cases a <;> cases b <;> simp [infoLE_def, Bool.forall_bool] at key ⊢ <;> grind

/-- The join is the greatest extension of Boolean disjunction that is monotone in the information
order. -/
theorem infoLE_sup_of_extends {f : Value → Value → Value}
    (mono : ∀ {a a' b b'}, a ⊑ a' → b ⊑ b' → f a b ⊑ f a' b')
    (ext : ∀ x y : Bool, f (ofBool x) (ofBool y) = ofBool (x || y))
    (a b : Value) : f a b ⊑ a ⊔ b := by
  have key (x y : Bool) (ha : a ⊑ ofBool x) (hb : b ⊑ ofBool y) : f a b ⊑ ofBool (x || y) :=
    ext x y ▸ mono ha hb
  cases a <;> cases b <;> simp [infoLE_def, Bool.forall_bool] at key ⊢ <;> grind

/-! ### The equivalence with `Option Bool` -/

/-- The definite values as `some`, `unknown` as `none`. -/
def toOption : Value → Option Bool
  | .true => some Bool.true
  | .false => some Bool.false
  | .unknown => none

/-- `some b` as `ofBool b`, `none` as `unknown`. -/
def ofOption : Option Bool → Value
  | some b => ofBool b
  | none => .unknown

@[simp, scoped grind =] theorem ofOption_some (b : Bool) : ofOption (some b) = ofBool b := rfl
@[simp, scoped grind =] theorem ofOption_none : ofOption none = .unknown := rfl

@[simp, scoped grind =] theorem toOption_ofBool (b : Bool) : toOption (ofBool b) = some b := by
  cases b <;> rfl
@[simp, scoped grind =] theorem toOption_true : toOption .true = some Bool.true := rfl
@[simp, scoped grind =] theorem toOption_false : toOption .false = some Bool.false := rfl
@[simp, scoped grind =] theorem toOption_unknown : toOption .unknown = none := rfl

@[simp] theorem toOption_eq_none_iff {a : Value} : toOption a = none ↔ a = .unknown := by
  cases a <;> simp [toOption]

@[simp] theorem toOption_eq_some_iff {a : Value} {b : Bool} :
    toOption a = some b ↔ a = ofBool b := by
  cases a <;> cases b <;> simp [toOption]

@[simp, scoped grind =] theorem toOption_compl (a : Value) :
    toOption aᶜ = (toOption a).map Bool.not := by cases a <;> rfl

@[simp, scoped grind =] theorem ofOption_toOption (a : Value) : ofOption (toOption a) = a := by
  cases a <;> rfl
@[simp, scoped grind =] theorem toOption_ofOption (o : Option Bool) :
    toOption (ofOption o) = o := by cases o <;> simp

/-- `Kleene.Value` is `Option Bool` with `unknown` as `none`. -/
@[simps (attr := scoped grind =)]
def equivOptionBool : Value ≃ Option Bool where
  toFun := toOption
  invFun := ofOption
  left_inv := ofOption_toOption
  right_inv := toOption_ofOption

/-- The information order, read through `ofOption`. -/
@[simp] theorem ofOption_infoLE_iff {o o' : Option Bool} :
    ofOption o ⊑ ofOption o' ↔ o = none ∨ o = o' := by
  cases o <;> cases o' <;> simp [infoLE_def]

end Value

end Cslib.Logic.Kleene
