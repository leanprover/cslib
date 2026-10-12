/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

module

public import Cslib.Init
public import Cslib.Foundations.Logic.Operators
public import Mathlib.Tactic.DeriveFintype

/-! # Kleene's strong three-valued logic

The truth values and connectives of Kleene's strong three-valued logic (K3) [Kleene1952].

## Main definitions

- `Kleene`: the three truth values.
- `Kleene.not`, `Kleene.and`, `Kleene.or`, `Kleene.imp`, `Kleene.iff`: the connectives.

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

end Kleene

end Cslib.Logic
