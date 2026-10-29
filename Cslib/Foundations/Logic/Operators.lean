/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Thomas Waring
-/

module

public import Cslib.Init

/-! # Logical operators

This module contains typeclasses and associated notation for common logical operators: propositional
connectives (like `∧` and `→`), modalities (like `◇`, plain and indexed), linear connectives (like
`⊗`), etc.
-/

@[expose] public section

namespace Cslib.Logic

section Propositional

/-! ## Propositional connectives -/

/-- The type `α` has an and connective (`∧`). -/
class HasAnd (α : Type*) where
  /-- `a ∧ b` is the conjunction of `a` and `b`. -/
  and (a b : α) : α

@[inherit_doc] scoped infixr:36 " ∧ " => HasAnd.and

/-- The type `α` has an or connective (`∨`). -/
class HasOr (α : Type*) where
  /-- `a ∨ b` is the disjunction of `a` and `b`. -/
  or (a b : α) : α

@[inherit_doc] scoped infixr:30 " ∨ " => HasOr.or

/-- The type `α` has an implication connective (`→`). -/
class HasImp (α : Type*) where
  /-- `a → b` denotes `a` implies `b`. -/
  imp (a b : α) : α

@[inherit_doc] scoped infixr:25 " → " => HasImp.imp

/-- The type `α` has a bi-implication connective (`↔`). -/
class HasIff (α : Type*) where
  /-- `a ↔ b` denotes `a` implies `b` and vice-versa. -/
  iff (a b : α) : α

@[inherit_doc] scoped infixr:20 " ↔ " => HasIff.iff

/-- The type `α` has a negation connective (`¬`). -/
class HasNot (α : Type*) where
  /-- `¬a` is the negation of `a`. -/
  not (a : α) : α

@[inherit_doc] scoped notation:max "¬" p:40 => HasNot.not p

end Propositional

section Modal

/-! ## Basic modalities -/

/-- The type `α` has a box modality (`□`). -/
class HasBox (α : Type*) where
  /-- `a` is valid in all immediately reachable states. -/
  box (a : α) : α

@[inherit_doc] scoped prefix:40 "□" => HasBox.box

/-- The type `α` has a diamond modality (`◇`). -/
class HasDiamond (α : Type*) where
  /-- `a` is valid in a reachable state. -/
  diamond (a : α) : α

@[inherit_doc] scoped prefix:40 "◇" => HasDiamond.diamond

end Modal

section Dynamic

/-! ## Dynamic modalities

Here we need to use the prefix `d` to distinguish our notation from the normal `[·]` and `⟨·⟩`.
A refactoring that makes this unnecessary would be welcome.
-/

/-- The type `α` has a dynamic box modality with action type `β` (`d[a]φ`). -/
class HasDynamicBox (α β : Type*) where
  /-- `b` is necessarily valid after `a`. -/
  dynBox (a : β) (b : α) : α

@[inherit_doc] scoped notation "d[" a "]" φ => HasDynamicBox.dynBox a φ

/-- The type `α` has a dynamic diamond modality with action type `β` (`d⟨a⟩φ`). -/
class HasDynamicDiamond (α β : Type*) where
  /-- `b` is possibly valid after `a`. -/
  dynDiamond (a : β) (b : α) : α

@[inherit_doc] scoped notation "d⟨" a "⟩" φ => HasDynamicDiamond.dynDiamond a φ

end Dynamic

section Linear

/-! ## Linear connectives -/

/-- The type `α` has a tensor connective (⊗). -/
class HasTensor (α : Type*) where
  /-- `a ⊗ b` is the multiplicative conjunction of `a` and `b`. -/
  tensor (a b : α) : α

@[inherit_doc] scoped infixr:35 " ⊗ " => HasTensor.tensor

end Linear

end Cslib.Logic
