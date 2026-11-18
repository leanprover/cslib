/-
Copyright (c) 2025 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/

module

public import Cslib.Init
public import Mathlib.Order.Notation

/-! # Notation classes for logical connectives -/

@[expose] public section

namespace Cslib.Logic

/-- Class for implication. -/
class HasImpl (α : Type*) where
  /-- Implication. -/
  impl : α → α → α

@[inherit_doc] scoped infixr:25 " → " => HasImpl.impl

/-- Class for conjunction. -/
class HasAnd (α : Type*) where
  /-- Conjunction. -/
  and : α → α → α

@[inherit_doc] scoped infixr:35 " ∧ " => HasAnd.and

/-- Class for disjunction. -/
class HasOr (α : Type*) where
  /-- Disjunction. -/
  or : α → α → α

@[inherit_doc] scoped infixr:30 " ∨ " => HasOr.or

/-- Class for negation. -/
class HasNot (α : Type*) where
  /-- Negation. -/
  not : α → α

@[inherit_doc] scoped notation:max "¬" a:40 => HasNot.not a

/-- Instantiate negation for types with implication and a bottom element. NB: this has a lower
  instance priority to account for proposition types with inbuilt negation. Possibly it should be
  a `def` instead? -/
instance (priority := 900) instNotImplBot (α : Type*) [HasImpl α] [Bot α] : HasNot α where
  not a := a → ⊥

end Cslib.Logic
