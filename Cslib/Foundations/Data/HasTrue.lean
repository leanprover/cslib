/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Init

/-! # Types with a designated true value

`HasTrue α` designates a value of `α` as true.
-/

namespace Cslib

@[expose] public section

universe u v

/-- A type with a designated true value. -/
class HasTrue (α : Type u) where
  /-- The designated true value. -/
  true : α

namespace HasTrue

instance : HasTrue Bool := ⟨.true⟩

instance : HasTrue Prop := ⟨True⟩

instance {α : Type u} [HasTrue α] : HasTrue (ULift.{v} α) := ⟨.up HasTrue.true⟩

@[grind =, simp]
theorem true_bool : (HasTrue.true : Bool) = Bool.true := rfl

@[grind =, simp]
theorem true_prop : (HasTrue.true : Prop) = True := rfl

@[grind =, simp]
theorem true_ulift {α : Type u} [HasTrue α] :
    (HasTrue.true : ULift.{v} α) = .up HasTrue.true := rfl

end HasTrue

end

end Cslib
