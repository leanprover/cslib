/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Foundations.Syntax.Context
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs

/-! Typeclass for congruence over a context. -/

@[expose] public section

namespace Cslib

/-- The relation `r` is a congruence on `α`. This class gives access to the `≡[r]` notation.
To instantiate a canonical congruence for `α`, see `HasCongruence`.

Congruence relations should also instantiate `LawfulCongruence` to prove that the relation respects
the expected congruence laws. -/
class Congruence (r : α → α → Prop)

/-- `a ≡[r] b` means that the `a` and `b` are related by the congruence `r`. -/
@[nolint unusedArguments]
abbrev Congruence.r (r : α → α → Prop) [Congruence r] := r

@[inherit_doc]
scoped notation:29 a " ≡[" r "] " b => Congruence.r r a b

/-- The type `α` has a canonical congruence relation. This gives access to the `≡` notation. -/
class DefaultCongruence (α : Type*) (r : outParam (α → α → Prop))

/-- `a ≡ b` means that `a` and `b` are related by the canonical congruence relation for their
type. -/
@[nolint unusedArguments]
abbrev DefaultCongruence.r {α : Type*} {r : α → α → Prop} [DefaultCongruence α r] (a b : α) := r a b

@[inherit_doc]
scoped infix:29 " ≡ " => DefaultCongruence.r

@[nolint unusedArguments]
instance (α : Type*) (r : α → α → Prop) [DefaultCongruence α r] : Congruence r := ⟨⟩

/-- An equivalence relation on `α` preserved by all contexts. -/
class LawfulCongruence (r : α → α → Prop) [Congruence r] [HasContext α] extends
  IsEquiv α r, covariant : CovariantClass (HasContext.Context α) α (·<[·]) r

end Cslib
