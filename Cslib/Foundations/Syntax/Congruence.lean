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
def Congruence.r (r : α → α → Prop) [Congruence r] := r

@[inherit_doc]
scoped notation:50 a " ≡[" r "] " b => Congruence.r r a b

/-- The type `α` has a canonical congruence relation. This gives access to the `≡` notation. -/
class DefaultCongruence (α : Type*) where
  /-- `a ≡ b` means that `a` and `b` are related by the canonical congruence relation for their
  type. -/
  r : α → α → Prop

@[inherit_doc]
scoped notation:50 a " ≡ " b => DefaultCongruence.r a b

open Lean Meta in
initialize registerBuiltinAttribute {
  name := `default_congruence
  descr := "Registers a Congruence relation as the default, giving access to the ≡ notation."
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let constInfo ← getConstInfo declName
    let type := constInfo.type
    MetaM.run' do
      forallTelescopeReducing type fun binders target => do
        match target.getAppFnArgs with
        | (``Congruence, #[αExpr, rel]) => do
            let α ← instantiateMVars αExpr
            let defaultCongruenceType' ← mkAppM ``DefaultCongruence #[α]
            let defaultCongruenceType ← mkForallFVars binders defaultCongruenceType'
            let value' ← mkAppM ``DefaultCongruence.mk #[rel]
            let value ← mkLambdaFVars binders value'
            let instName := declName.appendAfter "_canonical"
            addAndCompile <| .defnDecl {
              name        := instName
              levelParams := constInfo.levelParams
              type        := defaultCongruenceType
              value       := value
              safety      := .safe
              hints       := Lean.ReducibilityHints.regular 0
            }
            setReducibilityStatus instName .instanceReducible
            addInstance instName kind (prio := eval_prio default)
        | _ => throwError "@[default_congruence] can only be attached to `Congruence` instances."
}

/-- An equivalence relation on `α` preserved by all contexts. -/
class LawfulCongruence (r : α → α → Prop) [Congruence r] [HasContext α] extends
  IsEquiv α r, covariant : CovariantClass (HasContext.Context α) α (·<[·]) (· ≡[r] ·)

end Cslib
