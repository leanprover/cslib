/-
Copyright (c) 2025 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

import Cslib.Computability.LambdaCalculus.STLC.LocallyNameless.Context
import Cslib.Computability.LambdaCalculus.Untyped.LocallyNameless.Basic

/-! # λ-calculus

The simply typed λ-calculus, with a locally nameless representation of syntax.

## References

* [A. Chargueraud, *The Locally Nameless Representation*] [Chargueraud2012]
* See also https://www.cis.upenn.edu/~plclub/popl08-tutorial/code/, from which
  this is partially adapted

-/

universe u

variable {Var : Type u} [DecidableEq Var]

namespace LambdaCalculus.LocallyNameless

/-- Types of the simply typed lambda calculus. -/
inductive Ty
/-- A base type, from a typing context. -/
| base : Ty
/-- A function type. -/
| arrow : Ty → Ty → Ty

scoped infixr:70 " ⤳ " => Ty.arrow
scoped prefix:90 "~ " => Ty.base

open Term Ty

/-- An extrinsic typing derivation for locally nameless terms. -/
@[aesop unsafe [constructors (rule_sets := [LambdaCalculus.LocallyNameless.ruleSet])]]
inductive Typing : Ctx Var Ty → Term Var → Ty → Prop
| var : Γ.Ok → (x,σ) ∈ Γ → Typing Γ (fvar x) σ
| abs (L : Finset Var) : (∀ x ∉ L, Typing ((x,σ) :: Γ) (t ^ fvar x) τ) → Typing Γ t.abs (σ ⤳ τ) 
| app : Typing Γ t (σ ⤳ τ) → Typing Γ t' σ → Typing Γ (app t t') τ

scoped notation:50 Γ " ⊢ " t " ∶" τ:arg => Typing Γ t τ
