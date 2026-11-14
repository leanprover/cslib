/-
Copyright (c) 2025 Yichen Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yichen Xu.
-/

/-
# Core syntax for System F<:

This module defines the core syntactic constructs of System F<: (System F with subtyping).
The syntax uses intrinsically scoped de Bruijn indices where variables are indexed by
signatures that ensure well-scopedness by construction.

The module defines:
- `Ty`: Types including top type, type variables, function types, and polymorphic types
- `Exp`: Expressions including variables, abstractions, applications, and type applications
- Renaming operations for both types and expressions
- Value predicate identifying syntactic values

The syntax is intrinsically well-scoped.
Variables cannot refer to bindings that don't exist.
-/

import Cslib.Computability.LambdaCalculus.WellScoped.FSub.Debruijn

/-- Types in System F<:. The type system includes:
    - `top`: The universal supertype that all types are subtypes of
    - `tvar`: Type variables, intrinsically scoped by signature
    - `arrow`: Function types (A → B)
    - `poly`: Polymorphic types (forall X <: A. B) where B has access to type variable X -/
inductive Ty : Sig → Type where
/-- The top type, supertype of all types -/
| top : Ty s
/-- Type variable -/
| tvar : TVar s → Ty s
/-- Function type A → B -/
| arrow : Ty s → Ty s → Ty s
/-- Polymorphic type ∀X<:A.B -/
| poly : Ty s → Ty (s,X) → Ty s

/-- Rename all type variables in a type according to the given renaming. -/
def Ty.rename : Ty s1 → Rename s1 s2 → Ty s2
| top, _ => top
| tvar X, ρ => tvar (ρ.tvar X)
| arrow A B, ρ => arrow (A.rename ρ) (B.rename ρ)
| poly A B, ρ => poly (A.rename ρ) (B.rename ρ.liftTVar)

/-- Expressions in System F<:. The expression language includes:
    - `var`: Term variables, intrinsically scoped
    - `abs`: Function abstraction (λx:T. e) where T is the parameter type
    - `tabs`: Type abstraction (ΛX<:T. e) for polymorphic functions
    - `app`: Function application (e₁ e₂)
    - `tapp`: Type application (e T) for instantiating polymorphic functions -/
inductive Exp : Sig → Type where
/-- Term variable -/
| var : Var s → Exp s
/-- Function abstraction λx:T.e -/
| abs : Ty s → Exp (s,x) → Exp s
/-- Type abstraction ΛX<:T.e -/
| tabs : Ty s → Exp (s,X) → Exp s
/-- Function application e₁ e₂ -/
| app : Exp s → Exp s → Exp s
/-- Type application e[T] -/
| tapp : Exp s → Ty s → Exp s

/-- Rename all variables (both term and type variables) in an expression
    according to the given renaming. -/
def Exp.rename : Exp s1 → Rename s1 s2 → Exp s2
| var x, ρ => var (ρ.var x)
| abs A e, ρ => abs (A.rename ρ) (e.rename ρ.liftVar)
| tabs A e, ρ => tabs (A.rename ρ) (e.rename ρ.liftTVar)
| app e1 e2, ρ => app (e1.rename ρ) (e2.rename ρ)
| tapp e A, ρ => tapp (e.rename ρ) (A.rename ρ)

/-- Renaming with the identity renaming leaves a type unchanged. -/
theorem Ty.rename_id {T : Ty s} : T.rename Rename.id = T := by
  induction T <;> try (solve | rfl | simp only [Ty.rename, Rename.id_liftTVar_eq_id]; grind)

/-- Renaming with the identity renaming leaves an expression unchanged. -/
theorem Exp.rename_id {e : Exp s} : e.rename Rename.id = e := by
  induction e <;> try (solve | rfl |
    simp only [Exp.rename, Ty.rename_id, Rename.id_liftVar_eq_id, Rename.id_liftTVar_eq_id]; grind)

/-- Composition of renamings: renaming by f₁ then f₂ equals renaming by their composition. -/
theorem Ty.rename_comp {T : Ty s1} {f1 : Rename s1 s2} {f2 : Rename s2 s3} :
  (T.rename f1).rename f2 = T.rename (f1.comp f2) := by
  induction T generalizing s2 s3 <;>
    try (solve | rfl | simp only [Ty.rename, Rename.comp_liftTVar]; grind)

/-- Composition of renamings: renaming by f₁ then f₂ equals renaming by their composition. -/
theorem Exp.rename_comp {e : Exp s1} {f1 : Rename s1 s2} {f2 : Rename s2 s3} :
  (e.rename f1).rename f2 = e.rename (f1.comp f2) := by
  induction e generalizing s2 s3 <;>
    try (solve | rfl)
  all_goals
    simp only [Exp.rename, Ty.rename_comp, Rename.comp_liftVar, Rename.comp_liftTVar]; grind

/-- Commutativity law for term variable weakening and general renamings. -/
theorem Ty.rename_succVar_comm {T : Ty s} :
  (T.rename f).rename Rename.succVar = (T.rename Rename.succVar).rename f.liftVar := by
  simp [Ty.rename_comp, Rename.rename_succVar_comm]

/-- Commutativity law for type variable weakening and general renamings. -/
theorem Ty.rename_succTVar_comm {T : Ty s} :
  (T.rename f).rename Rename.succTVar = (T.rename Rename.succTVar).rename f.liftTVar := by
  simp [Ty.rename_comp, Rename.rename_succTVar_comm]

/-- The value predicate identifies expressions that are syntactic values.
    In System F<:, values are function abstractions and type abstractions.
    This predicate is used in the operational semantics to determine when
    evaluation has reached a final result. -/
@[grind]
inductive Exp.IsVal : Exp s → Prop where
/-- Function abstractions are values -/
| abs : IsVal (.abs T e)
/-- Type abstractions are values -/
| tabs : IsVal (.tabs T e)
