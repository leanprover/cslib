/-
# Type system for System F<:

This module defines the core type system for System F<: (System F with bounded quantification).

The module defines:
- `Subtyp`: The subtyping relation Γ ⊢ A <: B
- `HasType`: The typing relation Γ ⊢ e : T

System F<: extends System F with bounded type quantification.
The subtyping relation includes structural rules (reflexivity, transitivity),
the top type as universal supertype, contravariant function subtyping,
and covariant bounded quantifier subtyping.

The typing system is standard for System F<: with subsumption:
if an expression has type A and A <: B, then the expression also has type B.
-/

import Cslib.Computability.LambdaCalculus.WellScoped.FSub.Syntax

/-- The subtyping relation for System F<:. `Subtyp Γ A B` means that type `A` is a
    subtype of type `B` under context `Γ`.

    The rules include:
    - `top`: Every type is a subtype of the top type
    - `refl`: Subtyping is reflexive
    - `trans`: Subtyping is transitive
    - `tvar`: Type variables are subtypes of their bounds
    - `arrow`: Function types are contravariant in domain, covariant in codomain
    - `poly`: Polymorphic types are covariant in both bound and body -/
@[grind]
inductive Subtyp : Ctx s -> Ty s -> Ty s -> Prop where
/-- Every type is a subtype of the top type -/
| top :
  Subtyp Γ T .top
/-- Subtyping is reflexive -/
| refl :
  Subtyp Γ T T
/-- Subtyping is transitive -/
| trans :
  Subtyp Γ A B ->
  Subtyp Γ B C ->
  Subtyp Γ A C
/-- Type variables are subtypes of their declared upper bounds -/
| tvar :
  Ctx.LookupTVar Γ X T ->
  Subtyp Γ (.tvar X) T
/-- Function subtyping: contravariant in domain, covariant in codomain -/
| arrow :
  Subtyp Γ T2 T1 ->
  Subtyp Γ U1 U2 ->
  Subtyp Γ (.arrow T1 U1) (.arrow T2 U2)
/-- Polymorphic subtyping: covariant in bound and body -/
| poly :
  Subtyp Γ T2 T1 ->
  Subtyp (Γ,X<:T2) U1 U2 ->
  Subtyp Γ (.poly T1 U1) (.poly T2 U2)

/-- The typing relation for System F<:. `HasType Γ e T` means that expression `e`
    has type `T` under context `Γ`.

    The rules include:
    - `var`: Type variables according to context lookup
    - `sub`: Subsumption - if e : T₁ and T₁ <: T₂ then e : T₂
    - `abs`: Function abstraction
    - `tabs`: Type abstraction (polymorphic functions)
    - `app`: Function application
    - `tapp`: Type application (polymorphic instantiation) -/
inductive HasType : Ctx s -> Exp s -> Ty s -> Prop where
/-- Term variables have the type assigned in the context -/
| var :
  Ctx.LookupVar Γ x T ->
  HasType Γ (.var x) T
/-- Subsumption: if e : T₁ and T₁ <: T₂, then e : T₂ -/
| sub :
  Subtyp Γ T1 T2 ->
  HasType Γ t T1 ->
  HasType Γ t T2
/-- Function abstraction: λx:T.e has type T -> U if e has type U under x:T -/
| abs :
  HasType (Γ,x:T) t (U.rename Rename.succVar) ->
  HasType Γ (.abs T t) (.arrow T U)
/-- Type abstraction: ΛX<:T.e has type ∀X<:T.U if e has type U under X<:T -/
| tabs :
  HasType (Γ,X<:T) t U ->
  HasType Γ (.tabs T t) (.poly T U)
/-- Function application: if e₁ : T -> U and e₂ : T, then e₁ e₂ : U -/
| app :
  HasType Γ t1 (.arrow T1 U1) ->
  HasType Γ t2 T1 ->
  HasType Γ (.app t1 t2) U1
/-- Type application: if e : ∀X<:T.U and S <: T, then e[S] : U[X := S] -/
| tapp :
  HasType Γ t (.poly T U) ->
  HasType Γ (.tapp t T) (U.open_tvar T)
