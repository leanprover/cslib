/-
Copyright (c) 2026 zayn7lie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Wang
-/
module

public import Cslib.Languages.LambdaCalculus.Unscoped.Untyped.DeBruijnSyntax
public import Cslib.Foundations.Data.Relation

/-!
# One-step β-reduction and its reflexive-transitive closure (Star)

This file defines the usual compatible one-step β-reduction on de Bruijn lambda terms.
It also introduces its reflexive-transitive closure and proves basic closure lemmas for
application and abstraction.

## Main definitions

* `Lambda.Beta`: one-step β-reduction.

## Main lemmas

Inside `namespace BetaStar` we provide the standard constructors and congruence lemmas:

* `BetaStar.appL`, `BetaStar.appR`, `BetaStar.app`, `BetaStar.abs`

These lemmas are used later to compare β-reduction with parallel reduction.
-/


namespace Lambda
open Term
open Relation.ReflTransGen

/-- One-step β-reduction (compatible closure). -/
@[reduction_sys "β"]
public inductive Beta : Term → Term → Prop
  | abs  {t t'}        : Beta t t' → Beta (λ.t) (λ.t')
  | appL {t t' u}      : Beta t t' → Beta (t·u) (t'·u)
  | appR {t u u'}      : Beta u u' → Beta (t·u) (t·u')
  | red  (t' s : Term) : Beta ((λ.t')·s) (t'.sub 0 s)

namespace BetaStar

public theorem appL {t t' u : Term} (h : t ↠β t') :
    (t·u) ↠β (t'·u) := by
  induction h with
  | refl => exact refl (t·u)
  | tail hab hbc ih => exact tail ih (Beta.appL hbc)

public theorem appR {t u u' : Term} (h : u ↠β u') :
    (t·u) ↠β (t·u') := by
  induction h with
  | refl => exact refl (t·u)
  | tail hab hbc ih => exact tail ih (Beta.appR hbc)

public theorem app {t t' u u'}
    (ht : t ↠β t') (hu : u ↠β u') :
    (t·u) ↠β (t'·u') := by
  induction ht with
  | refl => exact appR hu
  | tail hab hbc ih => exact tail ih (Beta.appL hbc)

public theorem abs {t t' : Term} (h : t ↠β t') :
    (λ.t) ↠β (λ.t') := by
  induction h with
  | refl => exact refl (λ.t)
  | tail hab hbc ih => exact tail ih (Beta.abs hbc)

end BetaStar
end Lambda
