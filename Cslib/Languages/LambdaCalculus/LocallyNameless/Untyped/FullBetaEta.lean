/-
Copyright (c) 2026 Maximiliano Onofre Martínez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maximiliano Onofre Martínez, Yijun Leng
-/

module

public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBetaConfluence
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullEtaConfluence

/-! # βη-Confluence for the λ-calculus

## Reference

* [T. Nipkow, *More Church-Rosser Proofs (in Isabelle/HOL)*][Nipkow2001]

-/

@[expose] public section

set_option linter.unusedDecidableInType false

namespace Cslib

universe u

variable {Var : Type u}

namespace LambdaCalculus.LocallyNameless.Untyped.Term

open Relation

/-- Full βη-reduction. -/
@[reduction_sys "βηᶠ"]
abbrev FullBetaEta : Term Var → Term Var → Prop := FullBeta ⊔ FullEta

namespace FullBetaEta

theorem redex_app_l_cong (redex : M ↠βηᶠ M') (lc_N : LC N) : app M N ↠βηᶠ app M' N := by
  induction redex with
  | refl => grind
  | tail _ h ih =>
    refine .trans ih (.single ?_)
    rcases h with h | h
    · exact join_inl (h.appR lc_N)
    · exact join_inr (h.appR lc_N)

theorem redex_app_r_cong (redex : M ↠βηᶠ M') (lc_N : LC N) : app N M ↠βηᶠ app N M' := by
  induction redex with
  | refl => grind
  | tail _ h ih =>
    refine .trans ih (.single ?_)
    rcases h with h | h
    · exact join_inl (h.appL lc_N)
    · exact join_inr (h.appL lc_N)

end FullBetaEta

end LambdaCalculus.LocallyNameless.Untyped.Term

end Cslib
