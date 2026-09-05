/-
Copyright (c) 2025 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Leng
-/

module

public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Basic

/-! Size of untyped lambda calculus term. -/

@[expose] public section

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

universe u

variable {Var : Type u}

/-- Computes the size of a lambda calculus term. -/
@[simp, scoped grind =]
def size : Term Var -> Nat
| bvar _ => 0
| fvar _ => 0
| abs t => 1 + size t
| app t1 t2 => 1 + size t1 + size t2

@[scoped grind =]
theorem size_openRec_fvar (i) (x : Var) (M) : M⟦i ↝ fvar x⟧.size = M.size := by
  induction M generalizing i <;> grind

theorem size_open_fvar (x : Var) (t : Term Var) : size (t ^ fvar x) = size t :=
  size_openRec_fvar 0 x t

end LambdaCalculus.LocallyNameless.Untyped.Term

end Cslib
