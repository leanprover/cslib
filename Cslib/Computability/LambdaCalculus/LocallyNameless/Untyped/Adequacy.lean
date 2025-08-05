/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Cslib.Computability.LambdaCalculus.Named.Untyped.Basic
import Cslib.Computability.LambdaCalculus.LocallyNameless.Untyped.Basic

universe u

variable {Var : Type u} [DecidableEq Var]

namespace LambdaCalculus

def Named.Term.toLocallyNameless (m : Named.Term Var) : LocallyNameless.Term Var := sorry

theorem alphaEqv_iff_eq (m n : Named.Term Var) : m =α n ↔ m.toLocallyNameless = n.toLocallyNameless := by
  sorry
