/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Cslib.Languages.LambdaCalculus.Named.Untyped.Basic



namespace CslibTests

open Cslib LambdaCalculus.Named LambdaCalculus.Named.Term

abbrev NatTerm := Term ℕ

def lambdaId := abs 0 (var 0)

example : (abs 0 (var 0)) =α (abs 1 (var 1)) := by
  constructor
  simp [Term.fv]

example : (abs 1 (var 0)).subst 0 (app (var 1) (var 2)) = (abs 3 (app (var 1) (var 2))) := by
  simp +instances [subst, fv, bv, vars, rename, instHasFreshNat, HasFresh.ofSucc]

def x := 0
def y := 1
def z := 2
def w := 3

attribute [simp] x y z w

local instance coeNatTerm : Coe ℕ (Term ℕ) := ⟨Term.var⟩

-- section 5.3.4 of TAPL
example : (abs y (app x y))[x := (app y z : Term ℕ)] = (abs w (app (app y z) w)) := by
  simp +instances [subst, fv, bv, vars, rename, instHasFreshNat, HasFresh.ofSucc,
    instHasSubstitutionTerm]

-- example : (abs 0 (abs 1 (app (var 0) (var 1)))) =α (abs 1 (abs 0 (app (var 1) (var 0)))) := by

end CslibTests
