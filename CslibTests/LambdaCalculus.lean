/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Cslib.Computability.LambdaCalculus.Untyped.Named.Basic

open LambdaCalculus.Named
open LambdaCalculus.Named.Term

abbrev NatTerm := Term ℕ

def lambdaId := abs 0 (var 0)

example : (abs 0 (var 0)) =α (abs 1 (var 1)) := by
  constructor
  simp [Term.fv]

-- example : (abs 0 (abs 1 (app (var 0) (var 1)))) =α (abs 1 (abs 0 (app (var 1) (var 0)))) := by
