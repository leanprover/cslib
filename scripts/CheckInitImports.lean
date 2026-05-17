/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama, Chris Henson
-/

import Lean
import Mathlib.Lean.CoreM
import Batteries.Data.List.Basic
import ImportGraph

open Lean Core Elab Command

/-!
# Check Init Imports

This script checks that all CSLib modules (transitively) import Cslib.Init.
-/

/-- Modules with technical constraints preventing Cslib.Init import -/
def exceptions : List Name := [
  -- Circular dependency (imported by Cslib.Init)
  `Cslib.Foundations.Lint.Basic,
  `Cslib.Init,
]

def main : IO UInt32 := do
  let searchPath ← addSearchPathFromEnv (← getBuiltinSearchPath (← findSysroot))
  CoreM.withImportModules #[`Cslib] (searchPath := searchPath) (trustLevel := 1024) do
    let env ← getEnv
    let graph := env.importGraph.transitiveClosure
    let noInitGraph := 
      graph.filter (fun name imports => name.getRoot = `Cslib ∧ !imports.contains `Cslib.Init)
    let diff := noInitGraph.keys.diff exceptions
    if diff.length > 0 then
      IO.eprintln s!"error: the following modules do not import `Cslib.Init`: {diff}"
    return diff.length.toUInt32
