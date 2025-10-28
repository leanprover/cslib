/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Mathlib.Tactic.Linter.DirectoryDependency

/-!
# Check Init Imports

This script checks that all CSLib modules import at least one module from the Cslib namespace,
ensuring they are connected to the library's import graph and receive Cslib.Init.

Based on Mathlib's lint-style.lean script.
-/

open System

/-- Check that all Cslib modules import at least one Cslib module -/
def checkInitImports : IO UInt32 := do
  -- Get all module names from Cslib.lean
  let allModuleNames ← findImports "Cslib.lean"

  let mut modulesWithoutCslibImports := #[]

  for module in allModuleNames do
    -- Convert module name to file path (replace . with /)
    let pathParts := module.components.map toString
    let path := mkFilePath pathParts |>.addExtension "lean"

    -- Get imports for this module using Mathlib's robust parser
    let imports ← findImports path

    -- Check if any import starts with Cslib
    let hasCslibImport := imports.any fun imp => imp.getRoot == `Cslib

    if !hasCslibImport then
      modulesWithoutCslibImports := modulesWithoutCslibImports.push module

  -- Erase known exceptions with technical constraints
  modulesWithoutCslibImports := modulesWithoutCslibImports
    |>.erase `Cslib.Foundations.Lint.Basic          -- Circular dependency (imported by Cslib.Init)
    |>.erase `Cslib.Foundations.Data.FinFun         -- Notation conflict with Mathlib.Finsupp (→₀)
    |>.erase `Cslib.Foundations.Semantics.LTS.Basic -- Type elaboration issues in downstream files
    |>.erase `Cslib.Logics.LinearLogic.CLL.Basic    -- Syntax elaboration conflicts

  -- Report errors
  if modulesWithoutCslibImports.isEmpty then
    IO.println "✓ All modules import at least one Cslib module"
    return 0
  else
    IO.eprintln s!"error: the following {modulesWithoutCslibImports.size} module(s) do not import any Cslib module:"
    for module in modulesWithoutCslibImports do
      IO.eprintln s!"  {module}"
    IO.eprintln "\nThese modules should import Cslib.Init or another Cslib module."
    return modulesWithoutCslibImports.size.toUInt32

def main : IO UInt32 := checkInitImports
