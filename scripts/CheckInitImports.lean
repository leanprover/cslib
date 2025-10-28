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

/-- Modules with technical constraints preventing Cslib.Init import -/
def exceptions : Array Lean.Name := #[
  `Cslib.Foundations.Lint.Basic,          -- Circular dependency (imported by Cslib.Init)
  `Cslib.Foundations.Data.FinFun,         -- Notation conflict with Mathlib.Finsupp (→₀)
  `Cslib.Foundations.Semantics.LTS.Basic, -- Type elaboration issues in downstream files
  `Cslib.Logics.LinearLogic.CLL.Basic     -- Syntax elaboration conflicts
]

/-- Check that all Cslib modules import at least one Cslib module.

    This ensures all modules are connected to the library's import graph and receive Cslib.Init.
    Modules listed in `Cslib.lean` should import something from the Cslib namespace (typically
    Cslib.Init), except for a small set of modules with technical constraints.
-/
def checkInitImports : IO UInt32 := do
  -- Get all module names from Cslib.lean
  let allModuleNames ← findImports "Cslib.lean"

  let mut modulesWithoutCslibImports := #[]

  for module in allModuleNames do
    -- Skip known exceptions upfront
    if exceptions.contains module then
      continue

    -- Convert module name to file path
    let pathParts := module.components.map toString
    let path := mkFilePath pathParts |>.addExtension "lean"

    -- Get imports for this module using Mathlib's robust parser
    let imports ← findImports path

    -- Check if any import starts with Cslib (has Cslib as its root namespace)
    let hasCslibImport := imports.any fun imp => imp.getRoot == `Cslib

    if !hasCslibImport then
      modulesWithoutCslibImports := modulesWithoutCslibImports.push module

  -- Report results
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
