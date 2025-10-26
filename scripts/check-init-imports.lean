/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

/-!
# Check Init Imports

This script checks that all CSLib modules import at least one module from the Cslib namespace,
ensuring they are connected to the library's import graph and receive Cslib.Init.

Based on Mathlib's lint-style.lean script.
-/

open System

/-- Parse import statements from a file using simple text parsing -/
def findImports (path : FilePath) : IO (Array String) := do
  let contents ← IO.FS.readFile path
  let lines := contents.splitOn "\n"
  let imports := lines.filterMap fun line =>
    let trimmed := line.trim
    if trimmed.startsWith "import " then
      some (trimmed.drop 7 |>.trim)
    else
      none
  return imports.toArray

/-- Check that all Cslib modules import at least one Cslib module -/
def checkInitImports : IO UInt32 := do
  -- Get all module names from Cslib.lean
  let allModuleNames ← findImports "Cslib.lean"

  let mut modulesWithoutCslibImports := #[]

  for module in allModuleNames do
    -- Convert module name to file path (replace . with /)
    let pathParts := module.splitOn "."
    let path := mkFilePath pathParts |>.addExtension "lean"

    -- Get imports for this module
    let imports ← findImports path

    -- Check if ALL imports lack Cslib prefix (meaning no Cslib import)
    let hasNoCslibImport := imports.all fun imp ↦ !imp.startsWith "Cslib"

    if hasNoCslibImport then
      modulesWithoutCslibImports := modulesWithoutCslibImports.push module

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
