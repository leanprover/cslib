/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Mathlib.Tactic.Linter.DirectoryDependency

/-!
# Check Cslib.lean Completeness

This script checks that all CSLib modules in the source tree are imported in `Cslib.lean`,
ensuring no modules are orphaned from the main import graph.
-/

open System

/-- Get all .lean files recursively from a directory -/
partial def findAllLeanFiles (dir : FilePath) : IO (Array FilePath) := do
  let mut files := #[]
  let entries ← dir.readDir
  for entry in entries do
    let path := entry.path
    if ← path.isDir then
      -- Recursively search subdirectories
      files := files ++ (← findAllLeanFiles path)
    else if path.extension == some "lean" then
      files := files.push path
  return files

/-- Convert a file path to a module name (e.g., "Cslib/Foo/Bar.lean" -> `Cslib.Foo.Bar`) -/
def filePathToModuleName (filePath : FilePath) : Lean.Name :=
  let pathStr := filePath.toString
  -- Remove .lean extension
  let withoutExt := pathStr.dropRight 5
  -- Convert path separators to dots
  let parts := withoutExt.splitOn "/"
  -- Build the module name
  parts.foldl (init := Lean.Name.anonymous) fun name part =>
    name.mkStr part

/-- Modules that don't need to be imported in Cslib.lean -/
def exceptions : Array Lean.Name := #[
  `Cslib,       -- Cslib.lean itself
  `Cslib.Init   -- This is imported by other modules, not by Cslib.lean itself
]

def main : IO UInt32 := do
  -- Get all modules currently in Cslib.lean
  let importedModules ← findImports "Cslib.lean"

  -- Find all .lean files in Cslib directory
  let allFiles ← findAllLeanFiles "Cslib"

  -- Convert to module names
  let allModules := allFiles.map filePathToModuleName

  -- Find modules not imported in Cslib.lean (excluding exceptions)
  let missingModules := allModules.filter fun modName =>
    !importedModules.contains modName && !exceptions.contains modName

  -- Report results
  if missingModules.isEmpty then
    IO.println "✓ All Cslib modules are imported in Cslib.lean"
    return 0
  else
    IO.eprintln s!"error: the following {missingModules.size} module(s) are not imported in Cslib.lean:"
    for modName in missingModules do
      IO.eprintln s!"  {modName}"
    IO.eprintln "\nThese modules should be added to Cslib.lean to be part of the library."
    return missingModules.size.toUInt32
