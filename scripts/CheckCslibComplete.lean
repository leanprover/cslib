/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama, Chris Henson
-/

import Mathlib.Tactic.Linter.DirectoryDependency
import Batteries.Data.List.Basic

/-!
# Check Cslib.lean Completeness

This script checks that all CSLib modules in the source tree are imported in `Cslib.lean`,
ensuring no modules are orphaned from the main import graph.
-/

open Lean System

/-- The same as `Lean.forEachModuleInDir`, but return the names. -/
partial def forEachModuleInDir' [Monad m] [MonadLiftT IO m]
    (dir : FilePath) (f : Lean.Name → Lean.Name) : m (List Name) := do
  let mut ret := []
  for entry in (← dir.readDir) do
    if (← liftM (m := IO) <| entry.path.isDir) then
      let n := Lean.Name.mkSimple entry.fileName
      let ret' ← forEachModuleInDir' entry.path (f <| n ++ ·)
      ret := ret ++ ret'
    else if entry.path.extension == some "lean" then
      ret := (f <| Lean.Name.mkSimple <| FilePath.withExtension entry.fileName "" |>.toString) :: ret
  return ret

/-- Modules that don't need to be imported in Cslib.lean -/
def exceptions : List Name := []

def main : IO UInt32 := do
  let importedModules ← findImports "Cslib.lean"
  let allModules ← forEachModuleInDir' "Cslib" (`Cslib ++ ·)
  let missing := allModules.diff importedModules.toList
  let withoutExceptions := missing.diff exceptions
  let ret := withoutExceptions.length.toUInt32
  if ret ≠ 0 then
    .eprintln s!"error: the following module(s) are not imported in Cslib.lean: {withoutExceptions}"
  return ret
