/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

/-!
# Test Runner

This script runs all CSLib tests including:
- Building the CslibTests library
- Running init imports validation
-/

def main (_ : List String) : IO UInt32 := do
  -- Run Cslib.lean completeness check
  IO.println "Checking Cslib.lean completeness..."
  let completeResult ← IO.Process.spawn {
    cmd := "lake"
    args := #["exe", "checkCslibComplete"]
  } >>= (·.wait)

  if completeResult != 0 then
    IO.eprintln "\n✗ Cslib.lean completeness check failed"
    return completeResult

  -- Run init imports check
  IO.println "\nChecking init imports..."
  let checkResult ← IO.Process.spawn {
    cmd := "lake"
    args := #["exe", "checkInitImports"]
  } >>= (·.wait)

  if checkResult != 0 then
    IO.eprintln "\n✗ Init imports check failed"
    return checkResult

  IO.println "\n✓ All tests passed"
  return 0
