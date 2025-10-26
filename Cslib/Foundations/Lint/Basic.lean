/-
Copyright (c) 2025 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

import Mathlib

namespace Cslib.Lint

open Lean Meta Std Batteries.Tactic.Lint Elab Command

/-- A linter for checking that new declarations fall under some preexisting namespace. -/
@[env_linter]
def topNamespace : Batteries.Tactic.Lint.Linter where
  noErrorsFound := "No declarations are outside a namespace."
  errorsFound := "TOP LEVEL DECLARATIONS:"
  test declName := do
    if ← isAutoDecl declName then return none
    let env ← getEnv
    if isGlobalInstance env declName then return none
    let nss := env.getNamespaceSet
    let top := nss.fold (init := (∅ : NameSet)) fun tot n =>
      match n.components with
      | r::_::_ => tot.insert r
      | _ => tot    
    if top.contains declName.components[0]! then
      return none
    else
      let ty := env.find? declName |>.get! |>.type
      /- TODO: this is a temporary allowance for unscoped notations generated
         for `LTS` and `ReductionSystem`. -/
      if ty == .const ``Lean.TrailingParserDescr [] then
        return none
      else
        return m!"{declName} is not namespaced."

/-- A linter that checks if the current module imports at least one `Cslib` module.
This ensures all files are connected to the library's import graph and receive `Cslib.Init`. -/
@[env_linter]
def checkInitImports : Batteries.Tactic.Lint.Linter where
  noErrorsFound := "All modules import at least one Cslib module."
  errorsFound := "MISSING CSLIB IMPORT:"
  test _declName := do
    -- Only check the first declaration in each module
    let env ← getEnv
    let imports := env.imports.map (·.module)

    -- Check if any import starts with `Cslib`
    let hasCslibImport := imports.any fun imp =>
      match imp.components with
      | `Cslib :: _ => true
      | _ => false

    if hasCslibImport then
      return none
    else
      -- Get current module name
      let moduleName := env.mainModule
      return m!"Module {moduleName} does not import any Cslib module. \
                Consider importing Cslib.Init or another Cslib module."

end Cslib.Lint
