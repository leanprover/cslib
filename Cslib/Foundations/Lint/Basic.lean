/-
Copyright (c) 2025 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Batteries.Tactic.Lint.Basic
public import Lean.Message

namespace Cslib.Lint

open Lean Meta Std Batteries.Tactic.Lint

/-- A linter for checking that new declarations fall under some preexisting namespace. -/
@[env_linter]
public meta def topNamespace : Batteries.Tactic.Lint.Linter where
  noErrorsFound := "No declarations are outside a namespace."
  errorsFound := "TOP LEVEL DECLARATIONS:"
  test declName := do
    if ← isAutoDecl declName then return none
    let env ← getEnv
    if ← isImplicitReducible declName then return none
    let nss := env.getNamespaceSet
    let top := nss.fold (init := (∅ : NameSet)) fun tot n =>
      match n.components with
      | r::_::_ => tot.insert r
      | _ => tot
    if top.contains declName.components[0]! then
      return none
    else
      return m!"is not namespaced."

end Cslib.Lint
