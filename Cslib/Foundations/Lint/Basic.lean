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

/-- The root of the module name defining `declName`, or of the main module if `declName` is
declared in the current file. -/
meta def packageRoot (env : Environment) (declName : Name) : Name :=
  match env.getModuleIdxFor? declName with
  | some i => (env.header.moduleNames[i.toNat]?.getD .anonymous).getRoot
  | none => env.mainModule.getRoot

/-- Whether the namespace `ns` exists upstream, that is, whether some imported constant from a
module outside the package `pkg` lies strictly under `ns`. -/
meta def isUpstreamNamespace (env : Environment) (pkg ns : Name) : Bool :=
  env.constants.map₁.fold (init := false) fun found c _ =>
    found || (ns.isPrefixOf c && c != ns &&
      match env.getModuleIdxFor? c with
      | some i => !pkg.isPrefixOf (env.header.moduleNames[i.toNat]?.getD .anonymous)
      | none => false)

/--
A linter for checking that new declarations fall under some preexisting namespace: either the root
of a namespace of the library (such as `Cslib`), or an existing upstream namespace (such as
`Equivalence` from core, for `_root_.Equivalence.foo`).

Private declarations, which include all non-`public` declarations of a `module`, are skipped:
they are not exported, and their internal names are prefixed with `_private`.
-/
@[env_linter]
public meta def topNamespace : Batteries.Tactic.Lint.Linter where
  noErrorsFound := "No declarations are outside a namespace."
  errorsFound := "TOP LEVEL DECLARATIONS:"
  test declName := do
    if isPrivateName declName then return none
    if ← isAutoDecl declName then return none
    let env ← getEnv
    if ← isImplicitReducible declName then return none
    let nss := env.getNamespaces
    let top := nss.fold (init := (∅ : NameSet)) fun tot n =>
      match n.components with
      | r::_::_ => tot.insert r
      | _ => tot
    if top.contains declName.components[0]! then
      return none
    -- Declarations extending an existing upstream namespace are namespaced.
    if !declName.getPrefix.isAnonymous &&
        isUpstreamNamespace env (packageRoot env declName) declName.getRoot then
      return none
    return m!"is not namespaced."

end Cslib.Lint
