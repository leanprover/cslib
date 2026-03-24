/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Foundations.Semantics.LTS.Basic

@[expose] public section

/-!
# Notations about LTS
-/

namespace Cslib

meta section

open Lean Elab Meta Command Term

/-- A command to create an `LTS` from a labelled transition `α → β → α → Prop`, robust to use of
`variable `-/
elab "create_lts" lt:ident name:ident : command => do
  liftTermElabM do
    let lt ← realizeGlobalConstNoOverloadWithInfo lt
    let (declName, _) ← mkDeclName (← getCurrNamespace) default name.getId
    let ci ← getConstInfo lt
    forallTelescope ci.type fun args ty => do
      let throwNotLT := throwError m!"type{indentExpr ci.type}\nis not a labelled transition"
      unless args.size ≥ 2 do
        throwNotLT
      unless ← isDefEq (← inferType args[args.size - 3]!) (← inferType args[args.size - 1]!) do
        throwNotLT
      unless (← whnf ty).isProp do
        throwError m!"expecting Prop, not{indentExpr ty}"
      let params := ci.levelParams.map .param
      let lt := mkAppN (.const lt params) args[0:args.size-3]
      let bundle ← mkAppM ``LTS.mk #[lt]
      let value ← mkLambdaFVars args[0:args.size-3] bundle
      let type ← inferType value
      addAndCompile <| .defnDecl {
        name := declName
        levelParams := ci.levelParams
        type
        value
        safety := .safe
        hints := Lean.ReducibilityHints.abbrev
      }
      addTermInfo' name (.const declName params) (isBinder := true)
      addDeclarationRangesFromSyntax declName name

/--
  This command adds transition notations for an `LTS`. This should not usually be called directly,
  but from the `lts` attribute.

  As an example `lts_transition_notation foo "β"` will add the notations "[⬝]⭢β" and "[⬝]↠β"

  Note that the string used will afterwards be registered as a notation. This means that if you have
  also used this as a constructor name, you will need quotes to access corresponding cases, e.g. «β»
  in the above example.
-/
syntax attrKind "lts_transition_notation" ident (str)? : command
macro_rules
  | `($kind:attrKind lts_transition_notation $lts $sym) =>
    `(
      @[nolint docBlame]
      $kind:attrKind notation3 t:39 "["μ"]⭢" $sym:str t':39 => (LTS.Tr.toRelation $lts μ) t t'
      @[nolint docBlame]
      $kind:attrKind notation3 t:39 "["μs"]↠" $sym:str t':39 => (LTS.MTr.toRelation $lts μs) t t'
     )
  | `($kind:attrKind lts_transition_notation $lts) =>
    `(
      @[nolint docBlame]
      $kind:attrKind notation3 t:39 "["μ"]⭢" t':39 => (LTS.Tr.toRelation $lts μ) t t'
      @[nolint docBlame]
      $kind:attrKind notation3 t:39 "["μs"]↠" t':39 => (LTS.MTr.toRelation $lts μs) t t'
     )

/-- This attribute calls the `lts_transition_notation` command for the annotated declaration. -/
syntax (name := lts_attr) "lts" ident (ppSpace str)? : attr

initialize Lean.registerBuiltinAttribute {
  name := `lts_attr
  descr := "Register notation for an LTS"
  add := fun decl stx _ => MetaM.run' do
    let currNamespace ← getCurrNamespace
    match stx with
    | `(attr | lts $lts $sym) =>
        let mut sym := sym
        unless sym.getString.endsWith " " do
          sym := Syntax.mkStrLit (sym.getString ++ " ")
        liftCommandElabM <| do
          modifyScope ({ · with currNamespace })
          Command.elabCommand (← `(create_lts $(mkIdent decl) $lts))
          Command.elabCommand (← `(scoped lts_transition_notation $lts $sym))
    | `(attr | lts $lts) =>
        liftCommandElabM <| do
          modifyScope ({ · with currNamespace })
          Command.elabCommand (← `(create_lts $(mkIdent decl) $lts))
          Command.elabCommand (← `(scoped lts_transition_notation $lts))
    | _ => throwError "invalid syntax for 'lts' attribute"
}

end

end Cslib
