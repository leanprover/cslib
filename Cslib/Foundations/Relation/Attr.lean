/-
Copyright (c) 2025 Fabrizio Montesi and Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Thomas Waring, Chris Henson
-/

module

public import Cslib.Init
public import Lean.Elab.Command
public import Mathlib.Util.Notation3
public import Mathlib.Logic.Relation

/-! # Relations: Attributes

This module defines the `reduction_sys` attribute used for creating relation notations.

-/

public meta section

namespace Relation

open Lean Elab Meta Command Term

/--
  This command adds notations for relations. This should not usually be called directly, but from
  the `reduction_sys` attribute.

  As an example `reduction_notation foo "β"` will add the notations "⭢β" and "↠β".

  Note that the string used will afterwards be registered as a notation. This means that if you have
  also used this as a constructor name, you will need quotes to access corresponding cases, e.g. «β»
  in the above example.
-/
syntax attrKind "reduction_notation" ident (str)? : command
macro_rules
  | `($kind:attrKind reduction_notation $rel $sym) =>
    `(
      @[nolint docBlame]
      $kind:attrKind notation3 t:39 " ⭢" $sym:str t':39 => $rel t t'
      @[nolint docBlame]
      $kind:attrKind notation3 t:39 " ↠" $sym:str t':39 => Relation.ReflTransGen $rel t t'
     )
  | `($kind:attrKind reduction_notation $rel) =>
    `(
      @[nolint docBlame]
      $kind:attrKind notation3 t:39 " ⭢ " t':39 => $rel t t'
      @[nolint docBlame]
      $kind:attrKind notation3 t:39 " ↠ " t':39 => Relation.ReflTransGen $rel t t'
     )


/--
  This attribute calls the `reduction_notation` command for the annotated declaration, such as in:

  ```
  @[reduction_sys "ₙ", simp]
  def PredReduction (a b : ℕ) : Prop := a = b + 1
  ```
-/
syntax (name := reductionSys) "reduction_sys" (ppSpace str)? : attr

initialize Lean.registerBuiltinAttribute {
  name := `reductionSys
  descr := "Register notation for a relation and its closures."
  add := fun decl stx _ => MetaM.run' do
    let currNamespace ← getCurrNamespace
    match stx with
    | `(attr | reduction_sys $sym) =>
        let mut sym := sym
        unless sym.getString.endsWith " " do
          sym := Syntax.mkStrLit (sym.getString ++ " ")
        liftCommandElabM <| do
          modifyScope ({ · with currNamespace })
          elabCommand (← `(scoped reduction_notation $(mkIdent decl) $sym))
    | `(attr | reduction_sys) =>
        liftCommandElabM <| do
          modifyScope ({ · with currNamespace })
          elabCommand (← `(scoped reduction_notation $(mkIdent decl)))
    | _ => throwError "invalid syntax for 'reduction_sys' attribute"
}

end Relation

end
