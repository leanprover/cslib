/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Thomas Waring
-/

import Mathlib.Logic.Relation

/-!
# Reduction System

A reduction system is an operational semantics expressed as a relation between terms.
-/

universe u

/--
A reduction system is a relation between `Term`s.
-/
structure ReductionSystem (Term : Type u) where
  /-- The reduction relation. -/
  Red : Term → Term → Prop


section MultiStep

/-! ## Multi-step reductions -/

/-- Multi-step reduction relation. -/
abbrev ReductionSystem.MRed (rs : ReductionSystem Term) :=
  Relation.ReflTransGen rs.Red

/-- All multi-step reduction relations are reflexive. -/
@[refl]
theorem ReductionSystem.MRed.refl (rs : ReductionSystem Term) (t : Term) : rs.MRed t t :=
  Relation.ReflTransGen.refl

/-- Any reduction is a multi-step -/
theorem ReductionSystem.MRed.single (rs : ReductionSystem Term) (h : rs.Red a b) :
  rs.MRed a b :=
  Relation.ReflTransGen.single h

open Relation Relation.ReflTransGen

-- these instances allow us to switch between single and multistep reductions in a `calc` block
instance {α} (R : α → α → Prop) : Trans R (ReflTransGen R) (ReflTransGen R) where
  trans := head

instance {α} (R : α → α → Prop) : Trans (ReflTransGen R) R (ReflTransGen R) where
  trans := tail

instance (rs : ReductionSystem Term) : Trans rs.Red rs.MRed rs.MRed := by infer_instance
instance (rs : ReductionSystem Term) : Trans rs.MRed rs.Red rs.MRed := by infer_instance

end MultiStep

open Lean Elab Meta Command Term

-- thank you to Kyle Miller for this: 
-- https://leanprover.zulipchat.com/#narrow/channel/239415-metaprogramming-.2F-tactics/topic/Working.20with.20variables.20in.20a.20command/near/529324084

/-- A command to create a `ReductionSystem` from a relation, robust to use of `variable `-/
elab "create_reduction_sys" rel:ident name:ident : command => do
  liftTermElabM do
    let rel ← realizeGlobalConstNoOverloadWithInfo rel
    let ci ← getConstInfo rel
    forallTelescope ci.type fun args ty => do
      let throwNotRelation := throwError m!"type{indentExpr ci.type}\nis not a relation"
      unless args.size ≥ 2 do
        throwNotRelation
      unless ← isDefEq (← inferType args[args.size - 2]!) (← inferType args[args.size - 1]!) do
        throwNotRelation
      unless (← whnf ty).isProp do
        throwError m!"expecting Prop, not{indentExpr ty}"
      let params := ci.levelParams.map .param
      let rel := mkAppN (.const rel params) args[0:args.size-2]
      let bundle ← mkAppM ``ReductionSystem.mk #[rel]
      let value ← mkLambdaFVars args[0:args.size-2] bundle
      let type ← inferType value
      addAndCompile <| .defnDecl {
        name := name.getId
        levelParams := ci.levelParams
        type
        value
        safety := .safe
        hints := Lean.ReducibilityHints.abbrev
      }
      addTermInfo' name (.const name.getId params) (isBinder := true)
      addDeclarationRangesFromSyntax name.getId name
 
/-- 
  This command adds notations for a `ReductionSystem.Red` and `ReductionSystem.MRed`. This should
  not usually be called directly, but from the `reduction_sys` attribute. 

  As an example `reduction_notation foo "β"` will add the notations "⭢β" and "↠β".

  Note that the string used will afterwards be registered as a notation. This means that if you have
  also used this as a constructor name, you will need quotes to access corresponding cases, e.g. «β»
  in the above example.
-/
syntax "reduction_notation" ident (Lean.Parser.Command.notationItem)? : command
macro_rules
  | `(reduction_notation $rs $sym) => 
    `(
      notation:39 t " ⭢"$sym t' => (ReductionSystem.Red  $rs) t t'
      notation:39 t " ↠"$sym t' => (ReductionSystem.MRed $rs) t t'
     )
  | `(reduction_notation $rs) => 
    `(
      notation:39 t " ⭢" t' => (ReductionSystem.Red  $rs) t t'
      notation:39 t " ↠" t' => (ReductionSystem.MRed $rs) t t'
     )


/-- 
  This attribute calls the `reduction_notation` command for the annotated declaration, such as in:

  ```
  @[reduction rs "ₙ", simp]
  def PredReduction (a b : ℕ) : Prop := a = b + 1
  ```
-/
syntax (name := reduction_sys) "reduction_sys" ident (Lean.Parser.Command.notationItem)? : attr

initialize Lean.registerBuiltinAttribute {
  name := `reduction_sys
  descr := "Register notation for a relation and its closures."
  add := fun decl stx _ => MetaM.run' do
    match stx with
    | `(attr | reduction_sys $rs $sym) =>
        liftCommandElabM <| Command.elabCommand (← `(create_reduction_sys $(mkIdent decl) $rs))
        liftCommandElabM <| Command.elabCommand (← `(reduction_notation $rs $sym))
    | `(attr | reduction_sys $rs) =>
        liftCommandElabM <| Command.elabCommand (← `(create_reduction_sys $(mkIdent decl) $rs))
        liftCommandElabM <| Command.elabCommand (← `(reduction_notation $rs))
    | _ => throwError "invalid syntax for 'reduction_sys' attribute"
}
