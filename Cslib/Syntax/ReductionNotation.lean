import Mathlib

open Lean Lean.Elab Lean.Meta

/-- 
  This command adds notations for a relation, its reflexive transitive closure, and its equivalence
  closure. This should not usually be called directly, but from the `reduction` attribute. 

  As an example `reduction_notation foo "β"` will add the notations "⇢β", "↠β", and "≈β".

  Note that the string used will afterwards be registered as a notation. This means that if you have
  also used this as a constructor name, you will need quotes to access corresponding cases, e.g. «β»
  in the above example.
-/
syntax "reduction_notation" ident Lean.Parser.Command.notationItem : command
macro_rules
  | `(reduction_notation $rel $sym) => 
    `(
      notation:39 t " ⇢"$sym t' => $rel t t'
      notation:39 t " ↠"$sym t' => Relation.ReflTransGen $rel t t'
      notation:39 t " ≈"$sym t' => Relation.EqvGen $rel t t'
     )

/-- 
  This attribute calls the `reduction_notation` command for the annotated declaration, such as in:

  ```
  @[reduction "ₙ"]
  def PredReduction (a b : ℕ) : Prop := a = b + 1
  ```
-/
syntax (name := reduction) "reduction" Lean.Parser.Command.notationItem : attr

initialize Lean.registerBuiltinAttribute {
  name := `reduction
  descr := "Register notation for a relation and its closures."
  add := fun decl stx _ => MetaM.run' do
    let `(attr | reduction $sym) := stx 
     | throwError "invalid syntax for 'reduction' attribute"
    let cmd ← `(reduction_notation $(mkIdent decl) $sym)
    liftCommandElabM <| Command.elabCommand cmd
}
