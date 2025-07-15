import Mathlib

open Lean Lean.Elab Lean.Meta

/-- 
  This command adds notations for a relation, its reflexive transitive closure, and its equivalence
  closure. This should not usually be called directly, but as an attribute. 

  As an example `reduce_notation foo "β"` will add the notations "⇢β", "↠β", and "≈β".

  Note that the string used will afterwards be registered as a notation. This means that if you have
  also used this as a constructor name, you will need quotes to access corresponding cases, e.g. «β»
  in the above example.
-/
syntax "reduce_notation" ident Lean.Parser.Command.notationItem : command
macro_rules
  | `(reduce_notation $rel $sym) => 
    `(
      notation:39 t " ⇢"$sym t' => $rel t t'
      notation:39 t " ↠"$sym t' => Relation.ReflTransGen $rel t t'
      notation:39 t " ≈"$sym t' => Relation.EqvGen $rel t t'
     )

/-- 
  This attribute calls the `reduce_notation` command for the annotated declaration, such as in:

  ```
  @[reduce_notation "ₙ"]
  def PredReduction (a b : ℕ) : Prop := a = b + 1
  ```
-/
syntax (name := reduce_notation_attr) "reduce_notation" Lean.Parser.Command.notationItem : attr

initialize Lean.registerBuiltinAttribute {
  name := `reduce_notation_attr
  descr := "Register notation for a relation and its closures."
  add := fun decl stx kind => MetaM.run' do
    let `(attr | reduce_notation $sym) := stx 
     | throwError "invalid syntax for 'reduce_notation' attribute"
    let cmd ← `(reduce_notation $(mkIdent decl) $sym)
    liftCommandElabM <| Command.elabCommand cmd
}
