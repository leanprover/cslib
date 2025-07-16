import Mathlib
import Cslib.Semantics.ReductionSystem.Basic

open Lean Lean.Elab Lean.Meta

/-- 
  This command adds notations for a `ReductionSystem.Red` and
  `ReductionSystem.MRed`. This should not usually be called directly, but from
  the `reduction` attribute. 

  As an example `reduction_notation foo "β"` will add the notations "⇢β", "↠β", and "≈β".

  Note that the string used will afterwards be registered as a notation. This means that if you have
  also used this as a constructor name, you will need quotes to access corresponding cases, e.g. «β»
  in the above example.
-/
syntax "reduction_notation" ident Lean.Parser.Command.notationItem : command
macro_rules
  | `(reduction_notation $rs $sym) => 
    `(
      notation:39 t " ⭢"$sym t' => (ReductionSystem.Red  $rs) t t'
      notation:39 t " ↠"$sym t' => (ReductionSystem.MRed $rs) t t'
     )

/-- 
  This attribute calls the `reduction_notation` command for the annotated declaration, such as in:

  ```
  @[reduction rs "ₙ", simp]
  def PredReduction (a b : ℕ) : Prop := a = b + 1
  ```
-/
syntax (name := reduction) "reduction" ident Lean.Parser.Command.notationItem : attr

initialize Lean.registerBuiltinAttribute {
  name := `reduction
  descr := "Register notation for a relation and its closures."
  add := fun decl stx _ => MetaM.run' do
    let `(attr | reduction $rs $sym) := stx 
     | throwError "invalid syntax for 'reduction' attribute"
    let reduction_system_decl ← `(
      def $rs := ({Red := $(mkIdent decl)} : ReductionSystem _)
    )
    liftCommandElabM <| Command.elabCommand reduction_system_decl
    liftCommandElabM <| Command.elabCommand (← `(reduction_notation $rs $sym))
}
