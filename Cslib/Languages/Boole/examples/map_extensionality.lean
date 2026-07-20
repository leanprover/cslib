import StrataBoole.MetaVerifier
import Smt
import StrataBoole.Verify

open Strata
open Lambda

/-
Verification example for Boole's extensional-equality operator on `Map` types:
`a =~= b` lowers to `∀ i . a[i] == b[i]`.
-/

private def mapExtensionalitySeed : StrataDDM.Program :=
#strata
program Boole;

// `a =~= b` lowers to `∀ i: int . a[i] == b[i]`.
// Remaining gap: named map type synonyms do not yet work with `=~=`.

procedure map_extensionality_seed(a: Map int int, b: Map int int) returns ()
spec {
  requires ∀ i: int . a[i] == b[i];
  ensures a =~= b;
}
{
  assert a =~= b;
};
#end

/-- info:
Obligation: assert_2_578
Property: assert
Result: ✅ pass

Obligation: map_extensionality_seed_ensures_1_555
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" mapExtensionalitySeed (options := .quiet)

/--
The VCs are provable regardless of `useArrayTheory`: under `true` the `Map` is
encoded as an SMT array (denoted by `SmtArray`), under `false` as an
uninterpreted sort with an axiomatized `select` function.
-/
theorem mapExtensionalitySeed_smtVCsCorrect : ∀ useArrayTheory,
    Strata.smtVCsCorrectBoole mapExtensionalitySeed { useArrayTheory } := by
  intro useArrayTheory
  cases useArrayTheory
  case false =>
    gen_smt_vcs_boole
    all_goals
      intro Map inst select a b hPointwise i
      exact hPointwise i
  case true =>
    gen_smt_vcs_boole
    all_goals
      intro a b hPointwise i
      exact hPointwise i

/-!
Regression test for extensional equality nested under an outer quantifier.

The Boole frontend lowers `a =~= b` to `∀ i . a[i] == b[i]`. When `a` and `b`
are themselves outer bound variables, introducing that extra quantifier must
lift their de Bruijn indices so they keep referring to the outer map binders
instead of the new index binder.
-/

private def quantifiedMapExtensionalityCaptureSeed : StrataDDM.Program :=
#strata
program Boole;

procedure quantified_map_extensionality_capture() returns ()
spec {
  ensures ∀ a: Map int int, b: Map int int . a =~= b;
}
{
};
#end

private def mkExprApp (f : Core.Expression.Expr) (args : List Core.Expression.Expr) :
    Core.Expression.Expr :=
  Lambda.LExpr.mkApp () f args

private def loweredQuantifiedMapExtensionalityCapture? : Option Core.Expression.Expr := do
  let booleProg <- (Strata.Boole.getProgram quantifiedMapExtensionalityCaptureSeed).toOption
  let coreProg <-
    (Strata.Boole.toCoreProgram booleProg quantifiedMapExtensionalityCaptureSeed.globalContext).toOption
  coreProg.decls.findSome? fun decl =>
    match decl.getProc? with
    | some proc =>
        if proc.header.name == "quantified_map_extensionality_capture" then
          proc.spec.postconditions.values.head?.map (·.expr)
        else
          none
    | none => none

private def expectedQuantifiedMapExtensionalityCapture : Core.Expression.Expr :=
  let mapIntInt := Core.mapTy .int .int
  let lhs := mkExprApp Core.mapSelectOp [.bvar () 2, .bvar () 0]
  let rhs := mkExprApp Core.mapSelectOp [.bvar () 1, .bvar () 0]
  .quant () .all "" (some mapIntInt) (.bvar () 0)
    (.quant () .all "" (some mapIntInt) (.bvar () 0)
      (.quant () .all "" (some .int) lhs (.eq () lhs rhs)))

#guard loweredQuantifiedMapExtensionalityCapture? == some expectedQuantifiedMapExtensionalityCapture
