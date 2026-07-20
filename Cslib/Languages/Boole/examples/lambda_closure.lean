import StrataBoole.MetaVerifier
import Smt

open Strata

/-
Verification example for lambda expressions in Boole spec positions:
- `fun x : T => body` parses as Core's `lambda` op and lowers to a Core
  `.abs` node via `toCoreExpr`.
- `(f)(x)` parses as Core's `apply_expr` op and lowers to `.app`.
- Arrow type `T -> U` lowers to Core `.arrow`.
Function-typed *values* stored in variables or passed as procedure arguments
still require the abstract-type encoding used in `higher_order_encoding.lean`.
-/

private def lambdaClosureSeed : StrataDDM.Program :=
#strata
program Boole;

// Lambda in a spec (ensures) position: `(fun x : int => x + 1)(2) == 3`
// uses Core's `lambda` for abstraction and `apply_expr` for application.
procedure use_lambda() returns ()
spec {
  ensures (fun x : int => x + 1)(2) == 3;
}
{
  assert (fun x : int => x + 1)(2) == 3;
};
#end

/-- info:
Obligation: assert_1_819
Property: assert
Result: ✅ pass

Obligation: use_lambda_ensures_0_773
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" lambdaClosureSeed (options := .quiet)

theorem lambdaClosureSeed_smtVCsCorrect : Strata.smtVCsCorrectBoole lambdaClosureSeed := by
  gen_smt_vcs_boole
  all_goals (try smt +mono)
