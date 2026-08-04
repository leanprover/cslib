import StrataBoole.MetaVerifier
import Smt

open Strata

/-
Verification example encoding higher-order function values in Boole via a
first-order uninterpreted `apply` wrapper (`FnIntInt`), since Boole has no
native function-valued terms.
-/

private def higherOrderSeed : StrataDDM.Program :=
#strata
program Boole;

// Target shape: higher-order values and calls without an explicit `apply`
// wrapper.

type FnIntInt;

function apply(f: FnIntInt, x: int) : int;

procedure higher_order_seed(f: FnIntInt, x: int) returns (y: int)
spec {
  ensures y == apply(f, x);
}
{
  y := apply(f, x);
};
#end

/-- info:
Obligation: higher_order_seed_ensures_0_541
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" higherOrderSeed (options:=.quiet)

theorem higherOrderSeed_smtVCsCorrect : Strata.smtVCsCorrectBoole higherOrderSeed := by
  gen_smt_vcs_boole
  all_goals (try smt +mono)
