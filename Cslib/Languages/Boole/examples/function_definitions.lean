import StrataBoole.MetaVerifier
import Smt

open Strata

/-
Verification example for `function ... { body }` definitions that call one
another (`is_incremented_positive` calls `increment`): the verifier unfolds
both bodies to discharge the procedure's postcondition.
-/

private def function_definitions :=
#strata
program Boole;

function increment(x:int) : int
  { x + 1 }
function is_incremented_positive(x:int) : bool
  { increment(x) > 0 }

procedure test(x:int) returns (r:int)
spec {
  ensures (r > 0);
}
{
  if (is_incremented_positive(x)) {
    r := increment(x);
  } else {
    r := 1;
  }
};

#end

/-- info:
Obligation: test_ensures_0_493
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" function_definitions (options := .quiet)

theorem function_definitions_smtVCsCorrect : Strata.smtVCsCorrectBoole function_definitions := by
  gen_smt_vcs_boole
  all_goals (first | smt | (intro x _ _; split <;> omega))