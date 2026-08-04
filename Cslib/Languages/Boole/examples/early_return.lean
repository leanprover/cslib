import StrataBoole.MetaVerifier
import Smt

open Strata

/-
Verification example for early return in Boole via `exit functionName;`:
  1. The Boole → Core translator wraps every procedure body in a labeled
     block named after the procedure.
  2. `exit functionName;` in the body exits that block, skipping any
     remaining statements — i.e., an early return.
  3. Output variables must be assigned before the exit, as with any early
     return style.
-/

private def earlyReturnSeed : StrataDDM.Program :=
#strata
program Boole;

procedure abs_seed(x: int) returns (r: int)
spec {
  ensures 0 <= r;
}
{
  if (x < 0) {
    r := 0 - x;
    exit abs_seed;
  }
  r := x;
};
#end

/-- info:
Obligation: abs_seed_ensures_0_593
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" earlyReturnSeed (options := .quiet)

theorem earlyReturnSeed_smtVCsCorrect : Strata.smtVCsCorrectBoole earlyReturnSeed := by
  gen_smt_vcs_boole
  all_goals (try smt +mono)
