-- This imports the necessary Strata modules for working with Boole programs and verification.
import StrataBoole.MetaVerifier
import Smt

open Strata

def maxExample : StrataDDM.Program :=
#strata
program Boole; // Specify that this is a Boole program.

procedure max (x: int, y: int) returns (r: int)
spec {
  ensures r >= x && r >= y;
  ensures r == x || r == y;
}
{
  if (x >= y) {
    r := x;
  }
  else {
    r := y;
  }
};
#end

-- Approach 1: Using an SMT solver to verify the VCs.
/-- info:
Obligation: max_ensures_0_312
Property: assert
Result: ✅ pass

Obligation: max_ensures_1_340
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" maxExample (options := .quiet)

-- Approach 2: Using Lean tactics to verify the VCs.
theorem maxExample_smtVCsCorrect : Strata.smtVCsCorrectBoole maxExample := by
  gen_smt_vcs_boole
  all_goals (try smt +mono)
