-- This imports the necessary Strata modules for working with Boole programs and verification.
import Strata.MetaVerifier
import Smt

open Strata

def maxExample : Strata.Program :=
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
#eval Strata.Boole.verify "cvc5" maxExample

-- Approach 2: Using Lean tactics to verify the VCs.
theorem maxExample_smtVCsCorrect : Strata.smtVCsCorrect maxExample := by
  gen_smt_vcs
  all_goals smt
