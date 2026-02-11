import Strata.MetaVerifier
import Smt

open Strata

def maxExample : Strata.Program :=
#strata
program Boole;

procedure loopSimple (x: int, y: int) returns (r: int)
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

#eval Strata.Boole.verify "cvc5" maxExample

open Strata.SMT

theorem maxExample_smtVCsCorrect : smtVCsCorrect maxExample := by
  gen_smt_vcs
  all_goals smt
