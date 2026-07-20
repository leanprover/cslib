import StrataBoole.MetaVerifier
import Smt

namespace Strata

/-
Verification example for `const` declarations, global variables, and
if/else branching (loop and arithmetic reasoning are covered by
`ineq.lean`).
-/

private def constants :=
#strata
program Boole;

// verifies const declarations plus simple branching control flow
// (loop and arithmetic reasoning are covered by ineq.lean)

var GlobalFlag : bool;

const A: int;
const B: int;
const C: int;

procedure Join (b : bool) returns ()
spec
{
  modifies GlobalFlag;
}
{
  var x: int;
  var y: int;
  var z: int;

  GlobalFlag := true;
  x := 3;
  y := 4;
  z := x + y;

  if (b) {
    x := x + 1;
  } else {
    y := 4;
  }

  assert y == 4;
  assert z == 7;
  assert GlobalFlag == true;

};

#end

/-- info:
Obligation: assert_0_687
Property: assert
Result: ✅ pass

Obligation: assert_1_704
Property: assert
Result: ✅ pass

Obligation: assert_2_721
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" constants (options := .quiet)

theorem constants_smtVCsCorrect : Strata.smtVCsCorrectBoole constants := by
  gen_smt_vcs_boole
  all_goals (try smt +mono)
