import StrataBoole.MetaVerifier
import Smt

open Strata

/-
Verification example standing in for opaque/reveal-style proof-visibility
controls (not natively supported in Boole), using an explicit axiom for the
function body instead.
-/

private def opaqueRevealHideSeed : StrataDDM.Program :=
#strata
program Boole;

// Target shape once proof-visibility controls exist in Boole:
//
// opaque function square(x: int) : int { x * x }
//
// procedure opaque_reveal_hide_seed(x: int) returns ()
// {
//   reveal square;
//   assert square(x) == x * x;
//   hide square;
// };

function square(x: int) : int;

axiom (∀ x: int . square(x) == x * x);

procedure opaque_reveal_hide_seed(x: int) returns ()
{
  assert square(x) == x * x;
};
#end

/-- info:
Obligation: assert_1_706
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" opaqueRevealHideSeed (options := .quiet)

theorem opaqueRevealHideSeed_smtVCsCorrect : Strata.smtVCsCorrectBoole opaqueRevealHideSeed := by
  gen_smt_vcs_boole
  all_goals (try smt +mono)
