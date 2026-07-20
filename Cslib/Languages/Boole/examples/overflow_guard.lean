import StrataBoole.MetaVerifier
import Smt

open Strata

/-
Verification example for overflow guarding in Boole, using explicit
`fits_u32` predicates in place of native overflow-type checks.
-/

private def overflowGuardSeed : StrataDDM.Program :=
#strata
program Boole;

// Target shape: these `fits_u32` conditions stand in for the dropped
// `HasType(U32, e)` overflow checks that should survive translation.

function fits_u32(i: int) : bool;

axiom (∀ i: int . fits_u32(i) ==> 0 <= i);
axiom (∀ i: int . fits_u32(i) ==> i < 4294967296);

procedure overflow_guard_seed(x: int) returns (y: int)
spec {
  requires fits_u32(x);
  requires fits_u32(x + 1);
  ensures y == x + 1;
  ensures fits_u32(y);
}
{
  y := x + 1;
  assert fits_u32(y);
};
#end

/-- info:
Obligation: assert_6_728
Property: assert
Result: ✅ pass

Obligation: overflow_guard_seed_ensures_4_665
Property: assert
Result: ✅ pass

Obligation: overflow_guard_seed_ensures_5_687
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" overflowGuardSeed (options := .quiet)

theorem overflowGuardSeed_smtVCsCorrect : Strata.smtVCsCorrectBoole overflowGuardSeed := by
  gen_smt_vcs_boole
  all_goals (try smt +mono)
