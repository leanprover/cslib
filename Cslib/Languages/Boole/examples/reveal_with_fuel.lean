import StrataBoole.MetaVerifier
import Smt

open Strata

/-
Verification example standing in for bounded recursive unfolding
(`reveal_with_fuel`-style, not natively supported in Boole), using an
uninterpreted placeholder function instead.
-/

private def revealWithFuelSeed : StrataDDM.Program :=
#strata
program Boole;

// Target shape once bounded recursive unfolding is supported:
//
// rec function pow2(n: int) : int
// {
//   if n == 0 then 1 else 2 * pow2(n - 1)
// }
//
// procedure reveal_with_fuel_seed(n: int) returns ()
// spec {
//   requires 0 <= n;
//   ensures pow2(n) >= 1;
// }
// {
//   assert pow2(n) >= 1;
// };

function pow2(n: int) : int;

procedure reveal_with_fuel_seed(n: int) returns ()
spec {
  ensures true;
}
{
  assert pow2(n) == pow2(n);
};
#end

/-- info:
Obligation: assert_1_744
Property: assert
Result: ✅ pass

Obligation: reveal_with_fuel_seed_ensures_0_724
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" revealWithFuelSeed (options := .quiet)

theorem revealWithFuelSeed_smtVCsCorrect : Strata.smtVCsCorrectBoole revealWithFuelSeed := by
  gen_smt_vcs_boole
  all_goals (try smt +mono)
