import StrataBoole.MetaVerifier
import Smt

open Strata

/-
Verification example exercising the int/nat boundary in Boole using an
abstract (uninterpreted) `nat` predicate with explicit coercions, since Boole
has no native `nat` type.
-/

private def natIntBoundarySeed : StrataDDM.Program :=
#strata
program Boole;

// This file keeps the native-`nat` pressure explicit: abstract `nat`, explicit
// coercions, and an obligation that should become trivial once `nat` is modeled
// natively instead of via uninterpreted functions.

type nat;

function nat_to_int(n: nat) : int;
function int_to_nat(i: int) : nat;

axiom (∀ i: int . 0 <= i ==> nat_to_int(int_to_nat(i)) == i);

procedure nat_int_boundary_seed(n: nat, i: int) returns ()
spec {
  requires 0 <= i;
  ensures nat_to_int(int_to_nat(i)) == i;
}
{
  assume 0 <= nat_to_int(n);
  assert nat_to_int(int_to_nat(i)) == i;
};
#end

/-- info:
Obligation: assert_4_841
Property: assert
Result: ✅ pass

Obligation: nat_int_boundary_seed_ensures_2_766
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" natIntBoundarySeed (options := .quiet)

theorem natIntBoundarySeed_smtVCsCorrect : Strata.smtVCsCorrectBoole natIntBoundarySeed := by
  gen_smt_vcs_boole
  all_goals (try smt +mono)
