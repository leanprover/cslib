import StrataBoole.MetaVerifier
import Smt

open Strata

/-
Verification example for Boole `datatype` constructors and selectors, using a
small `Option`-like type to exercise construction and field access.
-/

private def datatypeSelectorsSeed : StrataDDM.Program :=
#strata
program Boole;

datatype OptionInt () { None(), Some(val: int) };

// This is the Boole-local analogue of the upstream datatype-constructor /
// selector cases: constructor tests, selector application, and datatype VCs.
//
// This small example passes. Larger datatype examples can still fail on richer
// generated obligations.

procedure datatype_selector_seed(x: int) returns (ok: bool)
spec {
  ensures ok;
}
{
  var o : OptionInt;

  o := Some(x);
  assert OptionInt..isSome(o);
  assert OptionInt..val(o) == x;

  ok := OptionInt..isSome(o) && OptionInt..val(o) == x;
};
#end

/-- info:
Obligation: assert_1_730
Property: assert
Result: ✅ pass

Obligation: assert_assert_2_761_calls_OptionInt..val_0
Property: assert
Result: ✅ pass

Obligation: assert_2_761
Property: assert
Result: ✅ pass

Obligation: set_ok_calls_OptionInt..val_0
Property: assert
Result: ✅ pass

Obligation: datatype_selector_seed_ensures_0_674
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" datatypeSelectorsSeed (options := .quiet)

theorem datatypeSelectorsSeed_smtVCsCorrect : Strata.smtVCsCorrectBoole datatypeSelectorsSeed := by
  gen_smt_vcs_boole
  all_goals (try smt +mono)
