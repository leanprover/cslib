import StrataBoole.MetaVerifier
import Smt

open Strata

-- Linear search: return an index where `A[idx] == x`, or `-1` if not found.
private def linearSearchPgm : StrataDDM.Program :=
#strata
program Boole;

type Array := Map int int;

procedure LinearSearch(A : Array, n : int, x : int) returns (idx : int)
spec
{
  requires n >= 0;
  ensures (idx == -1 ==> forall k:int :: 0 <= k && k < n ==> A[k] != x);
  ensures (idx != -1 ==> 0 <= idx && idx < n && A[idx] == x);
}
{
  var i : int;

  i := 0;
  idx := -1;

  while (i < n && idx == -1)
    invariant 0 <= i && i <= n
    invariant (idx == -1 ==> forall k:int :: 0 <= k && k < i ==> A[k] != x)
    invariant (idx != -1 ==> 0 <= idx && idx < i && A[idx] == x)
  {
    if (A[i] == x) {
      idx := i;
    }
    i := i + 1;
  }
};
#end

/-- info:
Obligation: entry_invariant_0_0
Property: assert
Result: ✅ pass

Obligation: entry_invariant_0_1
Property: assert
Result: ✅ pass

Obligation: entry_invariant_0_2
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_0_0
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_0_1
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_0_2
Property: assert
Result: ✅ pass

Obligation: LinearSearch_ensures_1_337
Property: assert
Result: ✅ pass

Obligation: LinearSearch_ensures_2_410
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" linearSearchPgm (options := .quiet)

set_option maxHeartbeats 500000 in
theorem linearSearchPgm_smtVCsCorrect : Strata.smtVCsCorrectBoole linearSearchPgm := by
  gen_smt_vcs_boole
  all_goals (try smt +mono)
