import StrataBoole.MetaVerifier
import Smt

open Strata

-- Two-sum (quadratic scan).
--
-- Returns `(i, j)` with `0 ≤ i < j < n` and `A[i] + A[j] == t`, or `(-1, -1)` if no pair is found.
--
-- Note: this example proves *soundness* of the returned indices, not *completeness*
-- (i.e. it does not prove that `(-1, -1)` implies there is no solution).
private def twoSumPgm : StrataDDM.Program :=
#strata
program Boole;

type Array := Map int int;

procedure TwoSum(A : Array, n : int, t : int) returns (ri : int, rj : int)
spec
{
  requires n >= 0;

  // Soundness: if we return indices, they denote a valid solution.
  ensures (ri != -1) ==> 0 <= ri && ri < rj && rj < n && A[ri] + A[rj] == t;
  // "Not found" is represented as (-1, -1).
  ensures (ri == -1) ==> rj == -1;
  ensures (rj == -1) ==> ri == -1;
}
{
  var i : int;
  var j : int;
  var found : bool;

  ri := -1;
  rj := -1;
  found := false;

  i := 0;
  while (i < n)
    invariant 0 <= i && i <= n
    invariant (found == false) ==> (ri == -1 && rj == -1)
    invariant (found == true) ==> 0 <= ri && ri < rj && rj < n && A[ri] + A[rj] == t
  {
    if (found == false) {
      j := i + 1;
      while (j < n)
        invariant i + 1 <= j && j <= n
        invariant (found == false) ==> (ri == -1 && rj == -1)
        invariant (found == true) ==> 0 <= ri && ri < rj && rj < n && A[ri] + A[rj] == t
      {
        if (found == false && A[i] + A[j] == t) {
          ri := i;
          rj := j;
          found := true;
        }
        j := j + 1;
      }
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

Obligation: entry_invariant_1_0
Property: assert
Result: ✅ pass

Obligation: entry_invariant_1_1
Property: assert
Result: ✅ pass

Obligation: entry_invariant_1_2
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_1_0
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_1_1
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_1_2
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

Obligation: TwoSum_ensures_1_622
Property: assert
Result: ✅ pass

Obligation: TwoSum_ensures_2_744
Property: assert
Result: ✅ pass

Obligation: TwoSum_ensures_3_779
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" twoSumPgm (options := .quiet)

set_option maxHeartbeats 1000000 in
theorem twoSumPgm_smtVCsCorrect : Strata.smtVCsCorrectBoole twoSumPgm := by
  gen_smt_vcs_boole
  all_goals (first | omega | trivial | grind)
