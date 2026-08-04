import StrataBoole.MetaVerifier
import Smt

open Strata

/-
Verification example ported from a Verus (Rust) specification, kept
alongside the original source below for direct comparison: the Boole
procedure `findMax` below expresses the identical `requires`/`ensures`
contract and loop invariants as the Verus `find_max` function, demonstrating
that Boole can state and verify the same spec Verus does.

/* Finds and returns the largest integer in a non-empty vector by iterating through its elements. */
#[allow(unused_imports)]
use vstd::prelude::*;
fn main() {}

verus! {

#[verifier::loop_isolation(false)]
fn find_max(nums: Vec<i32>) -> (ret:i32)
    requires
        nums.len() > 0
    ensures
        forall|i: int| 0 <= i && i < nums.len() ==> ret >= nums[i],
        exists|j: int| 0 <= j && j < nums.len() && ret == nums[j]
{
    let mut max = nums[0];
    let mut i = 1;

    while i < nums.len()
        invariant
            nums.len() > 0,
            0 <= i && i <= nums.len(),
            forall|k: int| 0 <= k && k < i ==> max >= nums[k],
            exists|j: int| 0 <= j && j < i && max == nums[j]
        decreases nums.len() - i
    {
        if nums[i] > max {
            max = nums[i];
        }
        i += 1;
    }

    max
}
}
// Score: (1, 0)
// Safe: True

-/

def findMax : StrataDDM.Program :=
#strata
program Boole;

procedure witnessOccurs(nums: Map int int, n: int, idx: int, value: int) returns ()
spec {
  requires 0 <= idx && idx < n;
  requires value == nums[idx];
  ensures ∃ j: int . 0 <= j && j < n && value == nums[j];
}
{
  assume ∃ j: int . 0 <= j && j < n && value == nums[j];
};

procedure findMax (nums: Map int int, n: int) returns (ret: int)
spec {
  requires n > 0;
  ensures ∀ i: int . 0 <= i && i < n ==> ret >= nums[i];
  ensures ∃ j: int . 0 <= j && j < n && ret == nums[j];
}
{
  var max : int := nums[0];
  var maxIndex : int := 0;
  var i : int := 1;

  while (i < n)
    decreases n - i
    invariant (1 <= i && i <= n)
    invariant (∀ k: int . 0 <= k && k < i ==> max >= nums[k])
    invariant (0 <= maxIndex && maxIndex < i && max == nums[maxIndex])
  {
    if (nums[i] > max) {
      max := nums[i];
      maxIndex := i;
    }
    i := i + 1;
  }
  assert 0 <= maxIndex && maxIndex < n && max == nums[maxIndex];
  ret := nums[maxIndex];
  call witnessOccurs(nums, n, maxIndex, ret);
};
#end

/-- info:
Obligation: witnessOccurs_ensures_2_1506
Property: assert
Result: ✅ pass

Obligation: entry_invariant_0_0
Property: assert
Result: ✅ pass

Obligation: entry_invariant_0_1
Property: assert
Result: ✅ pass

Obligation: entry_invariant_0_2
Property: assert
Result: ✅ pass

Obligation: measure_lb_0
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

Obligation: measure_decrease_0
Property: assert
Result: ✅ pass

Obligation: assert_7_2227
Property: assert
Result: ✅ pass

Obligation: callElimAssert_witnessOccurs_requires_0_1443_4
Property: assert
Result: ✅ pass

Obligation: callElimAssert_witnessOccurs_requires_1_1475_5
Property: assert
Result: ✅ pass

Obligation: findMax_ensures_5_1725
Property: assert
Result: ✅ pass

Obligation: findMax_ensures_6_1785
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" findMax (options := .quiet)

theorem findMax_smtVCsCorrect : Strata.smtVCsCorrectBoole findMax := by
  gen_smt_vcs_boole
  all_goals (try smt +mono)
