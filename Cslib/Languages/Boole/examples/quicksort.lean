import StrataBoole.MetaVerifier
import Smt

namespace Strata

-- CLRS Chapter 7: QUICKSORT
-- Pseudo-code adapted from CLRS book (2nd edition), page 146
-- Pseudo-code:
-- QUICKSORT(A, p, r)
-- 1  if p < r
-- 2    then q <-- PARTITION(A, p, r)
-- 3    QUICKSORT(A, p, q - 1)
-- 4    QUICKSORT(A, q + 1, r)
-- To sort an entire array A, the initial call is QUICKSORT(A, 1, length[A])

-- PARTITION(A, p, r)
-- 1  x <-- A[r]
-- 2  i <-- p - 1
-- 3  for j <-- p to r - 1
-- 4    do if A[j] <= x
-- 5        then i <-- i + 1
-- 6            exchange A[i] <-> A[j]
-- 7  exchange A[i + 1] <-> A[r]
-- 8  return i + 1

private def quickSort :=
#strata
program Boole;

var A: Map int int;

procedure Quicksort(p: int, r: int) returns ()
spec
{
  requires p >= 1;
  requires r >= p;
  modifies A;
}
{
  if (p < r) {
    var q: int;
    call q := Partition(p, r);
    if (p < q) {
        call Quicksort(p, q - 1);
    }
    if (q < r) {
        call Quicksort(q + 1, r);
    }
  }
};

procedure Partition(p: int, r: int) returns (q: int)
spec
{
  requires p >= 1;
  requires r >= p;
  modifies A;
  ensures q >= p;
  ensures q <= r;
}
{
  var x: int;
  var i: int;
  var temp: int;
  var temp2: int;

  x := A[r];
  i := p - 1;

  for j:int := p to r - 1
    invariant p - 1 <= i
    invariant i < j
    invariant j <= r
  {
    if (A[j] <= x) {
      i := i + 1;
      temp := A[i];
      A := A[i := A[j]];
      A := A[j := temp];
    }
  }

  temp2 := A[i + 1];
  A[i+1] := A[r];
  A[r] := temp2;

  q := i + 1;
};

#end

/-- info:
Obligation: callElimAssert_Partition_requires_2_1039_17
Property: assert
Result: ✅ pass

Obligation: callElimAssert_Partition_requires_3_1058_18
Property: assert
Result: ✅ pass

Obligation: callElimAssert_Quicksort_requires_0_739_10
Property: assert
Result: ✅ pass

Obligation: callElimAssert_Quicksort_requires_1_758_11
Property: assert
Result: ✅ pass

Obligation: callElimAssert_Quicksort_requires_0_739_4
Property: assert
Result: ✅ pass

Obligation: callElimAssert_Quicksort_requires_1_758_5
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

Obligation: arbitrary_iter_maintain_invariant_0_0
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_0_1
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_0_2
Property: assert
Result: ✅ pass

Obligation: Partition_ensures_4_1091
Property: assert
Result: ✅ pass

Obligation: Partition_ensures_5_1109
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" quickSort (options := .quiet)

-- TODO: re-enable once Strata's `gen_smt_vcs_boole` is fixed (modifies-global threading mis-binds
-- `Partition`'s `p` formal to `A`, producing a hard type error before any tactic runs: "expected
-- Int, got SmtArray Int Int"); the cvc5 `#eval verify` above still proves it.
/-
theorem quickSort_smtVCsCorrect : Strata.smtVCsCorrectBoole quickSort := by
  gen_smt_vcs_boole
  all_goals smt
-/
