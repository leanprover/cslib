import Strata.MetaVerifier

------------------------------------------------------------
namespace Strata

-- Prefix sums.
--
-- Intended spec: `S[i] = Σ_{k<i} A[k]`. In Boole, we encode the summation via an
-- uninterpreted function with recursive axioms.
private def prefixSumsPgm : Strata.Program :=
#strata
program Boole;

// Sum of the first `i` elements: `PrefixSum(A, i) = Σ_{k<i} A[k]`.
function PrefixSum(A : Map int int, i : int) : int;

axiom (forall A : Map int int :: PrefixSum(A, 0) == 0);
axiom (forall A : Map int int, i : int ::
  i > 0 ==> PrefixSum(A, i) == PrefixSum(A, i - 1) + A[i - 1]);

procedure PrefixSums(A : Map int int, n : int) returns (S : Map int int)
spec
{
  requires n >= 0;
  ensures forall i : int :: 0 <= i && i <= n ==> S[i] == PrefixSum(A, i);
}
{
  var i : int;

  // Initialize S[0] = 0.
  S := S[0 := 0];

  i := 0;
  while (i < n)
    invariant 0 <= i && i <= n
    invariant forall k : int :: 0 <= k && k <= i ==> S[k] == PrefixSum(A, k)
  {
    // Step: S[i+1] = S[i] + A[i].
    S := S[i + 1 := S[i] + A[i]];
    i := i + 1;
  }
};
#end

set_option maxHeartbeats 1000000 in
example : Strata.smtVCsCorrect prefixSumsPgm := by
  gen_smt_vcs
  all_goals grind

end Strata
