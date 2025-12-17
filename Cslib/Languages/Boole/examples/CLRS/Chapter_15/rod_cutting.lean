import Strata.MetaVerifier

------------------------------------------------------------
namespace Strata

-- CLRS Chapter 15: Dynamic Programming
-- Rod Cutting
--
-- BOTTOM-UP-CUT-ROD(p, n)
-- 1  let r[0..n] be a new array
-- 2  r[0] = 0
-- 3  for j = 1 to n
-- 4      q = -∞
-- 5      for i = 1 to j
-- 6          q = max(q, p[i] + r[j - i])
-- 7      r[j] = q
-- 8  return r[n]
--
-- Assumption: prices are nonnegative, so q can start at 0.

private def rodCuttingPgm :=
#strata
program Boole;

type Array := Map int int;

procedure BottomUpCutRod(p : Array, n : int) returns (res : int)
spec
{
  requires n >= 0;

  // [FEATURE REQUEST] Support for array bounds specifications
  requires forall k:int ::
    1 <= k && k <= n ==> p[k] >= 0;

  ensures res >= 0;

  // [FEATURE REQUEST] Ability to state functional correctness:
  // ensures res == max over all decompositions of n of sum(p[length_i])
}
{
  var r : Array;
  var j : int;
  var i : int;
  var q : int;
  var cand : int;

  // r[0] = 0
  r := r[0 := 0];

  // for j = 1 to n
  j := 1;
  while (j <= n)
    // invariant (1 <= j && j <= n + 1);
    // invariant (r[0] == 0);
    // [FEATURE REQUEST] Support for multiple invariants
    invariant (
      forall t:int ::
        0 <= t && t < j ==> r[t] >= 0
    );
  {
    // q = 0   (instead of -∞)
    // [FEATURE REQUEST] Support for -∞ / extended integers
    q := 0;

    // for i = 1 to j
    i := 1;
    while (i <= j)
      // invariant (1 <= i && i <= j + 1);
      // invariant (q >= 0);
      // [FEATURE REQUEST] Support for multiple invariants
      invariant (
        forall t:int ::
          0 <= t && t < j ==> r[t] >= 0
      );
    {
      // cand = p[i] + r[j - i]
      cand := p[i] + r[j - i];

      // q = max(q, cand)
      // [FEATURE REQUEST] Built-in max operator
      if (cand > q) {
        q := cand;
      };

      i := i + 1;
    }

    // r[j] = q
    r := r[j := q];

    j := j + 1;
  }

  res := r[n];
};

#end

#eval verify "cvc5" rodCuttingPgm
