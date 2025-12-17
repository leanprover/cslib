import Strata.MetaVerifier

------------------------------------------------------------
namespace Strata

-- CLRS Chapter 15: Dynamic Programming
-- Rod Cutting (Top-Down with Memoization)
--
-- MEMOIZED-CUT-ROD(p, n)
-- 1  let r[0..n] be a new array
-- 2  for i = 0 to n
-- 3      r[i] = -∞
-- 4  return MEMOIZED-CUT-ROD-AUX(p, n, r)
--
-- MEMOIZED-CUT-ROD-AUX(p, n, r)
-- 1  if r[n] >= 0
-- 2      return r[n]
-- 3  if n == 0
-- 4      q = 0
-- 5  else q = -∞
-- 6      for i = 1 to n
-- 7          q = max(q, p[i] + MEMOIZED-CUT-ROD-AUX(p, n-i, r))
-- 8  r[n] = q
-- 9  return q
--
-- Assumption: prices are nonnegative, so we can use r[k] = -1 as "unknown"
-- (instead of -∞) and initialize q := 0.

private def rodCuttingTopDownPgm :=
#strata
program Boole;

type Array := Map int int;

procedure MemoizedCutRodAux(p : Array, n : int, r : Array) returns (q : int, r' : Array)
spec
{
  requires n >= 0;

  // [FEATURE REQUEST] Array bounds specifications
  requires forall k:int :: 1 <= k && k <= n ==> p[k] >= 0;

  // Memo convention: r[t] == -1 means "unknown", otherwise r[t] >= 0
  requires forall t:int :: 0 <= t && t <= n ==> (r[t] == -1 || r[t] >= 0);

  ensures q >= 0;
  ensures forall t:int :: 0 <= t && t <= n ==> (r'[t] == -1 || r'[t] >= 0);

  // [FEATURE REQUEST] Stronger functional correctness:
  // ensures q == optimal revenue for length n
  // ensures r'[n] == q
}
{
  var i : int;
  var cand : int;
  var sub : int;
  var r2 : Array;

  // Default: output memo is input memo (we update as needed)
  r' := r;

  // if r[n] >= 0 return it
  if (r'[n] >= 0) {
    q := r'[n];
  } else {
    if (n == 0) {
      q := 0;
    } else {
      // q = 0 instead of -∞ since prices are nonnegative
      // [FEATURE REQUEST] Support for -∞ / extended integers
      q := 0;

      // for i = 1 to n
      i := 1;
      while (i <= n)
        // invariant (1 <= i && i <= n + 1);
        // invariant (q >= 0);
        // [FEATURE REQUEST] Support for multiple invariants
        invariant (
          forall t:int :: 0 <= t && t <= n ==> (r'[t] == -1 || r'[t] >= 0)
        );
      {
        // recursive call on (n - i)
        // [FEATURE REQUEST] Better support for mutual recursion / termination measures
        sub, r2 := MemoizedCutRodAux(p, n - i, r');

        // carry forward updated memo table from recursion
        r' := r2;

        cand := p[i] + sub;

        // q = max(q, cand)
        // [FEATURE REQUEST] Built-in max operator
        if (cand > q) {
          q := cand;
        };

        i := i + 1;
      }
    };

    // r[n] = q
    r' := r'[n := q];
  }
};

procedure MemoizedCutRod(p : Array, n : int) returns (res : int)
spec
{
  requires n >= 0;

  // [FEATURE REQUEST] Array bounds specifications
  requires forall k:int :: 1 <= k && k <= n ==> p[k] >= 0;

  ensures res >= 0;
}
{
  var r : Array;
  var i : int;
  var q : int;
  var r2 : Array;

  // Initialize memo array: r[0..n] = -1
  // [FEATURE REQUEST] Array allocation / initialization sugar
  i := 0;
  while (i <= n)
    // invariant (0 <= i && i <= n + 1);
    // [FEATURE REQUEST] Support for multiple invariants
    invariant (
      forall t:int :: 0 <= t && t < i ==> r[t] == -1
    );
  {
    r := r[i := -1];
    i := i + 1;
  }

  q, r2 := MemoizedCutRodAux(p, n, r);
  res := q;
};

#end

#eval verify "cvc5" rodCuttingTopDownPgm
