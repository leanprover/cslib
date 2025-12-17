import Strata.MetaVerifier

------------------------------------------------------------
namespace Strata

-- CLRS: Horner's rule for polynomial evaluation
-- Exercise 2.3
-- HORNER(A, x)
-- 1  y = 0
-- 2  for i = n downto 0
-- 3      y = A[i] + x * y
-- 4  return y
--
-- Here A[0..n] holds coefficients of
--   P(x) = A[0] + A[1] x + ... + A[n] x^n

private def hornerPgm :=
#strata
program Boole;

// "Array" of ints represented as a map from int to int
type Array := Map int int;

procedure Horner(A : Array, n : int, x : int) returns (y : int)
spec
{
  requires n >= 0;
  // A full spec would say: y = Σ_{k=0}^{n} A[k] * x^k
  // but we leave that as a future extension.
  // [FEATURE REQUEST] Should be able to borrow
  // mathlib's polynomial definitions. Or at least
  // have importable power/summation definitions.
}
{
  var i : int;

  y := 0;
  i := n;

  // for i = n downto 0
  // [FEATURE REQUEST] For loop construct with downto
  while (i >= 0)
    invariant (i >= -1 && i <= n);
  {
    y := A[i] + x * y;
    i := i - 1;
  }
};
#end

#eval verify "cvc5" hornerPgm
