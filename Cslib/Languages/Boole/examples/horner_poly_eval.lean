import Strata.MetaVerifier
import Smt

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
  y := 0;

  for i:int := n downto 0
  {
    y := A[i] + x * y;
  }
};
#end

#eval Strata.Boole.verify "cvc5" hornerPgm

example : Strata.smtVCsCorrect hornerPgm := by
  gen_smt_vcs
  all_goals smt +mono
