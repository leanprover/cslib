import StrataBoole.MetaVerifier
import Smt

open Strata

/-
Verification example for Horner's rule (polynomial evaluation), type-checking
the loop structure without a full polynomial-correctness postcondition.
-/

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
  // A full spec would say: y = Σ_{k=0}^{n} A[k] * x^k,
  // but we leave that as a future extension.
  // TODO(feature:math-imports): borrow polynomial/power/summation definitions
  // from a reusable library layer instead of restating them ad hoc.
}
{
  y := 0;

  for i:int := n downto 0
  {
    y := A[i] + x * y;
  }
};
#end

/-- info:
-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" hornerPgm (options := .quiet)

theorem hornerPgm_smtVCsCorrect : Strata.smtVCsCorrectBoole hornerPgm := by
  gen_smt_vcs_boole
  all_goals (try smt +mono)
