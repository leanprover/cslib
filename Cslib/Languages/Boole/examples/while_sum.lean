import StrataBoole.MetaVerifier
import Smt

open Strata

/-
Verification example for `while` loops (contrast with `loop_simple.lean`'s
`for ... to ... by` loop over the same triangular-number sum): the
postcondition is established via body-level named `assert`s after the loop
rather than a spec-level `ensures` clause.
-/

def whileSumSeed : StrataDDM.Program :=
#strata
program Boole;

procedure while_sum (n: int) returns (r: int)
spec {
  requires (n >= 0);
}
{
  var sum : int;
  var i : int;

  sum := 0;
  i := 0;
  while(i < n)
    invariant (i <= n && ((i * (i-1)) div 2 == sum))
  {
    sum := sum + i;
    i := i + 1;
  }
  assert [sum_assert]: ((n * (n-1)) div 2 == sum);
  assert [neg_cond]: (i == n);
  r := sum;
};
#end

/-- info:
Obligation: entry_invariant_0_0
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_0_0
Property: assert
Result: ✅ pass

Obligation: sum_assert
Property: assert
Result: ✅ pass

Obligation: neg_cond
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" whileSumSeed (options := .quiet)

open Strata.SMT

theorem whileSumSeed_smtVCsCorrect : smtVCsCorrectBoole whileSumSeed := by
  gen_smt_vcs_boole
  all_goals
    (intros
     first
     | smt +mono
     | smt
     | omega
     | trivial
     | (have hstep : ∀ x : Int, (x + 1) * (x + 1 - 1) = x * (x - 1) + 2 * x := fun x => by
          have e1 : x + 1 - 1 = x := by omega
          rw [e1, Int.add_mul, Int.one_mul, Int.mul_sub, Int.mul_one]
          omega
        simp only [hstep] at *
        omega)
     | grind)
