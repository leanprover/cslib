import StrataBoole.MetaVerifier
import Smt

open Strata

/-
Verification example for `for ... to ... by` loop syntax (contrast with `while_sum.lean`'s
`while` loop over the same triangular-number sum): the postcondition is established via a
spec-level named `ensures` clause rather than body-level `assert`s.
-/

def loop_simple_program : StrataDDM.Program :=
#strata
program Boole;

procedure loop_simple (n: int) returns (r: int)
spec {
  requires [non_negative]: (n >= 0);
  ensures [sum_assert]: ((n * (n-1)) div 2 == r);
}
{
  var sum : int := 0;
  for i : int := 0 to (n - 1) by 1
    invariant i <= n
    invariant (i * (i-1)) div 2 == sum
  {
    sum := sum + i;
  }
  r := sum;
};
#end

/-- info:
Obligation: entry_invariant_0_0
Property: assert
Result: ✅ pass

Obligation: entry_invariant_0_1
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_0_0
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_0_1
Property: assert
Result: ✅ pass

Obligation: sum_assert
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" loop_simple_program (options := .quiet)

open Strata.SMT

-- `(i*(i-1))/2 == sum` is a nonlinear invariant (product of two variables) combined with
-- integer division, which `smt`/`omega`/`grind` can't discharge alone; maintaining it across
-- one loop step needs the algebraic identity `(x+1)*x == x*(x-1) + 2*x`, and the postcondition
-- additionally needs a boundary case (`x <= 0 ==> x*(x-1) == 0`) split out from the `for` loop's
-- `if n-1 >= 0` guard.
theorem loop_simple_smtVCsCorrect : smtVCsCorrectBoole loop_simple_program := by
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
     | (split
        · rename_i h
          simp only [if_pos h] at *
          grind
        · rename_i h
          simp only [if_neg h] at *
          have hzero : ∀ x : Int, 0 ≤ x → x ≤ 0 → x * (x - 1) = 0 := fun x h1 h2 => by
            have hx0 : x = 0 := by omega
            rw [hx0]; decide
          simp (discharger := omega) only [hzero]
          omega))
