import StrataBoole.MetaVerifier
import Smt

open Strata

/-
Verification examples modeling the relational loop-invariant pattern used by
Montgomery-ladder-style scalar multiplication (Algorithm 8 of Costello-Smith
2017), which maintains two co-evolving values `x0`/`x1` across loop
iterations with an invariant relating them. The examples below model this
pattern with linear arithmetic in place of the full elliptic-curve group law.
-/

-- Baseline: single-variable for-loop invariant — works in Boole.
private def simpleInvariantSeed : StrataDDM.Program :=
#strata
program Boole;

procedure sum_to_n(n: int) returns (r: int)
spec {
  requires n >= 0;
  ensures r == (n * (n - 1)) div 2;
}
{
  var sum : int := 0;
  for i : int := 0 to (n - 1) by 1
    invariant i <= n
    invariant (i * (i - 1)) div 2 == sum
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

Obligation: sum_to_n_ensures_1_657
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" simpleInvariantSeed (options := .quiet)

theorem simpleInvariantSeed_smtVCsCorrect : Strata.smtVCsCorrectBoole simpleInvariantSeed := by
  gen_smt_vcs_boole
  all_goals
    (intros
     first
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

-- Relational while-loop invariant.
-- Models the structural pattern of the Montgomery ladder using linear arithmetic:
-- x0 tracks i * step, x1 tracks (i + 1) * step.
-- The relational invariant `x1 == x0 + step` mirrors the elliptic-curve identity
-- [q+1]P = [q]P + P (i.e. x1 - x0 = P = base in the scalar-multiplication loop).
private def relationalInvariantSeed : StrataDDM.Program :=
#strata
program Boole;

procedure linear_ladder(step: int, n: int) returns (r: int)
spec {
  requires n >= 0;
  ensures r == n * step;
}
{
  var x0 : int := 0;
  var x1 : int := step;
  var i  : int := 0;
  while (i < n)
    invariant i <= n
    invariant x1 == x0 + step
    invariant x0 == i * step
  {
    x0 := x1;
    x1 := x1 + step;
    i  := i + 1;
  }
  r := x0;
};
#end

/-- info:
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

Obligation: linear_ladder_ensures_1_2316
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" relationalInvariantSeed (options := .quiet)

theorem relationalInvariantSeed_smtVCsCorrect : Strata.smtVCsCorrectBoole relationalInvariantSeed := by
  gen_smt_vcs_boole
  all_goals (try smt +mono)
