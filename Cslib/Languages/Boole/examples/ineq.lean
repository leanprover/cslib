import StrataBoole.MetaVerifier
import Smt

namespace Strata

/-
Verification example for loop-bound inequalities: a fixed literal bound
(`SimpleLoop`) versus a parameterized bound (`VariableBoundLoop`). Both
establish the loop's negated guard as a post-loop fact via `assume`.
-/

private def ineq :=
#strata
program Boole;

procedure SimpleLoop () returns ()
{
  var i: int;

  i := 0;

  while (i < 10)
    invariant 0 <= i
    invariant i <= 10
  {
    i := i + 1;
  }
  // when loop exits, !(i < 10) holds
  assume !(i < 10);
};

procedure VariableBoundLoop (n : int) returns ()
spec {
  requires 0 <= n;
}
{
  var i: int;

  i := 0;

  while (i < n)
    invariant 0 <= i
    invariant i <= n
  {
    i := i + 1;
  }
  // when loop exits, !(i < n) holds
  assume !(i < n);
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
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" ineq (options := .quiet)

theorem ineq_smtVCsCorrect : Strata.smtVCsCorrectBoole ineq := by
  gen_smt_vcs_boole
  all_goals (try smt +mono)
