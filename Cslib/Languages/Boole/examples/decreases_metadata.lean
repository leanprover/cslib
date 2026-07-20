import StrataBoole.MetaVerifier
import Smt

open Strata

/-
Verification example for loop-level `decreases` termination metadata in
Boole (function/procedure/spec-function `decreases` is not yet supported).
-/

private def decreasesMetadataSeed : StrataDDM.Program :=
#strata
program Boole;

// Target shape for the remaining gap:
//
// function dec_to_zero(n: int) : int
//   decreases n
// {
//   if n <= 0 then 0 else dec_to_zero(n - 1)
// }
//
// procedure call_dec_to_zero(n: int) returns (r: int)
//   decreases n
// {
//   r := dec_to_zero(n);
// }

procedure loop_measure_seed(n: int) returns (i: int)
spec {
  requires 0 <= n;
  ensures i == n;
}
{
  i := 0;
  while (i < n)
    decreases n - i
    invariant 0 <= i
    invariant i <= n
  {
    i := i + 1;
  }
};
#end

/-- info:
Obligation: entry_invariant_0_0
Property: assert
Result: ✅ pass

Obligation: entry_invariant_0_1
Property: assert
Result: ✅ pass

Obligation: measure_lb_0
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_0_0
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_0_1
Property: assert
Result: ✅ pass

Obligation: measure_decrease_0
Property: assert
Result: ✅ pass

Obligation: loop_measure_seed_ensures_1_638
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" decreasesMetadataSeed (options:=.quiet)

theorem decreasesMetadataSeed_smtVCsCorrect : Strata.smtVCsCorrectBoole decreasesMetadataSeed := by
  gen_smt_vcs_boole
  all_goals (try smt +mono)
