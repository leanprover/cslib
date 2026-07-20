import StrataBoole.MetaVerifier
import Smt

open Strata

/-!
Out-of-bounds checks inside conjunctions are verified using the conjunction
prefix as a hypothesis.

For `0 <= j && j < Sequence.length(nums) && ret == Sequence.select(nums, j)`,
the bounds check on `Sequence.select(nums, j)` is discharged using
`0 <= j && j < Sequence.length(nums)` as an assumption, which is established
by the earlier conjuncts via short-circuit semantics.
-/

private def seqOobConjunctionPgm : StrataDDM.Program :=
#strata
program Boole;

procedure find_first (nums : Sequence bv32) returns (ret : bv32)
spec {
  requires Sequence.length(nums) > 0;
  ensures ∃ j : int :: 0 <= j && j < Sequence.length(nums) && ret == Sequence.select(nums, j);
}
{
  assume false;
  ret := Sequence.select(nums, 0);
  exit find_first;
};

#end

/-- info:
Obligation: find_first_post_find_first_ensures_1_634_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: set_ret_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: find_first_ensures_1_634
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" seqOobConjunctionPgm (options := .quiet)

theorem seqOobConjunctionPgm_smtVCsCorrect : Strata.smtVCsCorrectBoole seqOobConjunctionPgm := by
  gen_smt_vcs_boole
  all_goals (try smt +mono)
