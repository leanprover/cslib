import StrataBoole.MetaVerifier
import Smt

/-
Verification example for explicit labeled statement blocks (`label: { ... }`)
and vacuous-truth reasoning: after `x := bv{32}(0)`, assuming the
contradictory `x == bv{32}(1)` makes every subsequent assertion in the same
block trivially provable, including `assert false`.
-/

private def labeledBlockSeed :=
#strata
program Boole;

var x : bv32;

procedure main() returns ()
spec {
  modifies x;
}
{
  anon0: {
    x := bv{32}(0);
    assume (x == bv{32}(1));
    assert false;
  }
  end : {}
};

#end

/-- info:
Obligation: assert_1_511
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" labeledBlockSeed (options := .quiet)

theorem labeledBlockSeed_smtVCsCorrect : Strata.smtVCsCorrectBoole labeledBlockSeed := by
  gen_smt_vcs_boole
  all_goals (try smt +mono)
