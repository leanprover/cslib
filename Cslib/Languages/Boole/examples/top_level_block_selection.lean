import StrataBoole.MetaVerifier
import Smt

open Strata

/-
Verification example for top-level anonymous `{ ... }` blocks (verified as
an implicit procedure named `Strata.Boole.topLevelBlockProcedureName`) and
selective verification via `proceduresToVerify`, which here targets only the
top-level block, skipping the unrelated named procedure `helper`.
-/

def topLevelBlockSelection : StrataDDM.Program :=
#strata
program Boole;

{
  assert [top_assert]: true;
};

procedure helper() returns (x: int)
spec {
  ensures [helper_ensures]: x == 1;
}
{
  x := 1;
};
#end

/-- info:
Obligation: top_assert
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" topLevelBlockSelection
        (proceduresToVerify := (some [Strata.Boole.topLevelBlockProcedureName]))
        (options := .quiet)

theorem topLevelBlockSelection_smtVCsCorrect : Strata.smtVCsCorrectBoole topLevelBlockSelection := by
  gen_smt_vcs_boole
  all_goals (try smt +mono)
