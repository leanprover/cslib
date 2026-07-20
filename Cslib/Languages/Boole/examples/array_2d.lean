import StrataBoole.MetaVerifier
import Smt

open Strata

/-
Verification example for 2-dimensional map indexing: `grid[i][j] := v`
lowers to nested map `select`/`update` (a `Map int (Map int int)`).
-/

private def array_2d :=
#strata
program Boole;

procedure array_2d_write_read(i: int, j: int, v: int) returns ()
{
  var grid : Map int (Map int int);
  grid[i][j] := v;
  assert v == v;
};

#end

/-- info:
Obligation: assert_0_375
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" array_2d (options := .quiet)

theorem array_2d_smtVCsCorrect : Strata.smtVCsCorrectBoole array_2d := by
  gen_smt_vcs_boole
  all_goals (try smt +mono)
