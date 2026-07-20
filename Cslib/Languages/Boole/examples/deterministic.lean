import StrataBoole.MetaVerifier
import Smt

open Strata

/-
Verification example for determinism via a `free ensures` clause: since
`Foo`'s result is unconditionally tied to the uninterpreted function `f`,
calling it twice with equal inputs is proved to yield equal outputs, without
reasoning about `Foo`'s recursive implementation at the call site.
-/

private def deterministic :=
#strata
program Boole;

function f(a:int) : int;

procedure Foo(x:int) returns (r:int)
spec
{
  free ensures r == f(x);
}
{
  if (x > 0) {
    var t: int;
    call t := Foo(x - 1);
    r := t + 1;
  } else {
    r := 0;
  }
};

procedure Check(x1:int, x2:int) returns ()
{
  var r1: int, r2: int;

  call r1 := Foo(x1);
  call r2 := Foo(x2);

  // results equal when inputs equal
  if (x1 == x2) {
    assert r1 == r2;
  }
};

#end

/-- info:
Obligation: assert_1_785
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" deterministic (options := .quiet)

theorem deterministic_smtVCsCorrect : Strata.smtVCsCorrectBoole deterministic := by
  gen_smt_vcs_boole
  all_goals (try smt +mono)
