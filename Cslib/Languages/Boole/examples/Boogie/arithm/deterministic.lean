import Strata.MetaVerifier
namespace Strata

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

#eval Strata.Boole.verify "cvc5" deterministic

example : Strata.smtVCsCorrect deterministic := by
  gen_smt_vcs
  all_goals grind

end Strata
