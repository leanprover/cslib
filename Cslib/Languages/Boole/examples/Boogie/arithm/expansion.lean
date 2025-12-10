import Strata.MetaVerifier

namespace Strata

private def expansion :=
#strata
program Boogie;

function xxgz(x:int) : bool
{
  x > 0
}

function xxf1(x:int, y:bool) : int
{
  x + 1
}

axiom (forall z:int :: z > 12 ==> xxgz(z));
axiom (forall y:int, x:bool :: xxf1(y, x) > 1 ==> y > 0);

procedure foo() returns ()
{
  assert xxgz(12);
  assert xxf1(3,true) == 4;
};

#end

#eval Strata.Boole.verify "cvc5" expansion

example : Strata.smtVCsCorrect expansion := by
  gen_smt_vcs
  all_goals grind

end Strata
