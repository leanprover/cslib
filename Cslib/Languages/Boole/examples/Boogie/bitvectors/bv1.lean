import Strata.MetaVerifier

namespace Strata

private def bitVec :=
#strata
program Boogie;
type StrataHeap;
type StrataRef;
type StrataField (t: Type);

// Variables
var x : bv32;

// Uninterpreted procedures
// Implementations
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

#eval Strata.Boole.verify "cvc5" bitVec

example : Strata.smtVCsCorrect bitVec := by
  gen_smt_vcs
  all_goals grind

end Strata
