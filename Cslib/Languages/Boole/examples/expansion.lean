import StrataBoole.MetaVerifier
import Smt

namespace Strata

/-
Verification example for `function ... { body }` definitions (verified by
unfolding, i.e. "expansion") coexisting with independent quantified axioms
about the same function: `is_positive`'s body proves `is_positive(12)`
directly, while `increment` additionally has an axiom relating its result to
its boolean flag argument.
-/

private def expansion :=
#strata
program Boole;

function is_positive(x:int) : bool
{
  x > 0
}

function increment(x:int, flag:bool) : int
{
  x + 1
}

axiom (∀ z:int . z > 12 ==> is_positive(z));
axiom (∀ y:int, flag:bool . increment(y, flag) > 1 ==> y > 0);

procedure test_expansion() returns ()
{
  assert is_positive(12);
  assert increment(3, true) == 4;
};

#end

/-- info:
Obligation: assert_2_703
Property: assert
Result: ✅ pass

Obligation: assert_3_729
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" expansion (options := .quiet)

theorem expansion_smtVCsCorrect : Strata.smtVCsCorrectBoole expansion := by
  gen_smt_vcs_boole
  all_goals (first | smt +mono | (intros; decide))
