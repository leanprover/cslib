import StrataBoole.MetaVerifier
import Smt

open Strata

-- Mutual recursion over a Peano-style datatype: `even` calls `odd` and vice
-- versa, both terminating by structural recursion on the `@[cases] MyNat`
-- parameter.
private def mutualRecursionSeed : StrataDDM.Program :=
#strata
program Boole;

datatype MyNat () { Zero(), Succ(pred: MyNat) };

rec
function even(@[cases] n : MyNat) : bool
{
  if MyNat..isZero(n) then true else odd(MyNat..pred(n))
}
function odd(@[cases] n : MyNat) : bool
{
  if MyNat..isZero(n) then false else even(MyNat..pred(n))
}
;

procedure test_parity() returns ()
spec {
  ensures even(Zero()) == true;
  ensures odd(Zero()) == false;
  ensures even(Succ(Zero())) == false;
  ensures odd(Succ(Zero())) == true;
}
{
  assert even(Zero()) == true;
  assert odd(Zero()) == false;
  assert even(Succ(Zero())) == false;
  assert odd(Succ(Zero())) == true;
};
#end

/-- info:
Obligation: even_body_calls_MyNat..pred_0
Property: assert
Result: ✅ pass

Obligation: odd_body_calls_MyNat..pred_0
Property: assert
Result: ✅ pass

Obligation: even_terminates_0
Property: assert
Result: ✅ pass

Obligation: odd_terminates_0
Property: assert
Result: ✅ pass

Obligation: assert_4_752
Property: assert
Result: ✅ pass

Obligation: assert_5_783
Property: assert
Result: ✅ pass

Obligation: assert_6_814
Property: assert
Result: ✅ pass

Obligation: assert_7_852
Property: assert
Result: ✅ pass

Obligation: test_parity_ensures_0_608
Property: assert
Result: ✅ pass

Obligation: test_parity_ensures_1_640
Property: assert
Result: ✅ pass

Obligation: test_parity_ensures_2_672
Property: assert
Result: ✅ pass

Obligation: test_parity_ensures_3_711
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" mutualRecursionSeed (options := .quiet)

theorem mutualRecursionSeed_smtVCsCorrect : Strata.smtVCsCorrectBoole mutualRecursionSeed := by
  gen_smt_vcs_boole
  all_goals (first | smt +mono | smt | omega | trivial | grind)

-- Mutual recursion over int: `decreases n` on each function in the `rec`
-- block, with the termination VCs discharged by cvc5. `even`/`odd` are
-- emitted as uninterpreted functions in the SMT query, so the solver knows
-- they terminate but not their defining equations (no opaque/reveal support
-- yet to expose those to the solver).
private def mutualRecursionIntSeed : StrataDDM.Program :=
#strata
program Boole;

rec
function even(n: int) : bool
  decreases n
{
  if n <= 0 then true else odd(n - 1)
}
function odd(n: int) : bool
  decreases n
{
  if n <= 0 then false else even(n - 1)
}
;
#end

/-- info:
Obligation: even_terminates_0
Property: assert
Result: ✅ pass

Obligation: even_terminates_1
Property: assert
Result: ✅ pass

Obligation: odd_terminates_0
Property: assert
Result: ✅ pass

Obligation: odd_terminates_1
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" mutualRecursionIntSeed (options := .quiet)

theorem mutualRecursionIntSeed_smtVCsCorrect : Strata.smtVCsCorrectBoole mutualRecursionIntSeed := by
  gen_smt_vcs_boole
  all_goals (first | smt +mono | smt | omega | trivial | grind)
