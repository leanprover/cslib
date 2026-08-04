import StrataBoole.MetaVerifier
import Smt

open Strata

/-!
Verification examples covering the Boole grammar extensions introduced in `Boole.Grammar`:
- `for ... to`
- `for ... downto`
- `for ... by`
- multiple loop invariants
- array update / nested map syntax
- quantifiers inside invariants
-/

private def grammarExtensions : StrataDDM.Program :=
#strata
program Boole;

procedure test_for_to () returns ()
{
  for i : int := 0 to 10
    invariant 0 <= i
  {
    assert 0 <= i;
  }
};

procedure test_for_downto () returns ()
{
  for k : int := 20 downto 0
      invariant k >= -1
  {
      assert k >= 0;
  }
};

procedure test_for_downto_by () returns ()
{
  for k : int := 20 downto 0 by 2
      invariant k mod 2 == 0
      invariant k >= -2
  {
      assert k mod 2 == 0;
      assert k >= 0;
  }
};

procedure test_multiple_invariants () returns ()
{
  for j : int := 0 to 9
    invariant 0 <= j
    invariant j <= 10
    invariant j == 0 || j > 0
  {
    assert j <= 9;
  }
};

procedure test_arrays () returns ()
{
  var arr : Map int int;
  var idx : int;
  var sum : int;

  arr[0] := 5;
  arr[1] := 10;
  arr[2] := 15;

  sum := arr[0] + arr[1] + arr[2];

  idx := 0;
  for i : int := 0 to 9
    invariant 0 <= i && i <= 10
    invariant (∀ k : int . 0 <= k && k < i ==> arr[k] >= 0)
  {
    arr[i] := i * 2;
  }
};

#end

/-- info:
Obligation: entry_invariant_0_0
Property: assert
Result: ✅ pass

Obligation: assert_0_468
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_0_0
Property: assert
Result: ✅ pass

Obligation: entry_invariant_0_0
Property: assert
Result: ✅ pass

Obligation: assert_2_596
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_0_0
Property: assert
Result: ✅ pass

Obligation: entry_invariant_0_0
Property: assert
Result: ✅ pass

Obligation: entry_invariant_0_1
Property: assert
Result: ✅ pass

Obligation: assert_4_761
Property: assert
Result: ✅ pass

Obligation: assert_5_788
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_0_0
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_0_1
Property: assert
Result: ✅ pass

Obligation: entry_invariant_0_0
Property: assert
Result: ✅ pass

Obligation: entry_invariant_0_1
Property: assert
Result: ✅ pass

Obligation: entry_invariant_0_2
Property: assert
Result: ✅ pass

Obligation: assert_7_967
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_0_0
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_0_1
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_0_2
Property: assert
Result: ✅ pass

Obligation: entry_invariant_0_0
Property: assert
Result: ✅ pass

Obligation: entry_invariant_0_1
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_0_0
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_0_1
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" grammarExtensions (options := .quiet)

theorem grammarExtensions_smtVCsCorrect : Strata.smtVCsCorrectBoole grammarExtensions := by
  gen_smt_vcs_boole
  all_goals (first | smt +mono | omega | grind)
