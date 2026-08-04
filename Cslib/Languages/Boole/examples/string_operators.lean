import StrataBoole.MetaVerifier
import Smt

namespace Strata

/-
Verification example covering the string theory surface of Boole: length, concatenation,
substring extraction, indexing, containment, prefix/suffix relations, replacement, and
integer/string conversion. Demonstrates the axiomatization style used for `string` operations
throughout this example suite.
-/

private def basicOp :=
#strata
program Boole;

function strConcat(x: string, y: string): string;
function len(x: string): int;
function substr(x: string, y: int, z: int): string;
function indexOf(x: string, y: string): int;
function indexOfFromOffset(x: string, y: string, z: int): int;
function at(x: string, y: int): string;
function contains(x: string, y: string): bool;
function prefixOf(x: string, y: string): bool;
function suffixOf(x: string, y: string): bool;
function replace(x: string, y: string, z: string): string;
function stringToInt(x: string): int;
function intToString(x: int): string;

// axioms for basic string behavior

// length of concatenation = sum of lengths
axiom (∀ x: string, y: string . len(strConcat(x, y)) == len(x) + len(y));

// each character (returned by at) has length 1
axiom (∀ x: string, i: int .
    0 <= i && i < len(x) ==> len(at(x, i)) == 1);

// every string has non-negative length
axiom (∀ x: string . len(x) >= 0);

// prefix and suffix relationships
axiom (∀ x: string, y: string .
    prefixOf(x, strConcat(x, y)));       // x is prefix of x+y
axiom (∀ x: string, y: string .
    suffixOf(y, strConcat(x, y)));       // y is suffix of x+y

// contains relationships
axiom (∀ x: string, y: string .
    contains(strConcat(x, y), x));       // x+y contains x
axiom (∀ x: string, y: string .
    contains(strConcat(x, y), y));       // x+y contains y

// index of a prefix is 0
axiom (∀ x: string, y: string .
    indexOf(strConcat(x, y), x) == 0);
axiom (∀ x: string, y: string .
    indexOfFromOffset(strConcat(x, y), x, 0) == 0);

// substring extraction behaves as expected
axiom (∀ x: string, y: string .
    substr(strConcat(x, y), 0, len(x)) == x);
axiom (∀ x: string, y: string .
    substr(strConcat(x, y), len(x), len(y)) == y);

// replacement axiom: replacing prefix x with y in x+y yields y+y
axiom (∀ x: string, y: string .
    replace(strConcat(x, y), x, y) == strConcat(y, y));

// integer/string conversion inverses
axiom (∀ i: int . stringToInt(intToString(i)) == i);
axiom (∀ x: string . intToString(stringToInt(x)) == x);

// characters come from x when i < len(x)
axiom (∀ x: string, y: string, i: int .
    0 <= i && i < len(x) ==> at(strConcat(x, y), i) == at(x, i));

// characters come from y when i >= len(x)
axiom (∀ x: string, y: string, i: int .
    len(x) <= i && i < len(x) + len(y) ==>
        at(strConcat(x, y), i) == at(y, i - len(x)));


procedure main() returns () {
    var s1: string, s2: string, s3: string;

    assume len(s1) == 3;
    assume len(s3) == 3;
    assume strConcat(s1,s2) == s3;

    assert len(s1) + len(s2) == len(s3);

    assert substr(s3, len(s1), len(s2)) == s2;

    assert indexOf(s3, s1) == 0;

    assert indexOfFromOffset(s3, s1, 0) == 0;

    assert at(s3, 2) == at(s1, 2);

    assert contains(s3, s1);

    assert prefixOf(s1, s3);

    assert suffixOf(s2, s3);

    assert replace(s3, s1, s2) == strConcat(s2, s2);

    assert intToString(stringToInt(s1)) == s1;
};

#end

/-- info:
Obligation: assert_19_3004
Property: assert
Result: ✅ pass

Obligation: assert_20_3046
Property: assert
Result: ✅ pass

Obligation: assert_21_3094
Property: assert
Result: ✅ pass

Obligation: assert_22_3128
Property: assert
Result: ✅ pass

Obligation: assert_23_3175
Property: assert
Result: ✅ pass

Obligation: assert_24_3211
Property: assert
Result: ✅ pass

Obligation: assert_25_3241
Property: assert
Result: ✅ pass

Obligation: assert_26_3271
Property: assert
Result: ✅ pass

Obligation: assert_27_3301
Property: assert
Result: ✅ pass

Obligation: assert_28_3355
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" basicOp (options := .quiet)

theorem basicOp_smtVCsCorrect : Strata.smtVCsCorrectBoole basicOp := by
  gen_smt_vcs_boole
  all_goals (intros; first | smt +mono | smt | omega | trivial | grind)
