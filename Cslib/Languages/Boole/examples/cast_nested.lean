import StrataBoole.MetaVerifier
import Smt

open Strata

/-
Verification example exercising `as_uint(e)` in contexts beyond the flat
`as_uint(x)` covered by `cast_expr.lean`:

- Cast inside a ∀-quantifier body over a sequence
- Cast of a compound BV expression (bitwise &)
- Cast in an arithmetic sum bound
- Cast inside a `let_in_expr` binding
- Cast inside a ∃-quantifier body
- Cast inside a `rec function` body with `decreases`, plus axiom-backed
  properties (single-byte decode and empty-sequence base case)
-/

private def castNestedSeed : StrataDDM.Program :=
#strata
program Boole;

procedure cast_in_forall(s: Sequence bv8, n: int) returns ()
spec {
  requires 0 <= n && n <= Sequence.length(s);
  ensures ∀ i: int . 0 <= i && i < n ==> as_uint(Sequence.select(s, i)) < 256;
}
{
  assert ∀ i: int . 0 <= i && i < n ==> as_uint(Sequence.select(s, i)) < 256;
};

procedure cast_compound_bv(a: bv8, b: bv8) returns ()
spec {
  ensures 0 <= as_uint(a & b);
  ensures as_uint(a & b) < 256;
}
{
  assert 0 <= as_uint(a & b);
  assert as_uint(a & b) < 256;
};

procedure cast_sum_bound(a: bv8, b: bv8) returns ()
spec {
  ensures as_uint(a) + as_uint(b) < 512;
}
{
  assert as_uint(a) + as_uint(b) < 512;
};

procedure cast_in_let(x: bv8) returns ()
spec {
  ensures let n : int := as_uint(x) in n >= 0 && n < 256;
}
{
  assert let n : int := as_uint(x) in n >= 0 && n < 256;
};

procedure cast_in_exists(x: bv64) returns ()
spec {
  ensures ∃ n: int . n == as_uint(x) && n >= 0;
}
{
  assert ∃ n: int . n == as_uint(x) && n >= 0;
};

rec function bytes_to_nat(s: Sequence bv8) : int
  decreases Sequence.length(s)
{
  if Sequence.length(s) == 0 then 0
  else as_uint(Sequence.select(s, 0)) + 256 * bytes_to_nat(Sequence.skip(s, 1))
}
;

axiom bytes_to_nat(Sequence.empty_bv8) == 0;
axiom (∀ h: bv8 . ∀ t: Sequence bv8 .
  bytes_to_nat(Sequence.build(t, h)) == as_uint(h) + 256 * bytes_to_nat(t));

procedure test_rec_empty() returns ()
spec {
  ensures bytes_to_nat(Sequence.empty_bv8) == 0;
} { exit test_rec_empty; };

procedure test_rec_single_byte(x: bv8) returns ()
spec {
  ensures bytes_to_nat(Sequence.build(Sequence.empty_bv8, x)) == as_uint(x);
} { exit test_rec_single_byte; };

// Cast inside a `decreases` clause.
// `decreases as_uint(n)` uses a cast expression as the termination measure.
rec function countdown_bv(n: bv8) : int
  decreases as_uint(n)
{
  if n == bv{8}(0) then 0
  else 1 + countdown_bv(n - bv{8}(1))
}
;

// Cast in a function precondition.
function decode_low_byte(b: bv8) : int
  requires as_uint(b) < 128;
{
  as_uint(b)
}

procedure call_decode_byte(x: bv8) returns (r: int)
spec {
  requires as_uint(x) < 128;
  ensures r == as_uint(x);
}
{
  r := decode_low_byte(x);
};
#end

/-- info:
Obligation: cast_in_forall_post_cast_in_forall_ensures_1_712_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: assert_assert_2_798_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: assert_2_798
Property: assert
Result: ✅ pass

Obligation: cast_in_forall_ensures_1_712
Property: assert
Result: ✅ pass

Obligation: assert_5_1011
Property: assert
Result: ✅ pass

Obligation: assert_6_1041
Property: assert
Result: ✅ pass

Obligation: cast_compound_bv_ensures_3_944
Property: assert
Result: ✅ pass

Obligation: cast_compound_bv_ensures_4_975
Property: assert
Result: ✅ pass

Obligation: assert_8_1180
Property: assert
Result: ✅ pass

Obligation: cast_sum_bound_ensures_7_1135
Property: assert
Result: ✅ pass

Obligation: assert_10_1334
Property: assert
Result: ✅ pass

Obligation: cast_in_let_ensures_9_1272
Property: assert
Result: ✅ pass

Obligation: assert_12_1502
Property: assert
Result: ✅ pass

Obligation: cast_in_exists_ensures_11_1447
Property: assert
Result: ✅ pass

Obligation: bytes_to_nat_body_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: bytes_to_nat_body_calls_Sequence.drop_1
Property: out-of-bounds access check
Result: ✅ pass

Obligation: bytes_to_nat_terminates_0
Property: assert
Result: ✅ pass

Obligation: bytes_to_nat_terminates_1
Property: assert
Result: ✅ pass

Obligation: test_rec_empty_ensures_15_1971
Property: assert
Result: ✅ pass

Obligation: test_rec_single_byte_ensures_16_2106
Property: assert
Result: ✅ pass

Obligation: countdown_bv_terminates_0
Property: assert
Result: ✅ pass

Obligation: countdown_bv_terminates_1
Property: assert
Result: ✅ pass

Obligation: set_r_calls_decode_low_byte_0
Property: assert
Result: ✅ pass

Obligation: call_decode_byte_ensures_19_2676
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" castNestedSeed (options := .quiet)

set_option maxRecDepth 8000 in
theorem castNestedSeed_smtVCsCorrect : Strata.smtVCsCorrectBoole castNestedSeed := by
  gen_smt_vcs_boole
  all_goals (try (first | smt +mono | smt | omega))
  all_goals (try (intro a b; simp only [Int.ofNat_eq_natCast] at *; have := (a : BitVec 8).isLt; have := (b : BitVec 8).isLt; omega))
  all_goals (try (try intros; try simp only [Int.ofNat_eq_natCast] at *; first | (have := (‹BitVec _›).isLt) | skip; first | omega | simp_all))
  all_goals (try rfl)
  all_goals grind
