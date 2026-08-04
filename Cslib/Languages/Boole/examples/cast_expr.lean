import StrataBoole.MetaVerifier
import Smt

open Strata

/-
Verification example for the widening cast `as_uint(e)` (any bitvector type
to `int`) across all supported bitvector widths (bv1, bv8, bv16, bv32, bv64,
bv128). Lowers to a native `Bv{n}.ToUInt : bvN → int` Core op; the SMT
encoder maps it to the SMT-LIB 2.7 `ubv_to_int` function. No axioms injected.
-/

private def castExprSeed : StrataDDM.Program :=
#strata
program Boole;

procedure cast_bv8_nonneg(x: bv8) returns ()
spec {
  ensures 0 <= as_uint(x);
}
{
  assert 0 <= as_uint(x);
};

procedure cast_bv64_nonneg(x: bv64) returns ()
spec {
  ensures 0 <= as_uint(x);
}
{
  assert 0 <= as_uint(x);
};

procedure cast_bv32_bounded(x: bv32) returns ()
spec {
  ensures 0 <= as_uint(x) && as_uint(x) < 4294967296;
}
{
  assert 0 <= as_uint(x) && as_uint(x) < 4294967296;
};

procedure cast_bv1_nonneg(x: bv1) returns ()
spec {
  ensures 0 <= as_uint(x);
}
{
  assert 0 <= as_uint(x);
};

procedure cast_bv16_nonneg(x: bv16) returns ()
spec {
  ensures 0 <= as_uint(x);
}
{
  assert 0 <= as_uint(x);
};

procedure cast_bv128_nonneg(x: bv128) returns ()
spec {
  ensures 0 <= as_uint(x);
}
{
  assert 0 <= as_uint(x);
};
#end

/-- info:
Obligation: assert_1_525
Property: assert
Result: ✅ pass

Obligation: cast_bv8_nonneg_ensures_0_494
Property: assert
Result: ✅ pass

Obligation: assert_3_640
Property: assert
Result: ✅ pass

Obligation: cast_bv64_nonneg_ensures_2_609
Property: assert
Result: ✅ pass

Obligation: assert_5_783
Property: assert
Result: ✅ pass

Obligation: cast_bv32_bounded_ensures_4_725
Property: assert
Result: ✅ pass

Obligation: assert_7_923
Property: assert
Result: ✅ pass

Obligation: cast_bv1_nonneg_ensures_6_892
Property: assert
Result: ✅ pass

Obligation: assert_9_1038
Property: assert
Result: ✅ pass

Obligation: cast_bv16_nonneg_ensures_8_1007
Property: assert
Result: ✅ pass

Obligation: assert_11_1155
Property: assert
Result: ✅ pass

Obligation: cast_bv128_nonneg_ensures_10_1124
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" castExprSeed (options := .quiet)

-- `omega` treats a literal `Int.ofNat n` and its own `↑n` (natCast) atoms as
-- unrelated unless `Int.ofNat_eq_natCast` normalizes them first; `as_uint(x) < 2^w`
-- also needs the bitvector's width bound `x.isLt`, which `omega` doesn't discover
-- on its own.
theorem castExprSeed_smtVCsCorrect : Strata.smtVCsCorrectBoole castExprSeed := by
  gen_smt_vcs_boole
  all_goals (first | smt +mono | smt | omega | (intros; simp only [Int.ofNat_eq_natCast]; have := (‹BitVec _›).isLt; omega) | grind)
