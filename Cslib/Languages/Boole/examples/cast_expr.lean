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

procedure cast_bv8_nonneg(x: bv W8) returns ()
spec {
  ensures 0 <= as_uint(x);
}
{
  assert 0 <= as_uint(x);
};

procedure cast_bv64_nonneg(x: bv W64) returns ()
spec {
  ensures 0 <= as_uint(x);
}
{
  assert 0 <= as_uint(x);
};

procedure cast_bv32_bounded(x: bv W32) returns ()
spec {
  ensures 0 <= as_uint(x) && as_uint(x) < 4294967296;
}
{
  assert 0 <= as_uint(x) && as_uint(x) < 4294967296;
};

procedure cast_bv1_nonneg(x: bv W1) returns ()
spec {
  ensures 0 <= as_uint(x);
}
{
  assert 0 <= as_uint(x);
};

procedure cast_bv16_nonneg(x: bv W16) returns ()
spec {
  ensures 0 <= as_uint(x);
}
{
  assert 0 <= as_uint(x);
};

procedure cast_bv128_nonneg(x: bv W128) returns ()
spec {
  ensures 0 <= as_uint(x);
}
{
  assert 0 <= as_uint(x);
};
#end

/-- info:
Obligation: assert_1_527
Property: assert
Result: ✅ pass

Obligation: cast_bv8_nonneg_ensures_0_496
Property: assert
Result: ✅ pass

Obligation: assert_3_644
Property: assert
Result: ✅ pass

Obligation: cast_bv64_nonneg_ensures_2_613
Property: assert
Result: ✅ pass

Obligation: assert_5_789
Property: assert
Result: ✅ pass

Obligation: cast_bv32_bounded_ensures_4_731
Property: assert
Result: ✅ pass

Obligation: assert_7_931
Property: assert
Result: ✅ pass

Obligation: cast_bv1_nonneg_ensures_6_900
Property: assert
Result: ✅ pass

Obligation: assert_9_1048
Property: assert
Result: ✅ pass

Obligation: cast_bv16_nonneg_ensures_8_1017
Property: assert
Result: ✅ pass

Obligation: assert_11_1167
Property: assert
Result: ✅ pass

Obligation: cast_bv128_nonneg_ensures_10_1136
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
