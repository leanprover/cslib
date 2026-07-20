import StrataBoole.MetaVerifier
import Smt

open Strata

/-
Tests all three SMT-LIB 2.7 cast directions:
  1. `as_uint(e)`  — unsigned bv → Int  (ubv_to_int)
  2. `as_sint(e)`  — signed bv → Int    (sbv_to_int)
  3. `as_bv{n}(e)` — Int → bv           ((_ int_to_bv n))
-/

private def castAllDirectionsSeed : StrataDDM.Program :=
#strata
program Boole;

// (1) ubv_to_int: unsigned interpretation, always in [0, 255]
procedure test_ubv_to_int(x: bv8) returns ()
spec {
  ensures as_uint(x) >= 0;
  ensures as_uint(x) <= 255;
} {
  exit test_ubv_to_int;
};

// (2) sbv_to_int: signed interpretation, range [-128, 127]
procedure test_sbv_to_int(x: bv8) returns ()
spec {
  ensures as_sint(x) >= -128;
  ensures as_sint(x) <= 127;
} {
  exit test_sbv_to_int;
};

// (3) int_to_bv: truncating cast, as_uint(result) == n for n in [0, 255]
procedure test_int_to_bv(n: int) returns (result: bv8)
spec {
  requires 0 <= n && n < 256;
  ensures as_uint(result) == n;
} {
  result := as_bv8(n);
  exit test_int_to_bv;
};

// Round-trip: as_uint(as_bv8(n)) == n for n in [0, 255]
procedure test_roundtrip(n: int) returns ()
spec {
  requires 0 <= n && n < 256;
  ensures as_uint(as_bv8(n)) == n;
} {
  exit test_roundtrip;
};

// Signed and unsigned agree when value is non-negative
procedure test_sign_agreement(x: bv8) returns ()
spec {
  requires as_sint(x) >= 0;
  ensures as_uint(x) == as_sint(x);
} {
  exit test_sign_agreement;
};
#end

/-- info:
Obligation: test_ubv_to_int_ensures_0_483
Property: assert
Result: ✅ pass

Obligation: test_ubv_to_int_ensures_1_510
Property: assert
Result: ✅ pass

Obligation: test_sbv_to_int_ensures_2_683
Property: assert
Result: ✅ pass

Obligation: test_sbv_to_int_ensures_3_713
Property: assert
Result: ✅ pass

Obligation: test_int_to_bv_ensures_5_940
Property: assert
Result: ✅ pass

Obligation: test_roundtrip_ensures_7_1164
Property: assert
Result: ✅ pass

Obligation: test_sign_agreement_ensures_9_1370
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" castAllDirectionsSeed (options := .quiet)

set_option maxRecDepth 4000 in
theorem castAllDirectionsSeed_smtVCsCorrect : Strata.smtVCsCorrectBoole castAllDirectionsSeed := by
  gen_smt_vcs_boole
  all_goals (first | smt +mono | smt | omega | (intro x; simp only [Int.ofNat_eq_natCast, BitVec.toNat_ofInt, BitVec.toInt_eq_toNat_cond] at *; have := x.isLt; omega) | (intro n hn; simp only [Int.ofNat_eq_natCast, BitVec.toNat_ofInt] at *; rw [Int.toNat_of_nonneg (by omega)]; omega) | (intro x hx; simp only [Int.ofNat_eq_natCast, BitVec.toInt_eq_toNat_cond] at *; have := x.isLt; omega) | grind)
