import StrataBoole.MetaVerifier
import Smt

open Strata

/-
Verification example for bitwise operators (`&`, `|`, `^`, `>>`, `ashr`, `<<`,
`~`) on `bvN` types, lowering to the corresponding `Bv{N}.And`/`Or`/`Xor`/
`UShr`/`SShr`/`Shl`/`Not` Core operations (`>>` is unsigned, `ashr` is signed).
-/

-- Exercises & and | (X25519 scalar clamping).
private def bitvectorOpsSeed : StrataDDM.Program :=
#strata
program Boole;

procedure clamp_seed(b0: bv W8, b31: bv W8) returns (r0: bv W8, r31: bv W8)
spec {
  ensures r0  == b0  & bv{8}(0b11111000);
  ensures r31 == (b31 & bv{8}(0b01111111)) | bv{8}(0b01000000);
  ensures r0  & bv{8}(0b00000111) == bv{8}(0);
  ensures r31 & bv{8}(0b10000000) == bv{8}(0);
  ensures r31 & bv{8}(0b01000000) == bv{8}(0b01000000);
}
{
  r0  := b0  & bv{8}(0b11111000);
  r31 := (b31 & bv{8}(0b01111111)) | bv{8}(0b01000000);
};
#end

/-- info:
Obligation: clamp_seed_ensures_0_506
Property: assert
Result: ✅ pass

Obligation: clamp_seed_ensures_1_548
Property: assert
Result: ✅ pass

Obligation: clamp_seed_ensures_2_612
Property: assert
Result: ✅ pass

Obligation: clamp_seed_ensures_3_659
Property: assert
Result: ✅ pass

Obligation: clamp_seed_ensures_4_706
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" bitvectorOpsSeed (options := .quiet)

theorem bitvectorOpsSeed_smtVCsCorrect : Strata.smtVCsCorrectBoole bitvectorOpsSeed := by
  gen_smt_vcs_boole
  all_goals (first | grind | decide)

-- Exercises ~, ^, >>, << (bit extraction, conditional swap, nibble ops).
private def bitvectorShiftXorSeed : StrataDDM.Program :=
#strata
program Boole;

procedure bv_shift_xor(b: bv W8, k: bv W8) returns (r_not: bv W8, r_xor: bv W8, r_hi: bv W8, r_lo: bv W8)
spec {
  ensures r_not == ~b;
  ensures r_xor == b ^ k;
  ensures r_hi  == b >> bv{8}(4);
  ensures r_lo  == b << bv{8}(4);
  // b AND its complement is always zero
  ensures b & ~b == bv{8}(0);
  // b XOR itself is always zero
  ensures b ^ b == bv{8}(0);
  // logical right shift fills upper bits with 0
  ensures (b >> bv{8}(4)) & bv{8}(0b11110000) == bv{8}(0);
  // left shift clears lower bits
  ensures (b << bv{8}(4)) & bv{8}(0b00001111) == bv{8}(0);
}
{
  r_not := ~b;
  r_xor := b ^ k;
  r_hi  := b >> bv{8}(4);
  r_lo  := b << bv{8}(4);
};
#end

/-- info:
Obligation: bv_shift_xor_ensures_0_1738
Property: assert
Result: ✅ pass

Obligation: bv_shift_xor_ensures_1_1761
Property: assert
Result: ✅ pass

Obligation: bv_shift_xor_ensures_2_1787
Property: assert
Result: ✅ pass

Obligation: bv_shift_xor_ensures_3_1821
Property: assert
Result: ✅ pass

Obligation: bv_shift_xor_ensures_4_1896
Property: assert
Result: ✅ pass

Obligation: bv_shift_xor_ensures_5_1959
Property: assert
Result: ✅ pass

Obligation: bv_shift_xor_ensures_6_2037
Property: assert
Result: ✅ pass

Obligation: bv_shift_xor_ensures_7_2130
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" bitvectorShiftXorSeed (options := .quiet)

theorem bitvectorShiftXorSeed_smtVCsCorrect : Strata.smtVCsCorrectBoole bitvectorShiftXorSeed := by
  gen_smt_vcs_boole
  all_goals (first | grind | decide)

-- Exercises ashr (arithmetic/signed right shift): vacated bits are filled with
-- the sign bit, unlike >> which fills with 0.
private def bitvectorSShrSeed : StrataDDM.Program :=
#strata
program Boole;

procedure bv_sshr(b: bv W8) returns (r: bv W8)
spec {
  ensures r == b ashr bv{8}(1);
  // negative value: sign bit propagates into vacated position
  ensures bv{8}(0b10000000) ashr bv{8}(1) == bv{8}(0b11000000);
  // positive value: behaves like unsigned shift
  ensures bv{8}(0b01000000) ashr bv{8}(1) == bv{8}(0b00100000);
}
{
  r := b ashr bv{8}(1);
};
#end

/-- info:
Obligation: bv_sshr_ensures_0_3405
Property: assert
Result: ✅ pass

Obligation: bv_sshr_ensures_1_3500
Property: assert
Result: ✅ pass

Obligation: bv_sshr_ensures_2_3613
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" bitvectorSShrSeed (options := .quiet)

theorem bitvectorSShrSeed_smtVCsCorrect : Strata.smtVCsCorrectBoole bitvectorSShrSeed := by
  gen_smt_vcs_boole
  all_goals (try smt +mono)

-- Exercises signed bitvector comparisons (slt, sle, sgt, sge).
-- In bv8 signed interpretation: 0xFF = -1, 0x7F = 127.
private def bitvectorSignedCmpSeed : StrataDDM.Program :=
#strata
program Boole;

procedure bv_signed_cmp(a: bv W8, b: bv W8) returns ()
spec {
  ensures bv{8}(255) slt bv{8}(0);
  ensures bv{8}(127) sgt bv{8}(0);
  ensures bv{8}(255) sle bv{8}(0);
  ensures bv{8}(127) sge bv{8}(0);
  ensures bv{8}(0)   sle bv{8}(0);
  ensures bv{8}(0)   sge bv{8}(0);
  ensures bv{8}(255) slt bv{8}(1);
}
{ };
#end

/-- info:
Obligation: bv_signed_cmp_ensures_0_4427
Property: assert
Result: ✅ pass

Obligation: bv_signed_cmp_ensures_1_4462
Property: assert
Result: ✅ pass

Obligation: bv_signed_cmp_ensures_2_4497
Property: assert
Result: ✅ pass

Obligation: bv_signed_cmp_ensures_3_4532
Property: assert
Result: ✅ pass

Obligation: bv_signed_cmp_ensures_4_4567
Property: assert
Result: ✅ pass

Obligation: bv_signed_cmp_ensures_5_4602
Property: assert
Result: ✅ pass

Obligation: bv_signed_cmp_ensures_6_4637
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" bitvectorSignedCmpSeed (options := .quiet)

theorem bitvectorSignedCmpSeed_smtVCsCorrect : Strata.smtVCsCorrectBoole bitvectorSignedCmpSeed := by
  gen_smt_vcs_boole
  all_goals (try smt +mono)
