import StrataBoole.MetaVerifier
import Smt

open Strata

/-
Verification example for bitwise operators (`&`, `|`, `^`, `>>`, `>>s`, `<<`,
`~`) on `bvN` types, lowering to the corresponding `Bv{N}.And`/`Or`/`Xor`/
`UShr`/`SShr`/`Shl`/`Not` Core operations (`>>` is unsigned, `>>s` is signed).
-/

-- Exercises & and | (X25519 scalar clamping).
private def bitvectorOpsSeed : StrataDDM.Program :=
#strata
program Boole;

procedure clamp_seed(b0: bv8, b31: bv8) returns (r0: bv8, r31: bv8)
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
Obligation: clamp_seed_ensures_0_496
Property: assert
Result: ✅ pass

Obligation: clamp_seed_ensures_1_538
Property: assert
Result: ✅ pass

Obligation: clamp_seed_ensures_2_602
Property: assert
Result: ✅ pass

Obligation: clamp_seed_ensures_3_649
Property: assert
Result: ✅ pass

Obligation: clamp_seed_ensures_4_696
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

procedure bv_shift_xor(b: bv8, k: bv8) returns (r_not: bv8, r_xor: bv8, r_hi: bv8, r_lo: bv8)
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
Obligation: bv_shift_xor_ensures_0_1716
Property: assert
Result: ✅ pass

Obligation: bv_shift_xor_ensures_1_1739
Property: assert
Result: ✅ pass

Obligation: bv_shift_xor_ensures_2_1765
Property: assert
Result: ✅ pass

Obligation: bv_shift_xor_ensures_3_1799
Property: assert
Result: ✅ pass

Obligation: bv_shift_xor_ensures_4_1874
Property: assert
Result: ✅ pass

Obligation: bv_shift_xor_ensures_5_1937
Property: assert
Result: ✅ pass

Obligation: bv_shift_xor_ensures_6_2015
Property: assert
Result: ✅ pass

Obligation: bv_shift_xor_ensures_7_2108
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" bitvectorShiftXorSeed (options := .quiet)

theorem bitvectorShiftXorSeed_smtVCsCorrect : Strata.smtVCsCorrectBoole bitvectorShiftXorSeed := by
  gen_smt_vcs_boole
  all_goals (first | grind | decide)

-- Exercises >>s (arithmetic/signed right shift): vacated bits are filled with
-- the sign bit, unlike >> which fills with 0.
private def bitvectorSShrSeed : StrataDDM.Program :=
#strata
program Boole;

procedure bv_sshr(b: bv8) returns (r: bv8)
spec {
  ensures r == b >>s bv{8}(1);
  // negative value: sign bit propagates into vacated position
  ensures bv{8}(0b10000000) >>s bv{8}(1) == bv{8}(0b11000000);
  // positive value: behaves like unsigned shift
  ensures bv{8}(0b01000000) >>s bv{8}(1) == bv{8}(0b00100000);
}
{
  r := b >>s bv{8}(1);
};
#end

/-- info:
Obligation: bv_sshr_ensures_0_3378
Property: assert
Result: ✅ pass

Obligation: bv_sshr_ensures_1_3472
Property: assert
Result: ✅ pass

Obligation: bv_sshr_ensures_2_3584
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" bitvectorSShrSeed (options := .quiet)

theorem bitvectorSShrSeed_smtVCsCorrect : Strata.smtVCsCorrectBoole bitvectorSShrSeed := by
  gen_smt_vcs_boole
  all_goals (try smt +mono)

-- Exercises signed bitvector comparisons (<s, <=s, >s, >=s).
-- In bv8 signed interpretation: 0xFF = -1, 0x7F = 127.
private def bitvectorSignedCmpSeed : StrataDDM.Program :=
#strata
program Boole;

procedure bv_signed_cmp(a: bv8, b: bv8) returns ()
spec {
  ensures bv{8}(255) <s  bv{8}(0);
  ensures bv{8}(127) >s  bv{8}(0);
  ensures bv{8}(255) <=s bv{8}(0);
  ensures bv{8}(127) >=s bv{8}(0);
  ensures bv{8}(0)   <=s bv{8}(0);
  ensures bv{8}(0)   >=s bv{8}(0);
  ensures bv{8}(255) <s  bv{8}(1);
}
{ };
#end

/-- info:
Obligation: bv_signed_cmp_ensures_0_4390
Property: assert
Result: ✅ pass

Obligation: bv_signed_cmp_ensures_1_4425
Property: assert
Result: ✅ pass

Obligation: bv_signed_cmp_ensures_2_4460
Property: assert
Result: ✅ pass

Obligation: bv_signed_cmp_ensures_3_4495
Property: assert
Result: ✅ pass

Obligation: bv_signed_cmp_ensures_4_4530
Property: assert
Result: ✅ pass

Obligation: bv_signed_cmp_ensures_5_4565
Property: assert
Result: ✅ pass

Obligation: bv_signed_cmp_ensures_6_4600
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" bitvectorSignedCmpSeed (options := .quiet)

theorem bitvectorSignedCmpSeed_smtVCsCorrect : Strata.smtVCsCorrectBoole bitvectorSignedCmpSeed := by
  gen_smt_vcs_boole
  all_goals (try smt +mono)
