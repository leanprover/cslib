import StrataBoole.MetaVerifier
import Smt

open Strata

/-
Verification example for `Sequence T` slicing operations in Boole:
`Sequence.length`, `Sequence.select`, `Sequence.take`, `Sequence.drop`,
`Sequence.append` (Core Grammar), plus the Boole-specific `Sequence.skip`,
`Sequence.dropFirst`, `Sequence.subrange`. Dot-method syntax (`s.len()`) isn't
used because the DDM init dialect parses `id.id` as a qualified identifier
before Expr-level trailing rules apply; `"Sequence.xxx"` as a single string
keyword token avoids that ambiguity.
-/

private def seqSlicingSeed : StrataDDM.Program :=
#strata
program Boole;

function seq_sum_first_two(s: Sequence int) : int;
axiom ∀ s: Sequence int .
  Sequence.length(s) >= 2 ==>
    seq_sum_first_two(s) == Sequence.select(s, 0) + Sequence.select(s, 1);

procedure seq_slicing_seed(s: Sequence int) returns (head: int, tail: Sequence int, mid: Sequence int)
spec {
  requires Sequence.length(s) >= 4;
  ensures head == Sequence.select(s, 0);
  ensures Sequence.length(tail) == Sequence.length(s) - 1;
  ensures Sequence.length(mid) == 2;
  ensures Sequence.select(mid, 0) == Sequence.select(s, 1);
  ensures Sequence.select(mid, 1) == Sequence.select(s, 2);
}
{
  head := Sequence.select(s, 0);
  tail := Sequence.skip(s, 1);
  mid  := Sequence.subrange(s, 1, 3);
};

procedure seq_empty_bv64_seed() returns (s: Sequence bv64)
spec {
  ensures Sequence.length(s) == 1;
  ensures Sequence.select(s, 0) == bv{64}(0);
}
{
  s := Sequence.build(Sequence.empty_bv64, bv{64}(0));
};

rec function reconstruct(naf: Sequence int) : int
  decreases Sequence.length(naf)
{
  if Sequence.length(naf) == 0 then
    0
  else
    Sequence.select(naf, 0) + 2 * reconstruct(Sequence.skip(naf, 1))
}
;
#end

/-- info:
Obligation: seq_slicing_seed_post_seq_slicing_seed_ensures_2_953_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: seq_slicing_seed_post_seq_slicing_seed_ensures_5_1090_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: seq_slicing_seed_post_seq_slicing_seed_ensures_5_1090_calls_Sequence.select_1
Property: out-of-bounds access check
Result: ✅ pass

Obligation: seq_slicing_seed_post_seq_slicing_seed_ensures_6_1150_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: seq_slicing_seed_post_seq_slicing_seed_ensures_6_1150_calls_Sequence.select_1
Property: out-of-bounds access check
Result: ✅ pass

Obligation: set_head_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: set_tail_calls_Sequence.drop_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: set_mid_calls_Sequence.drop_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: set_mid_calls_Sequence.take_1
Property: out-of-bounds access check
Result: ✅ pass

Obligation: seq_slicing_seed_ensures_2_953
Property: assert
Result: ✅ pass

Obligation: seq_slicing_seed_ensures_3_994
Property: assert
Result: ✅ pass

Obligation: seq_slicing_seed_ensures_4_1053
Property: assert
Result: ✅ pass

Obligation: seq_slicing_seed_ensures_5_1090
Property: assert
Result: ✅ pass

Obligation: seq_slicing_seed_ensures_6_1150
Property: assert
Result: ✅ pass

Obligation: seq_empty_bv64_seed_post_seq_empty_bv64_seed_ensures_8_1421_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: seq_empty_bv64_seed_ensures_7_1386
Property: assert
Result: ✅ pass

Obligation: seq_empty_bv64_seed_ensures_8_1421
Property: assert
Result: ✅ pass

Obligation: reconstruct_body_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: reconstruct_body_calls_Sequence.drop_1
Property: out-of-bounds access check
Result: ✅ pass

Obligation: reconstruct_terminates_0
Property: assert
Result: ✅ pass

Obligation: reconstruct_terminates_1
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" seqSlicingSeed (options := .quiet)

-- `smt`/`smt +mono` trigger a kernel application type mismatch here (not just a tactic
-- failure) on the `Sequence` obligations, so they're deliberately excluded.
theorem seqSlicingSeed_smtVCsCorrect : Strata.smtVCsCorrectBoole seqSlicingSeed := by
  gen_smt_vcs_boole
  all_goals (first | omega | trivial | grind)
