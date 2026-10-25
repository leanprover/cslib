/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataBoole.MetaVerifier
import Smt

open Strata

/-
Near-upstream anchor:
- Source: RustCrypto `sha2/src/sha256/soft/compact.rs`

Loop counters and block indices use `int` rather than `bv W64`.
In the original Rust, the loop variable is `usize` — a non-negative integer,
not a bitvector. Encoding it as `bv W64` requires a `bv64_to_int_u` cast to
use it as a `Sequence` index; as an uninterpreted function that cast causes
unknown VCs for loop invariants that mix the counter with `Sequence.length`.
`int` with range bounds is the faithful encoding and eliminates the cast.

All 75 VCs in this seed pass, with cvc5 and in Lean. The original Rust source
uses features not yet supported in Boole:
- iterator protocol (`for x in iter.iter()` style loops)
- `Set` is reserved but has no Boole syntax, so the abstract set type
  here is named `AbstractSet`
- fixed-size array syntax (`[u8; 64]`)
- slice types

This seed works around them (using `Sequence`, `int` counters, and
`Sequence (bv W8)` instead of slices). A fuller port would need them supported.
-/

private def sha256_compact_indexed_program : StrataDDM.Program :=
#strata
program Boole;

 type nat;
 function int_to_nat (i : int) : nat;
 function Seq_len_bv32 (s : Sequence (bv W32)) : nat {
  int_to_nat(Sequence.length(s))
}
 function Seq_lib_insert_bv32 (s : Sequence (bv W32), i : int, val : bv W32) : Sequence (bv W32)
  requires 0 <= i && i <= Sequence.length(s);
 {
  Sequence.append(Sequence.build(Sequence.take(s, i), val), Sequence.drop(s, i))
}
 function Seq_new_bv32 (len : nat, f : int -> bv W32) : Sequence (bv W32);
 function Seq_lib_map_bv32 (s : Sequence (bv W32), f : int -> bv W32 -> bv W32) : Sequence (bv W32);
 function Seq_lib_map_values_bv32 (s : Sequence (bv W32), f : bv W32 -> bv W32) : Sequence (bv W32);
 type AbstractSet (T : Type);
 function Seq_lib_filter_bv32 (s : Sequence (bv W32), p : bv W32 -> bool) : Sequence (bv W32);
 function Seq_lib_sort_by_bv32 (s : Sequence (bv W32), less : bv W32 -> bv W32 -> bool) : Sequence (bv W32);
 function Seq_lib_to_set_bv32 (s : Sequence (bv W32)) : AbstractSet (bv W32);
 function Set_finite_bv32 (s : AbstractSet (bv W32)) : bool;
 function bv8_to_bv32_u (x : bv W8) : bv W32;
 function k32 () : Sequence (bv W32) {
  Sequence.of_bv32[bv{32}(1116352408), bv{32}(1899447441), bv{32}(3049323471), bv{32}(3921009573), bv{32}(961987163), bv{32}(1508970993), bv{32}(2453635748), bv{32}(2870763221), bv{32}(3624381080), bv{32}(310598401), bv{32}(607225278), bv{32}(1426881987), bv{32}(1925078388), bv{32}(2162078206), bv{32}(2614888103), bv{32}(3248222580), bv{32}(3835390401), bv{32}(4022224774), bv{32}(264347078), bv{32}(604807628), bv{32}(770255983), bv{32}(1249150122), bv{32}(1555081692), bv{32}(1996064986), bv{32}(2554220882), bv{32}(2821834349), bv{32}(2952996808), bv{32}(3210313671), bv{32}(3336571891), bv{32}(3584528711), bv{32}(113926993), bv{32}(338241895), bv{32}(666307205), bv{32}(773529912), bv{32}(1294757372), bv{32}(1396182291), bv{32}(1695183700), bv{32}(1986661051), bv{32}(2177026350), bv{32}(2456956037), bv{32}(2730485921), bv{32}(2820302411), bv{32}(3259730800), bv{32}(3345764771), bv{32}(3516065817), bv{32}(3600352804), bv{32}(4094571909), bv{32}(275423344), bv{32}(430227734), bv{32}(506948616), bv{32}(659060556), bv{32}(883997877), bv{32}(958139571), bv{32}(1322822218), bv{32}(1537002063), bv{32}(1747873779), bv{32}(1955562222), bv{32}(2024104815), bv{32}(2227730452), bv{32}(2361852424), bv{32}(2428436474), bv{32}(2756734187), bv{32}(3204031479), bv{32}(3329325298)]
}
 procedure rotate_right (x : bv W32, n : bv W32) returns (_pct_return : bv W32)
spec {
  requires bv{32}(1) <= n && n < bv{32}(32);
  } {
  assert bv{32}(0) <= n && n < bv{32}(32);
  assert bv{32}(0) <= bv{32}(32) - n && bv{32}(32) - n < bv{32}(32);
  _pct_return := x >> n | (x << bv{32}(32) - n);
  exit rotate_right;
};
 procedure to_u32s (block : Sequence (bv W8)) returns (_pct_return : (Sequence (bv W32)))
spec {
  requires Sequence.length(block) >= 64;
  ensures Sequence.length(_pct_return) == 16;
  } {
  var j : int;
  var res : (Sequence (bv W32));
  res := Sequence.of_bv32[bv{32}(0), bv{32}(0), bv{32}(0), bv{32}(0), bv{32}(0), bv{32}(0), bv{32}(0), bv{32}(0), bv{32}(0), bv{32}(0), bv{32}(0), bv{32}(0), bv{32}(0), bv{32}(0), bv{32}(0), bv{32}(0)];
  for i : int := 0 to 16 - 1
  invariant 0 <= i
  invariant Sequence.length(res) == 16
  {
    j := i * 4;
    assert 0 <= 24 && 24 < 32;
    assert 0 <= 16 && 16 < 32;
    assert 0 <= 8 && 8 < 32;
    res := Sequence.update(res, i, bv8_to_bv32_u(Sequence.select(block, j)) << bv{32}(24) | (bv8_to_bv32_u(Sequence.select(block, j + 1)) << bv{32}(16)) | (bv8_to_bv32_u(Sequence.select(block, j + 2)) << bv{32}(8)) | bv8_to_bv32_u(Sequence.select(block, j + 3)));
  }
  _pct_return := res;
  exit to_u32s;
};
 procedure compress_u32 (state : Sequence (bv W32), block : Sequence (bv W32)) returns (state_out : (Sequence (bv W32)))
spec {
  requires Sequence.length(state) >= 8 && Sequence.length(block) >= 16;
  ensures Sequence.length(state_out) == Sequence.length(state);
  } {
  var tmp15 : bv W32;
  var tmp16 : bv W32;
  var tmp22 : bv W32;
  var tmp23 : bv W32;
  var w15 : bv W32;
  var s0 : bv W32;
  var w2 : bv W32;
  var s1 : bv W32;
  var new_w : bv W32;
  var tmp36 : bv W32;
  var tmp37 : bv W32;
  var tmp38 : bv W32;
  var tmp40 : bv W32;
  var tmp44 : (Sequence (bv W32));
  var tmp48 : bv W32;
  var tmp49 : bv W32;
  var tmp51 : bv W32;
  var w : bv W32;
  var ch : bv W32;
  var t1 : bv W32;
  var maj : bv W32;
  var t2 : bv W32;
  var a : bv W32;
  var b : bv W32;
  var c : bv W32;
  var d : bv W32;
  var e : bv W32;
  var f : bv W32;
  var g : bv W32;
  var h : bv W32;
  var block_local : (Sequence (bv W32));
  state_out := state;
  block_local := block;
  a := Sequence.select(state_out, 0);
  b := Sequence.select(state_out, 1);
  c := Sequence.select(state_out, 2);
  d := Sequence.select(state_out, 3);
  e := Sequence.select(state_out, 4);
  f := Sequence.select(state_out, 5);
  g := Sequence.select(state_out, 6);
  h := Sequence.select(state_out, 7);
  for i : int := 0 to 64 - 1
  invariant 0 <= i
  invariant Sequence.length(block_local) >= 16
  invariant Sequence.length(state_out) >= 8
  {
    if (i < 16) {
      tmp36 := Sequence.select(block_local, i);
    } else {
      w15 := Sequence.select(block_local, (i - 15) mod 16);
      call tmp15 := rotate_right(w15, bv{32}(7));

      call tmp16 := rotate_right(w15, bv{32}(18));

      assert 0 <= 3 && 3 < 32;
      s0 := tmp15 ^ tmp16 ^ (w15 >> bv{32}(3));
      w2 := Sequence.select(block_local, (i - 2) mod 16);
      call tmp22 := rotate_right(w2, bv{32}(17));

      call tmp23 := rotate_right(w2, bv{32}(19));

      assert 0 <= 10 && 10 < 32;
      s1 := tmp22 ^ tmp23 ^ (w2 >> bv{32}(10));
      new_w := Sequence.select(block_local, (i - 16) mod 16) + s0 + Sequence.select(block_local, (i - 7) mod 16) + s1;
      block_local := Sequence.update(block_local, i mod 16, new_w);
      tmp36 := new_w;
    }
    w := tmp36;
    call tmp37 := rotate_right(e, bv{32}(6));

    call tmp38 := rotate_right(e, bv{32}(11));

    call tmp40 := rotate_right(e, bv{32}(25));

    s1 := tmp37 ^ tmp38 ^ tmp40;
    ch := e & f ^ (~e & g);
    tmp44 := k32;
    t1 := s1 + ch + Sequence.select(tmp44, i) + w + h;
    call tmp48 := rotate_right(a, bv{32}(2));

    call tmp49 := rotate_right(a, bv{32}(13));

    call tmp51 := rotate_right(a, bv{32}(22));

    s0 := tmp48 ^ tmp49 ^ tmp51;
    maj := a & b ^ (a & c) ^ (b & c);
    t2 := s0 + maj;
    h := g;
    g := f;
    f := e;
    e := d + t1;
    d := c;
    c := b;
    b := a;
    a := t1 + t2;
  }
  state_out := Sequence.update(state_out, 0, Sequence.select(state_out, 0) + a);
  state_out := Sequence.update(state_out, 1, Sequence.select(state_out, 1) + b);
  state_out := Sequence.update(state_out, 2, Sequence.select(state_out, 2) + c);
  state_out := Sequence.update(state_out, 3, Sequence.select(state_out, 3) + d);
  state_out := Sequence.update(state_out, 4, Sequence.select(state_out, 4) + e);
  state_out := Sequence.update(state_out, 5, Sequence.select(state_out, 5) + f);
  state_out := Sequence.update(state_out, 6, Sequence.select(state_out, 6) + g);
  state_out := Sequence.update(state_out, 7, Sequence.select(state_out, 7) + h);
  exit compress_u32;
};
 procedure compress (state : Sequence (bv W32), blocks : Sequence (Sequence (bv W8))) returns (state_out : (Sequence (bv W32)))
spec {
  requires Sequence.length(state) >= 8;
  requires ∀ k:int . 0 <= k && k < Sequence.length(blocks) ==> Sequence.length(Sequence.select(blocks, k)) >= 64;
  } {
  var tmp6 : (Sequence (bv W32));
  state_out := state;
  for k : int := 0 to Sequence.length(blocks) - 1
  invariant 0 <= k
  invariant Sequence.length(state_out) >= 8
  {
    call tmp6 := to_u32s(Sequence.select(blocks, k));

    call state_out := compress_u32(state_out, tmp6);

  }
  exit compress;
};
 procedure main () returns ()
spec {
  } {
  exit main;
};
#end

/-- info:
Obligation: Seq_lib_insert_bv32_body_calls_Sequence.take_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: Seq_lib_insert_bv32_body_calls_Sequence.drop_1
Property: out-of-bounds access check
Result: ✅ pass

Obligation: assert_2_3770
Property: assert
Result: ✅ pass

Obligation: assert_3_3813
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_entry_invariant_loop_49_0
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_entry_invariant_loop_49_1
Property: assert
Result: ✅ pass

Obligation: assert_6_4505
Property: assert
Result: ✅ pass

Obligation: assert_7_4536
Property: assert
Result: ✅ pass

Obligation: assert_8_4567
Property: assert
Result: ✅ pass

Obligation: set_res_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: set_res_calls_Sequence.select_1
Property: out-of-bounds access check
Result: ✅ pass

Obligation: set_res_calls_Sequence.select_2
Property: out-of-bounds access check
Result: ✅ pass

Obligation: set_res_calls_Sequence.select_3
Property: out-of-bounds access check
Result: ✅ pass

Obligation: set_res_calls_Sequence.update_4
Property: out-of-bounds access check
Result: ✅ pass

Obligation: insertLoopInvAssert_arbitrary_iter_maintain_invariant_loop_49_0
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_arbitrary_iter_maintain_invariant_loop_49_1
Property: assert
Result: ✅ pass

Obligation: to_u32s_ensures_5_4093
Property: assert
Result: ✅ pass

Obligation: set_a_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: set_b_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: set_c_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: set_d_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: set_e_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: set_f_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: set_g_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: set_h_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: insertLoopInvAssert_entry_invariant_loop_50_0
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_entry_invariant_loop_50_1
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_entry_invariant_loop_50_2
Property: assert
Result: ✅ pass

Obligation: set_tmp36_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: set_w15_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: callElimAssert_rotate_right_requires_1_3719_3
Property: assert
Result: ✅ pass

Obligation: callElimAssert_rotate_right_requires_1_3719_7
Property: assert
Result: ✅ pass

Obligation: assert_12_6568
Property: assert
Result: ✅ pass

Obligation: set_w2_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: callElimAssert_rotate_right_requires_1_3719_11
Property: assert
Result: ✅ pass

Obligation: callElimAssert_rotate_right_requires_1_3719_15
Property: assert
Result: ✅ pass

Obligation: assert_13_6807
Property: assert
Result: ✅ pass

Obligation: set_new_w_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: set_new_w_calls_Sequence.select_1
Property: out-of-bounds access check
Result: ✅ pass

Obligation: set_block_local_calls_Sequence.update_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: callElimAssert_rotate_right_requires_1_3719_19
Property: assert
Result: ✅ pass

Obligation: callElimAssert_rotate_right_requires_1_3719_23
Property: assert
Result: ✅ pass

Obligation: callElimAssert_rotate_right_requires_1_3719_27
Property: assert
Result: ✅ pass

Obligation: set_t1_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: callElimAssert_rotate_right_requires_1_3719_31
Property: assert
Result: ✅ pass

Obligation: callElimAssert_rotate_right_requires_1_3719_35
Property: assert
Result: ✅ pass

Obligation: callElimAssert_rotate_right_requires_1_3719_39
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_arbitrary_iter_maintain_invariant_loop_50_0
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_arbitrary_iter_maintain_invariant_loop_50_1
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_arbitrary_iter_maintain_invariant_loop_50_2
Property: assert
Result: ✅ pass

Obligation: set_state_out_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: set_state_out_calls_Sequence.update_1
Property: out-of-bounds access check
Result: ✅ pass

Obligation: set_state_out_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: set_state_out_calls_Sequence.update_1
Property: out-of-bounds access check
Result: ✅ pass

Obligation: set_state_out_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: set_state_out_calls_Sequence.update_1
Property: out-of-bounds access check
Result: ✅ pass

Obligation: set_state_out_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: set_state_out_calls_Sequence.update_1
Property: out-of-bounds access check
Result: ✅ pass

Obligation: set_state_out_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: set_state_out_calls_Sequence.update_1
Property: out-of-bounds access check
Result: ✅ pass

Obligation: set_state_out_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: set_state_out_calls_Sequence.update_1
Property: out-of-bounds access check
Result: ✅ pass

Obligation: set_state_out_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: set_state_out_calls_Sequence.update_1
Property: out-of-bounds access check
Result: ✅ pass

Obligation: set_state_out_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: set_state_out_calls_Sequence.update_1
Property: out-of-bounds access check
Result: ✅ pass

Obligation: compress_u32_ensures_11_5103
Property: assert
Result: ✅ pass

Obligation: compress_pre_compress_requires_16_8584_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: insertLoopInvAssert_entry_invariant_loop_51_0
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_entry_invariant_loop_51_1
Property: assert
Result: ✅ pass

Obligation: init_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: callElimAssert_to_u32s_requires_4_4052_42
Property: assert
Result: ✅ pass

Obligation: callElimAssert_compress_u32_requires_10_5031_47
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_arbitrary_iter_maintain_invariant_loop_51_0
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_arbitrary_iter_maintain_invariant_loop_51_1
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" sha256_compact_indexed_program (options := .quiet)

theorem sha256_compact_indexed_smtVCsCorrect :
    Strata.smtVCsCorrectBoole sha256_compact_indexed_program := by
  gen_smt_vcs_boole
  all_goals grind
