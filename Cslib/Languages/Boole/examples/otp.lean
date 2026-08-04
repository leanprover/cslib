import StrataBoole.MetaVerifier
import Smt

open Strata

/-
Verification examples for the one-time-pad round-trip property
(`Decrypt(key, Encrypt(key, m)) == m`), across three data representations:
`Map int int` arrays (`one_time_pad_map_program`), an inductive `List`
datatype (`one_time_pad_ll_program`), and Boole's native `Sequence` type
(`one_time_pad_seq_program`).
-/

private def one_time_pad_map_program : StrataDDM.Program :=
#strata
program Boole;

type Array := Map int int;

procedure Encrypt(key : Array, message : Array, len : int)
  returns (cipher : Array)
spec
{
  ensures (∀ i:int . 0 <= i && i < len ==> cipher[i] == key[i] + message[i]);
}
{
  for i : int := 0 to (len-1) by 1
    invariant ∀ j:int . 0 <= j && j < i ==> cipher[j] == key[j] + message[j]
  {
    cipher[i] := key[i] + message[i];
  }
};

procedure Decrypt(key : Array, message : Array, len : int)
  returns (cipher : Array)
spec
{
  ensures (∀ i:int . 0 <= i && i < len ==> cipher[i] == message[i] - key[i]);
}
{
  for i : int := 0 to (len-1) by 1
    invariant ∀ j:int . 0 <= j && j < i ==> cipher[j] == message[j] - key[j]
  {
    cipher[i] := message[i] - key[i];
  }
};

procedure RoundTrip(key : Array, message : Array, len : int)
  returns (roundtrip : Array)
spec
{
  ensures (∀ i:int . 0 <= i && i < len ==> roundtrip[i] == message[i]);
}
{
  var encrypted : Array;
  call encrypted := Encrypt(key, message, len);
  call roundtrip := Decrypt(key, encrypted, len);
};

#end

theorem one_time_pad_map_program_smtVCsCorrect : Strata.smtVCsCorrectBoole one_time_pad_map_program := by
  gen_smt_vcs_boole
  all_goals (first | grind | decide)

private def one_time_pad_ll_program : StrataDDM.Program :=
#strata
program Boole;

datatype List () { Nil(), Cons(head: int, tail: List) };

// Structural same-length check: axiom directly exposes isCons(message) when key is Cons,
// avoiding indirect Len counting arguments that SMT solvers cannot resolve.
rec function SameLen (@[cases] key : List, message : List) : bool
{
  if List..isNil(key) then List..isNil(message)
  else List..isCons(message) && SameLen(List..tail!(key), List..tail!(message))
};

rec function EncryptSpec (@[cases] key : List, message : List) : List
{
  if List..isNil(key) then Nil()
  else Cons(
    List..head(key) + List..head!(message),
    EncryptSpec(List..tail(key), List..tail!(message))
  )
};

rec function DecryptSpec (@[cases] key : List, message : List) : List
{
  if List..isNil(key) then Nil()
  else Cons(
    List..head!(message) - List..head(key),
    DecryptSpec(List..tail(key), List..tail!(message))
  )
};

procedure Encrypt(key : List, message : List) returns (cipher : List)
spec
{
  requires SameLen(key, message);
  ensures cipher == EncryptSpec(key, message);
  ensures SameLen(key, cipher);
}
{
  if (List..isNil(key)) {
    cipher := Nil();
  } else {
    var t : List;
    call t := Encrypt(List..tail!(key), List..tail!(message));
    cipher := Cons(List..head!(key) + List..head!(message), t);
  }
};

procedure Decrypt(key : List, message : List) returns (result : List)
spec
{
  requires SameLen(key, message);
  ensures result == DecryptSpec(key, message);
}
{
  if (List..isNil(key)) {
    result := Nil();
  } else {
    var t : List;
    call t := Decrypt(List..tail!(key), List..tail!(message));
    result := Cons(List..head!(message) - List..head!(key), t);
  }
};

// Lemma: decrypting an encrypted message recovers the original, proven by structural induction.
procedure RoundTripLemma(key : List, message : List)
spec
{
  requires SameLen(key, message);
  ensures DecryptSpec(key, EncryptSpec(key, message)) == message;
}
{
  if (List..isCons(key)) {
    call RoundTripLemma(List..tail!(key), List..tail!(message));
  }
};

procedure RoundTrip(key : List, message : List) returns (roundtrip : List)
spec
{
  requires SameLen(key, message);
  ensures roundtrip == message;
}
{
  var encrypted : List;
  call encrypted := Encrypt(key, message);
  call roundtrip := Decrypt(key, encrypted);
  call RoundTripLemma(key, message);
};

#end

/-- info:
Obligation: SameLen_terminates_0
Property: assert
Result: ✅ pass

Obligation: EncryptSpec_body_calls_List..head_0
Property: assert
Result: ✅ pass

Obligation: EncryptSpec_body_calls_List..tail_1
Property: assert
Result: ✅ pass

Obligation: EncryptSpec_terminates_0
Property: assert
Result: ✅ pass

Obligation: DecryptSpec_body_calls_List..head_0
Property: assert
Result: ✅ pass

Obligation: DecryptSpec_body_calls_List..tail_1
Property: assert
Result: ✅ pass

Obligation: DecryptSpec_terminates_0
Property: assert
Result: ✅ pass

Obligation: callElimAssert_Encrypt_requires_0_2680_3
Property: assert
Result: ✅ pass

Obligation: Encrypt_ensures_1_2714
Property: assert
Result: ✅ pass

Obligation: Encrypt_ensures_2_2761
Property: assert
Result: ✅ pass

Obligation: callElimAssert_Decrypt_requires_3_3085_9
Property: assert
Result: ✅ pass

Obligation: Decrypt_ensures_4_3119
Property: assert
Result: ✅ pass

Obligation: callElimAssert_RoundTripLemma_requires_5_3538_13
Property: assert
Result: ✅ pass

Obligation: RoundTripLemma_ensures_6_3572
Property: assert
Result: ✅ pass

Obligation: callElimAssert_Encrypt_requires_0_2680_27
Property: assert
Result: ✅ pass

Obligation: callElimAssert_Decrypt_requires_3_3085_22
Property: assert
Result: ✅ pass

Obligation: callElimAssert_RoundTripLemma_requires_5_3538_17
Property: assert
Result: ✅ pass

Obligation: RoundTrip_ensures_8_3858
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" one_time_pad_ll_program (options := .quiet)

-- TODO: re-enable once `gen_smt_vcs_boole` is fixed for this program: it currently errors
-- internally ("Error: variable 'Translate.Var.us { name := "List", arity := 0 }' not found in
-- context") before any tactic runs, the same class of compiler bug as quicksort.lean; the cvc5
-- #eval verify above still proves it.
/-
theorem one_time_pad_ll_program_smtVCsCorrect : Strata.smtVCsCorrectBoole one_time_pad_ll_program := by
  gen_smt_vcs_boole
  all_goals (first | smt +mono | smt | omega | trivial | grind)
-/

private def one_time_pad_seq_program : StrataDDM.Program :=
#strata
program Boole;

procedure Encrypt(key : Sequence int, message : Sequence int, len : int) returns (cipher : Sequence int)
spec
{
  requires 0 <= len;
  requires Sequence.length(key) >= len;
  requires Sequence.length(message) >= len;
  ensures Sequence.length(cipher) == len;
  ensures (forall i : int :: 0 <= i && i < len ==>
    Sequence.select(cipher, i) == Sequence.select(key, i) + Sequence.select(message, i));
}
{
  cipher := Sequence.take(key, 0);
  var i : int;
  i := 0;
  while (i < len)
    decreases len - i
    invariant 0 <= i
    invariant i <= len
    invariant Sequence.length(cipher) == i
    invariant (forall j : int :: 0 <= j && j < i ==>
      Sequence.select(cipher, j) == Sequence.select(key, j) + Sequence.select(message, j))
  {
    cipher := Sequence.build(cipher, Sequence.select(key, i) + Sequence.select(message, i));
    i := i + 1;
  }
};

procedure Decrypt(key : Sequence int, message : Sequence int, len : int) returns (result : Sequence int)
spec
{
  requires 0 <= len;
  requires Sequence.length(key) >= len;
  requires Sequence.length(message) >= len;
  ensures Sequence.length(result) == len;
  ensures (forall i : int :: 0 <= i && i < len ==>
    Sequence.select(result, i) == Sequence.select(message, i) - Sequence.select(key, i));
}
{
  result := Sequence.take(key, 0);
  var i : int;
  i := 0;
  while (i < len)
    decreases len - i
    invariant 0 <= i
    invariant i <= len
    invariant Sequence.length(result) == i
    invariant (forall j : int :: 0 <= j && j < i ==>
      Sequence.select(result, j) == Sequence.select(message, j) - Sequence.select(key, j))
  {
    result := Sequence.build(result, Sequence.select(message, i) - Sequence.select(key, i));
    i := i + 1;
  }
};

procedure RoundTrip(key : Sequence int, message : Sequence int, len : int) returns (roundtrip : Sequence int)
spec
{
  requires 0 <= len;
  requires Sequence.length(key) >= len;
  requires Sequence.length(message) >= len;
  ensures Sequence.length(roundtrip) == len;
  ensures (forall i : int :: 0 <= i && i < len ==> Sequence.select(roundtrip, i) == Sequence.select(message, i));
}
{
  var encrypted : Sequence int;
  call encrypted := Encrypt(key, message, len);
  call roundtrip := Decrypt(key, encrypted, len);
};

#end

/-- info:
Obligation: Encrypt_post_Encrypt_ensures_4_6465_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: Encrypt_post_Encrypt_ensures_4_6465_calls_Sequence.select_1
Property: out-of-bounds access check
Result: ✅ pass

Obligation: Encrypt_post_Encrypt_ensures_4_6465_calls_Sequence.select_2
Property: out-of-bounds access check
Result: ✅ pass

Obligation: set_cipher_calls_Sequence.take_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: loop_invariant_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: loop_invariant_calls_Sequence.select_1
Property: out-of-bounds access check
Result: ✅ pass

Obligation: loop_invariant_calls_Sequence.select_2
Property: out-of-bounds access check
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

Obligation: entry_invariant_0_3
Property: assert
Result: ✅ pass

Obligation: measure_lb_0
Property: assert
Result: ✅ pass

Obligation: set_cipher_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: set_cipher_calls_Sequence.select_1
Property: out-of-bounds access check
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

Obligation: arbitrary_iter_maintain_invariant_0_3
Property: assert
Result: ✅ pass

Obligation: measure_decrease_0
Property: assert
Result: ✅ pass

Obligation: Encrypt_ensures_3_6423
Property: assert
Result: ✅ pass

Obligation: Encrypt_ensures_4_6465
Property: assert
Result: ✅ pass

Obligation: Decrypt_post_Decrypt_ensures_9_7321_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: Decrypt_post_Decrypt_ensures_9_7321_calls_Sequence.select_1
Property: out-of-bounds access check
Result: ✅ pass

Obligation: Decrypt_post_Decrypt_ensures_9_7321_calls_Sequence.select_2
Property: out-of-bounds access check
Result: ✅ pass

Obligation: set_result_calls_Sequence.take_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: loop_invariant_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: loop_invariant_calls_Sequence.select_1
Property: out-of-bounds access check
Result: ✅ pass

Obligation: loop_invariant_calls_Sequence.select_2
Property: out-of-bounds access check
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

Obligation: entry_invariant_0_3
Property: assert
Result: ✅ pass

Obligation: measure_lb_0
Property: assert
Result: ✅ pass

Obligation: set_result_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: set_result_calls_Sequence.select_1
Property: out-of-bounds access check
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

Obligation: arbitrary_iter_maintain_invariant_0_3
Property: assert
Result: ✅ pass

Obligation: measure_decrease_0
Property: assert
Result: ✅ pass

Obligation: Decrypt_ensures_8_7279
Property: assert
Result: ✅ pass

Obligation: Decrypt_ensures_9_7321
Property: assert
Result: ✅ pass

Obligation: RoundTrip_post_RoundTrip_ensures_14_8185_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: RoundTrip_post_RoundTrip_ensures_14_8185_calls_Sequence.select_1
Property: out-of-bounds access check
Result: ✅ pass

Obligation: callElimAssert_Encrypt_requires_0_6318_13
Property: assert
Result: ✅ pass

Obligation: callElimAssert_Encrypt_requires_1_6339_14
Property: assert
Result: ✅ pass

Obligation: callElimAssert_Encrypt_requires_2_6379_15
Property: assert
Result: ✅ pass

Obligation: assume_callElimAssume_Encrypt_ensures_4_6465_17_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: assume_callElimAssume_Encrypt_ensures_4_6465_17_calls_Sequence.select_1
Property: out-of-bounds access check
Result: ✅ pass

Obligation: assume_callElimAssume_Encrypt_ensures_4_6465_17_calls_Sequence.select_2
Property: out-of-bounds access check
Result: ✅ pass

Obligation: callElimAssert_Decrypt_requires_5_7174_4
Property: assert
Result: ✅ pass

Obligation: callElimAssert_Decrypt_requires_6_7195_5
Property: assert
Result: ✅ pass

Obligation: callElimAssert_Decrypt_requires_7_7235_6
Property: assert
Result: ✅ pass

Obligation: assume_callElimAssume_Decrypt_ensures_9_7321_8_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: assume_callElimAssume_Decrypt_ensures_9_7321_8_calls_Sequence.select_1
Property: out-of-bounds access check
Result: ✅ pass

Obligation: assume_callElimAssume_Decrypt_ensures_9_7321_8_calls_Sequence.select_2
Property: out-of-bounds access check
Result: ✅ pass

Obligation: RoundTrip_ensures_13_8140
Property: assert
Result: ✅ pass

Obligation: RoundTrip_ensures_14_8185
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" one_time_pad_seq_program (options := .quiet)

theorem one_time_pad_seq_program_smtVCsCorrect : Strata.smtVCsCorrectBoole one_time_pad_seq_program := by
  gen_smt_vcs_boole
  all_goals (first | smt +mono | smt | omega | trivial | grind)
