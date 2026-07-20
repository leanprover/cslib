import StrataBoole.MetaVerifier
import Smt

open Strata

/-
Verification example modeling modular scalar reduction (as used by
`Scalar::from_bytes_mod_order_wide` in curve25519-dalek): `ByteArray64` and
`Scalar` are kept abstract, and two axioms capture what `reduce` guarantees,
so the procedure body verifies by axiom instantiation alone.
-/

private def scalarReduceSeed : StrataDDM.Program :=
#strata
program Boole;

type ByteArray64;
type Scalar;

function reduce(b: ByteArray64) : Scalar;
function scalar_as_canonical(s: Scalar) : int;
function u8_64_as_group_canonical(b: ByteArray64) : int;
function is_canonical_scalar(s: Scalar) : bool;

// Gap #11 (PR #1167) is now merged; u8_64_as_group_canonical can be given a
// real recursive definition using Sequence bv8.  The recursive
// byte-accumulation (little-endian) follows dalek-lite's bytes_seq_as_nat
// (curve25519-dalek/src/specs/core_specs.rs):
//
//   function bv8_to_int_u(x: bv8) : int;
//   function group_order() : int;
//
//   rec function bytes_seq_as_nat(b: Sequence bv8) : int
//     decreases Sequence.length(b)
//   {
//     if Sequence.length(b) == 0 then
//       0
//     else
//       bv8_to_int_u(Sequence.select(b, 0)) + 256 * bytes_seq_as_nat(Sequence.skip(b, 1))
//   }
//
//   function u8_64_as_group_canonical(b: Sequence bv8) : int {
//     bytes_seq_as_nat(b) mod group_order()
//   }
//
// Note: int-recursive functions are pure UFs in SMT (no definitional axioms).
// Functional properties still require manual axioms — the two axioms below
// (scalar_as_canonical/reduce and is_canonical_scalar/reduce) continue to apply.

axiom (∀ b: ByteArray64 . scalar_as_canonical(reduce(b)) == u8_64_as_group_canonical(b));
axiom (∀ b: ByteArray64 . is_canonical_scalar(reduce(b)));

procedure from_bytes_mod_order_wide(bytes: ByteArray64) returns (result: Scalar)
spec {
  ensures scalar_as_canonical(result) == u8_64_as_group_canonical(bytes);
  ensures is_canonical_scalar(result);
}
{
  result := reduce(bytes);
};
#end

/-- info:
Obligation: from_bytes_mod_order_wide_ensures_2_1863
Property: assert
Result: ✅ pass

Obligation: from_bytes_mod_order_wide_ensures_3_1937
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" scalarReduceSeed (options := .quiet)

theorem scalarReduceSeed_smtVCsCorrect : Strata.smtVCsCorrectBoole scalarReduceSeed := by
  gen_smt_vcs_boole
  all_goals (try smt +mono)
