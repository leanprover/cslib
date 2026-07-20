import StrataBoole.MetaVerifier
import Smt

open Strata

/-
Verification example for the widening cast `as_uint(e)`, which lowers to the
native `Bv{n}.ToUInt` Core op (SMT-LIB 2.7 `ubv_to_int`) with no axioms
injected.
-/

private def wideningCastsSeed : StrataDDM.Program :=
#strata
program Boole;

// `as_uint(v[i])` lowers to `Bv32.ToUInt` Core op → SMT-LIB 2.7 `ubv_to_int`.
procedure widening_cast_seed(v: Map int bv32, n: int) returns ()
spec {
  requires 0 <= n;
  ensures ∀ i: int . 0 <= i && i < n ==> 0 <= (as_uint(v[i]));
}
{
  assert ∀ i: int . 0 <= i && i < n ==> 0 <= (as_uint(v[i]));
};
#end

/-- info:
Obligation: assert_2_544
Property: assert
Result: ✅ pass

Obligation: widening_cast_seed_ensures_1_474
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" wideningCastsSeed (options := .quiet)

/--
The VCs are provable regardless of `useArrayTheory`: under `true` the `Map` is
encoded as an SMT array (denoted by `SmtArray`), under `false` as an
uninterpreted sort with an axiomatized `select` function.
Since `as_uint` lowers to `ubv_to_int` (unsigned), the result is `Int.ofNat _`
which is always non-negative — no axiom required.
-/
theorem wideningCastsSeed_smtVCsCorrect : ∀ useArrayTheory,
    Strata.smtVCsCorrectBoole wideningCastsSeed { useArrayTheory } := by
  intro useArrayTheory
  cases useArrayTheory
  case false =>
    gen_smt_vcs_boole
    all_goals
      intro Map inst n select v hn i hi
      exact Int.natCast_nonneg _
  case true =>
    gen_smt_vcs_boole
    all_goals
      intro n v hn i hi
      exact Int.natCast_nonneg _
