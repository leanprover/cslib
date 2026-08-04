import StrataBoole.MetaVerifier
import Smt

open Strata

/-
Verification example standing in for model types not natively modeled in
Boole (e.g. `Thread`, `Cell`, `Rwlock`), using an abstract uninterpreted type
and stub operations instead.
-/

private def abstractTypesAndStubsSeed : StrataDDM.Program :=
#strata
program Boole;

type Thread;
type Cell;
type Rwlock;
type SeqInt;

function Seq_len(s: SeqInt) : int;

axiom (∀ s: SeqInt . (0 <= Seq_len(s)));

procedure abstract_type_and_stub_seed(s: SeqInt) returns ()
spec {
  requires 0 <= Seq_len(s);
}
{
  assert 0 <= Seq_len(s);
};
#end

/-- info:
Obligation: assert_2_562
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" abstractTypesAndStubsSeed (options := .quiet)

theorem abstractTypesAndStubsSeed_smtVCsCorrect : Strata.smtVCsCorrectBoole abstractTypesAndStubsSeed := by
  gen_smt_vcs_boole
  all_goals (try smt +mono)
