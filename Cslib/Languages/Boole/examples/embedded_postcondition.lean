import StrataBoole.MetaVerifier
import Smt

open Strata

/-
Verification example for inline `let` bindings inside `ensures` clauses:
`let v := value in body` is a first-class Boole expression form that lowers
by substituting the converted value expression for the bound variable in the
converted body. This lets multi-step postconditions name intermediate
subexpressions without auxiliary definitions.
-/

private def embeddedPostconditionSeed : StrataDDM.Program :=
#strata
program Boole;

function shifted(n: int, k: int) : int;
axiom (∀ n: int, k: int . shifted(n, k) == n + k);

function negated(x: int) : int;
axiom (∀ x: int . negated(x) == -x);

procedure shift_negate(n: int, k: int) returns (r: int)
spec {
  ensures let s : int := shifted(n, k) in
          let d : int := negated(s) in
          r == d;
}
{ r := -(n + k); };
#end

/-- info:
Obligation: shift_negate_ensures_2_724
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" embeddedPostconditionSeed (options := .quiet)

theorem embeddedPostconditionSeed_smtVCsCorrect : Strata.smtVCsCorrectBoole embeddedPostconditionSeed := by
  gen_smt_vcs_boole
  all_goals (try smt +mono)
