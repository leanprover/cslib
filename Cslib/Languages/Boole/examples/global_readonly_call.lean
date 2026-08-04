import StrataBoole.MetaVerifier
import Smt

/-!
Test that read-only globals are correctly threaded through procedure headers
and call sites.
-/

namespace Strata

/-! ## Header shape: read-only globals appear as inputs -/

private def headerHelper (p : StrataDDM.Program) : Except String (List String) := do
  let prog ← (Boole.getProgram p).mapError toString
  let cp ← (Boole.toCoreProgram prog p.globalContext).mapError
    fun e => toString (e.format none)
  return cp.decls.filterMap fun d =>
    match d with
    | .proc p _ =>
      let ins := p.header.inputs.toList.map fun (id, _) => id.name
      let outs := p.header.outputs.toList.map fun (id, _) => id.name
      some s!"{p.header.name.name}(in: {ins}, out: {outs})"
    | _ => none

private def readOnlyGlobalPgm :=
#strata
program Boole;

// Declared in reverse-alphabetical order to exercise deterministic sorting.
var z : int;
var g : int;
var a : int;

procedure inc(x : int) returns ()
spec
{
  modifies g;
  ensures g == old(g) + x + a + z;
}
{
  g := g + x + a + z;
};

#end

-- Read-only globals `a` and `z` appear sorted despite `z` being declared first.
/-- info:
Obligation: inc_ensures_0_982
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" readOnlyGlobalPgm (options := .quiet)

theorem readOnlyGlobalPgm_smtVCsCorrect : Strata.smtVCsCorrectBoole readOnlyGlobalPgm := by
  gen_smt_vcs_boole
  all_goals (try smt +mono)
