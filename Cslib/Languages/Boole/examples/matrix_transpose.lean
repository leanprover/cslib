import Strata.MetaVerifier
import Smt

open Strata

def matrixTranspose : Strata.Program :=
#strata
program Boole;

type Matrix := Map int (Map int int);

procedure matrix_transpose (A: Matrix, m: int, n: int) returns (B: Matrix)
{
  var i: int;
  var j: int;

  i := 0;
  while (i < m)
  {
    j := 0;
    while (j < n)
    {
      // New map assignment syntax.
      B[i][j] := (A[j])[i];
      // Previously would have been:
      // B := B[i := (B[i])[j := (A[j])[i]]];
      j := j + 1;
    }
    i := i + 1;
  }
};
#end

-- Approach 1: Using an SMT solver to verify the VCs.
#eval Strata.Boole.verify "cvc5" matrixTranspose

-- Approach 2: Using Lean tactics to verify the VCs.
theorem matrixTranspose_smtVCsCorrect : Strata.smtVCsCorrect matrixTranspose := by
  gen_smt_vcs
  all_goals smt +mono
