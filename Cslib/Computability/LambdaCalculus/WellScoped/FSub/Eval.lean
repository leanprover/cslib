/-
Copyright (c) 2025 Yichen Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yichen Xu.
-/

/-
# Big-step evaluator for System F<:
-/

import Cslib.Computability.LambdaCalculus.WellScoped.FSub.Syntax

/-- The result of evaluating an expression. Evaluation may succeed with a value,
    fail with an error, or exhaust its fuel allocation. -/
inductive Result (s : Sig) where
/-- Successful evaluation to a value -/
| ok : Exp s -> Result s
/-- Runtime error (e.g., free variable, type mismatch) -/
| err : Result s
/-- Evaluation did not terminate within fuel limit -/
| nonterm : Result s

/-- Big-step evaluator with fuel-based termination. -/
def eval : Nat -> Exp s -> Result s
| 0, _ => .nonterm
| _, .var _ => .err
| _, .abs A e => .ok (.abs A e)
| _, .tabs S e => .ok (.tabs S e)
| fuel+1, .app e1 e2 =>
  match eval fuel e1 with
  | .ok (.abs _ t1) =>
    eval fuel (t1.open_var e2)
  | .ok _ => .err
  | .err => .err
  | .nonterm => .nonterm
| fuel+1, .tapp e A =>
  match eval fuel e with
  | .ok (.tabs _ t) =>
    eval fuel (t.open_tvar A)
  | .ok _ => .err
  | .err => .err
  | .nonterm => .nonterm
