/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Cslib.Algorithms.StatefulProcesses.DiffieHellman.Basic

namespace CslibTests.DiffieHellman

open Cslib.Mech Cslib.Algorithms.StatefulProcesses.DiffieHellman

variable {Pid Var : Type*} (params : Params Pid Var)

-- Each role must use its own exponent in its public message.
example (σ : LocalStore Var params.Val) :
    (funEval params).EvalExpr σ (aliceComputeMesg params) (.zMod (params.g ^ params.a)) := by
  apply FunCallEval.EvalExpr.call (.cons .val (.cons .val (.cons .val .nil)))
  intro hmod
  rfl

example (σ : LocalStore Var params.Val) :
    (funEval params).EvalExpr σ (bobComputeMesg params) (.zMod (params.g ^ params.b)) := by
  apply FunCallEval.EvalExpr.call (.cons .val (.cons .val (.cons .val .nil)))
  intro hmod
  rfl

-- Each role must also use its own exponent on the received message.
example (σ : LocalStore Var params.Val) (message : ZMod params.p)
    (h : σ params.y = .zMod message) :
    (funEval params).EvalExpr σ (aliceComputeSharedSecret params) (.zMod (message ^ params.a)) := by
  apply FunCallEval.EvalExpr.call (.cons .val (.cons .var (.cons .val .nil)))
  simp only [h, funEval]
  intro hmod
  rfl

example (σ : LocalStore Var params.Val) (message : ZMod params.p)
    (h : σ params.x = .zMod message) :
    (funEval params).EvalExpr σ (bobComputeSharedSecret params) (.zMod (message ^ params.b)) := by
  apply FunCallEval.EvalExpr.call (.cons .val (.cons .var (.cons .val .nil)))
  simp only [h, funEval]
  intro hmod
  rfl

end CslibTests.DiffieHellman
