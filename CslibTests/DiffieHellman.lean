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
  exact ⟨rfl, rfl⟩

example (σ : LocalStore Var params.Val) :
    (funEval params).EvalExpr σ (bobComputeMesg params) (.zMod (params.g ^ params.b)) := by
  apply FunCallEval.EvalExpr.call (.cons .val (.cons .val (.cons .val .nil)))
  exact ⟨rfl, rfl⟩

-- Each role must also use its own exponent on the received message.
example (σ : LocalStore Var params.Val) (message : ZMod params.p)
    (h : σ params.y = .zMod message) :
    (funEval params).EvalExpr σ (aliceComputeSharedSecret params) (.zMod (message ^ params.a)) := by
  apply FunCallEval.EvalExpr.call (.cons .val (.cons .var (.cons .val .nil)))
  simp [h, funEval, computeSharedSecret]

example (σ : LocalStore Var params.Val) (message : ZMod params.p)
    (h : σ params.x = .zMod message) :
    (funEval params).EvalExpr σ (bobComputeSharedSecret params) (.zMod (message ^ params.b)) := by
  apply FunCallEval.EvalExpr.call (.cons .val (.cons .var (.cons .val .nil)))
  simp [h, funEval, computeSharedSecret]

-- A mismatched modulus must reject every result for either function.
example (f : FunId) (p : ℕ) (hp : p ≠ params.p) (message : ZMod params.p)
    (privateExp : ℕ) (v : params.Val) :
    ¬ funEval params f [.nat p, .zMod message, .nat privateExp] v := by
  cases f <;> exact fun h => hp h.1

end CslibTests.DiffieHellman
