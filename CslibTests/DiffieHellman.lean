/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Cslib.Algorithms.StatefulProcesses.DiffieHellman.Basic

namespace CslibTests.DiffieHellman

open Cslib.Mech Cslib.Algorithms.StatefulProcesses.DiffieHellman

variable {Pid Var : Type*} (params : Params Pid Var)

-- Each final key computation can evaluate after receiving a field element.
example (σ : LocalStore Var params.Val) (message : ZMod params.p)
    (h : σ params.y = .zMod message) :
    ∃ key, (funEval params).EvalExpr σ (aliceComputeSharedSecret params) (.zMod key) := by
  refine ⟨message ^ params.a, .call (.cons .val (.cons .var (.cons .val .nil))) ?_⟩
  simp only [h, funEval]
  intro hmod
  rfl

example (σ : LocalStore Var params.Val) (message : ZMod params.p)
    (h : σ params.x = .zMod message) :
    ∃ key, (funEval params).EvalExpr σ (bobComputeSharedSecret params) (.zMod key) := by
  refine ⟨message ^ params.a, .call (.cons .val (.cons .var (.cons .val .nil))) ?_⟩
  simp only [h, funEval]
  intro hmod
  rfl

end CslibTests.DiffieHellman
