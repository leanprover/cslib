/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Cslib.Algorithms.StatefulProcesses.DiffieHellman.Basic

namespace CslibTests.DiffieHellman

open Cslib Cslib.Mech Cslib.StatefulProcesses Cslib.Algorithms.StatefulProcesses.DiffieHellman

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

-- A complete execution exists from every initial store and produces the expected key.
theorem complete_run [DecidableEq Pid] [DecidableEq Var]
    (gs : GlobalStore Pid Var params.Val) :
    ∃ gs' μs, μs.length = 4 ∧ params.cfgLts.MTr ⟨net params, gs⟩ μs ⟨0, gs'⟩ ∧
      (gs' params.alice) params.s = .zMod (params.g ^ (params.a * params.b)) ∧
      (gs' params.bob) params.s = .zMod (params.g ^ (params.a * params.b)) := by
  let aliceMsg : params.Val := .zMod (params.g ^ params.a)
  let bobMsg : params.Val := .zMod (params.g ^ params.b)
  let key : params.Val := .zMod (params.g ^ (params.a * params.b))
  let cfg₁ := Cfg.mk ((net params)[params.alice := alice₁ params][params.bob := bob₁ params])
    (gs[(params.bob, params.x) := aliceMsg])
  let cfg₂ := Cfg.mk (cfg₁.net[params.bob := bob₂ params][params.alice := alice₂ params])
    (cfg₁.store[(params.alice, params.y) := bobMsg])
  let cfg₃ := Cfg.mk (Function.update cfg₂.net params.alice 0)
    (cfg₂.store[(params.alice, params.s) := key])
  refine ⟨cfg₃.store[(params.bob, params.s) := key],
    [.com params.alice params.bob aliceMsg, .com params.bob params.alice bobMsg,
      .local params.alice, .local params.bob], rfl,
    .stepL (s2 := cfg₁) ?_ (.stepL (s2 := cfg₂) ?_ (.stepL (s2 := cfg₃) ?_ (.single _ ?_))),
    ?_, ?_⟩
  · apply Cfg.Tr.com (e := aliceComputeMesg params) (hstore := rfl)
    · refine Network.Tr.com ?_ ?_ rfl
      · simp only [net, HasSubstitution.subst, Function.update_of_ne params.alice_neq_bob,
          Function.update_self]
        exact .pre
      · simp only [net, HasSubstitution.subst, Function.update_self]
        exact .pre
    · exact .call (.cons .val (.cons .val (.cons .val .nil))) ⟨rfl, rfl⟩
  · apply Cfg.Tr.com (e := bobComputeMesg params) (hstore := rfl)
    · refine Network.Tr.com ?_ ?_ rfl
      · simp only [cfg₁, HasSubstitution.subst, Function.update_self]
        exact .pre
      · simp only [cfg₁, HasSubstitution.subst, Function.update_of_ne params.alice_neq_bob,
          Function.update_self]
        exact .pre
    · exact .call (.cons .val (.cons .val (.cons .val .nil))) ⟨rfl, rfl⟩
  · apply Cfg.Tr.assign (x := params.s) (e := aliceComputeSharedSecret params) (hstore := rfl)
    · refine Network.Tr.local rfl ?_ rfl
      simp only [cfg₂, HasSubstitution.subst, Function.update_self]
      exact .pre
    · apply FunCallEval.EvalExpr.call (.cons .val (.cons .var (.cons .val .nil)))
      simp [cfg₂, HasSubstitution.subst, key, bobMsg, funEval, computeSharedSecret,
        ← pow_mul, Nat.mul_comm]
  · apply Cfg.Tr.assign (x := params.s) (e := bobComputeSharedSecret params) (hstore := rfl)
    · apply Network.Tr.local (prP := 0) rfl
      · simp only [cfg₃, cfg₂, HasSubstitution.subst,
          Function.update_of_ne (Ne.symm params.alice_neq_bob), Function.update_self]
        exact .pre
      · ext p
        simp +contextual [cfg₃, cfg₂, cfg₁, net, HasSubstitution.subst, Function.update_apply]
    · apply FunCallEval.EvalExpr.call (.cons .val (.cons .var (.cons .val .nil)))
      simp [cfg₃, cfg₂, cfg₁, HasSubstitution.subst, key, aliceMsg, funEval, computeSharedSecret,
        ← pow_mul, Ne.symm params.alice_neq_bob]
  · simp [cfg₃, HasSubstitution.subst, params.alice_neq_bob, key]
  · simp [HasSubstitution.subst, key]

end CslibTests.DiffieHellman
