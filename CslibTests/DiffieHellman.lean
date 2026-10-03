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
  let n₁ : Network Pid Var params.Val FunId params.SelLabel params.ProcName :=
    0[params.alice := alice₁ params][params.bob := bob₁ params]
  let n₂ : Network Pid Var params.Val FunId params.SelLabel params.ProcName :=
    0[params.alice := alice₂ params][params.bob := bob₂ params]
  let n₃ : Network Pid Var params.Val FunId params.SelLabel params.ProcName :=
    0[params.bob := bob₂ params]
  let aliceMsg : params.Val := .zMod (params.g ^ params.a)
  let bobMsg : params.Val := .zMod (params.g ^ params.b)
  let key : params.Val := .zMod (params.g ^ (params.a * params.b))
  let gs₁ := gs[(params.bob, params.x) := aliceMsg]
  let gs₂ := gs₁[(params.alice, params.y) := bobMsg]
  let gs₃ := gs₂[(params.alice, params.s) := key]
  let gs₄ := gs₃[(params.bob, params.s) := key]
  have h₁ : params.cfgLts.Tr ⟨net params, gs⟩
      (.com params.alice params.bob (.zMod (params.g ^ params.a))) ⟨n₁, gs₁⟩ := by
    apply Cfg.Tr.com (e := aliceComputeMesg params) (hstore := rfl)
    · apply Network.Tr.com (prP := alice₁ params) (prQ := bob₁ params)
      · simp only [net, HasSubstitution.subst, Function.update_of_ne params.alice_neq_bob,
          Function.update_self]
        exact .pre
      · simp only [net, HasSubstitution.subst, Function.update_self]
        exact .pre
      · ext p
        simp only [n₁, net, HasSubstitution.subst]
        grind
    · exact .call (.cons .val (.cons .val (.cons .val .nil))) ⟨rfl, rfl⟩
  have h₂ : params.cfgLts.Tr ⟨n₁, gs₁⟩
      (.com params.bob params.alice (.zMod (params.g ^ params.b))) ⟨n₂, gs₂⟩ := by
    apply Cfg.Tr.com (e := bobComputeMesg params) (hstore := rfl)
    · apply Network.Tr.com (prP := bob₂ params) (prQ := alice₂ params)
      · simp only [n₁, HasSubstitution.subst, Function.update_self]
        exact .pre
      · simp only [n₁, HasSubstitution.subst, Function.update_of_ne params.alice_neq_bob,
          Function.update_self]
        exact .pre
      · ext p
        simp only [n₂, n₁, HasSubstitution.subst]
        grind [params.alice_neq_bob]
    · exact .call (.cons .val (.cons .val (.cons .val .nil))) ⟨rfl, rfl⟩
  have h₃ : params.cfgLts.Tr ⟨n₂, gs₂⟩ (.local params.alice) ⟨n₃, gs₃⟩ := by
    apply Cfg.Tr.assign (x := params.s) (e := aliceComputeSharedSecret params) (hstore := rfl)
    · apply Network.Tr.local (prP := 0) rfl
      · simp only [n₂, HasSubstitution.subst, Function.update_of_ne params.alice_neq_bob,
          Function.update_self]
        exact .pre
      · ext p
        by_cases hp : p = params.alice
        · simp [n₃, n₂, HasSubstitution.subst, hp, params.alice_neq_bob]
        · by_cases hq : p = params.bob <;>
            simp [n₃, n₂, HasSubstitution.subst, hp, hq, Ne.symm params.alice_neq_bob]
    · apply FunCallEval.EvalExpr.call (.cons .val (.cons .var (.cons .val .nil)))
      simp [gs₂, HasSubstitution.subst, key, bobMsg, funEval, computeSharedSecret,
        ← pow_mul, Nat.mul_comm]
  have h₄ : params.cfgLts.Tr ⟨n₃, gs₃⟩ (.local params.bob) ⟨0, gs₄⟩ := by
    apply Cfg.Tr.assign (x := params.s) (e := bobComputeSharedSecret params) (hstore := rfl)
    · apply Network.Tr.local (prP := 0) rfl
      · simp only [n₃, HasSubstitution.subst, Function.update_self]
        exact .pre
      · ext p
        simp [n₃, HasSubstitution.subst]
    · apply FunCallEval.EvalExpr.call (.cons .val (.cons .var (.cons .val .nil)))
      simp [gs₃, gs₂, gs₁, HasSubstitution.subst, key, aliceMsg, funEval, computeSharedSecret,
        ← pow_mul, Ne.symm params.alice_neq_bob]
  refine ⟨gs₄, _, rfl, .stepL h₁ (.stepL h₂ (.stepL h₃ (.single _ h₄))), ?_, ?_⟩
  · simp [gs₄, gs₃, HasSubstitution.subst, params.alice_neq_bob, key]
  · simp [gs₄, HasSubstitution.subst, key]

end CslibTests.DiffieHellman
