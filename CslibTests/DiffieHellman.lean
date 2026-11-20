/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Cslib.Algorithms.StatefulProcesses.DiffieHellman.Basic

namespace CslibTests.DiffieHellman

open Cslib Cslib.Mech Cslib.StatefulProcesses Cslib.Algorithms.StatefulProcesses.DiffieHellman

variable {Pid SelLabel ProcName : Type} [DecidableEq Pid] {S : Sig Pid} {L : LocalSig} {p : ℕ}

-- Each role uses its own exponent in its public message `{g ^ $e}`.
theorem eval_publicValue (σ : L.Store) (g : ZMod p) (e : L.Var ℕ) (n : ℕ) (hn : σ[e] = n) :
    LocalSig.Expr.Eval σ `(MechExpr| {g ^ $e}) (g ^ n) :=
  .call (.var e) (by rw [hn])

-- Each role also uses its own exponent on the received message, in `{$u ^ $e}`.
theorem eval_key (σ : L.Store) (u : L.Var (ZMod p)) (e : L.Var ℕ) (v : ZMod p) (n : ℕ)
    (hv : σ[u] = v) (hn : σ[e] = n) :
    LocalSig.Expr.Eval σ `(MechExpr| {$u ^ $e}) (v ^ n) :=
  .call (.pair (.call (.var u) rfl) (.var e)) (by rw [hv, hn])

-- A complete execution exists from every initial store and produces the expected key.
theorem complete_run (g : ZMod p) (alice bob : Pid) (hne : alice ≠ bob)
    (a : S.Var alice ℕ) (y aliceKey : S.Var alice (ZMod p))
    (b : S.Var bob ℕ) (x bobKey : S.Var bob (ZMod p))
    (hya : y.name ≠ a.name) (hxb : x.name ≠ b.name) (gs : S.Store) (a₀ b₀ : ℕ)
    (ha : (gs alice)[a] = a₀) (hb : (gs bob)[b] = b₀) :
    ∃ gs' μs, μs.length = 4 ∧
      (Cfg.lts (SelLabel := SelLabel) (ProcName := ProcName)).MTr
        ⟨net g alice bob a y aliceKey b x bobKey, gs⟩ μs ⟨0, gs'⟩ ∧
      (gs' alice)[aliceKey] = g ^ (a₀ * b₀) ∧ (gs' bob)[bobKey] = g ^ (a₀ * b₀) := by
  -- The configurations after each of the first three steps.
  let cfg₁ : Cfg Pid S SelLabel ProcName := ⟨Function.update (Function.update
    (net g alice bob a y aliceKey b x bobKey) alice (aliceProc₁ bob a y aliceKey)) bob
    (bobProc₁ alice g b x bobKey), gs[⟨bob, x⟩ := g ^ a₀]⟩
  let cfg₂ : Cfg Pid S SelLabel ProcName := ⟨Function.update (Function.update cfg₁.net
    bob (bobProc₂ b x bobKey)) alice (aliceProc₂ a y aliceKey), cfg₁.store[⟨alice, y⟩ := g ^ b₀]⟩
  let cfg₃ : Cfg Pid S SelLabel ProcName :=
    ⟨Function.update cfg₂.net alice 0, cfg₂.store[⟨alice, aliceKey⟩ := (g ^ b₀) ^ a₀]⟩
  -- The run: Alice sends `g ^ a` to Bob, Bob sends `g ^ b` to Alice, then both compute the key.
  -- The remaining goals are named after the step that they belong to.
  refine ⟨cfg₃.store[⟨bob, bobKey⟩ := (g ^ a₀) ^ b₀],
    [.com alice bob (g ^ a₀), .com bob alice (g ^ b₀), .local alice, .local bob], rfl,
    .stepL (s2 := cfg₁)
      (.com (x := x) (.com ?send₁ ?recv₁ rfl) (eval_publicValue _ g a a₀ ha) rfl) <|
    .stepL (s2 := cfg₂)
      (.com (x := y) (.com ?send₂ ?recv₂ rfl) (eval_publicValue _ g b b₀ ?read₂) rfl) <|
    .stepL (s2 := cfg₃)
      (.assign (x := aliceKey) (.local rfl ?assign₃ rfl)
        (eval_key _ y a _ a₀ ?read₃ ?read₃') rfl) <|
    .single _
      (.assign (x := bobKey) (.local (prP := 0) rfl ?assign₄ ?done)
        (eval_key _ x b _ b₀ ?read₄ ?read₄') rfl),
    ?aliceKey, ?bobKey⟩
  -- Each participant is ready to perform the action of its step.
  case send₁ | recv₁ | send₂ | recv₂ | assign₃ | assign₄ =>
    simp only [cfg₃, cfg₂, cfg₁, net, ne_eq, hne, Ne.symm hne, not_false_eq_true,
      Function.update_self, Function.update_of_ne, Function.update_idem]
    exact .pre
  -- The variables read in each step hold the expected values.
  case read₂ | read₃ | read₃' | read₄ | read₄' => grind
  -- Both keys are `g ^ (a₀ * b₀)`.
  case aliceKey | bobKey => grind [pow_mul, Nat.mul_comm]
  -- After the last step, every process has terminated.
  case done =>
    funext q
    by_cases hqa : q = alice <;> by_cases hqb : q = bob <;> subst_vars <;>
      simp_all [cfg₃, cfg₂, cfg₁, net]

end CslibTests.DiffieHellman
