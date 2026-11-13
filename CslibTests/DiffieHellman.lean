/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Cslib.Algorithms.StatefulProcesses.DiffieHellman.Basic

namespace CslibTests.DiffieHellman

open Cslib Cslib.Mech Cslib.StatefulProcesses Cslib.Algorithms.StatefulProcesses.DiffieHellman

section Roles

variable {Pid : Type} {L : LocalSig} {SelLabel ProcName : Type} {p : ℕ}

local notation "Proc" => Process Pid L SelLabel ProcName

-- The labels in `net_completeTraces` are the actions of the role programs.
example (g : ZMod p) (peer : Pid) (a : L.Var ℕ) (y key : L.Var (ZMod p)) :
    (aliceProc peer g a y key : Proc) =
      .pre (.sendValue peer `(MechExpr| {g ^ $a})) (aliceProc₁ peer a y key) := rfl

example (peer : Pid) (a : L.Var ℕ) (y key : L.Var (ZMod p)) :
    (aliceProc₁ peer a y key : Proc) = .pre (.recvValue peer y) (aliceProc₂ a y key) := rfl

example (a : L.Var ℕ) (y key : L.Var (ZMod p)) :
    (aliceProc₂ a y key : Proc) = .pre (.assign key `(MechExpr| {$y ^ $a})) 0 := rfl

example (g : ZMod p) (peer : Pid) (b : L.Var ℕ) (x key : L.Var (ZMod p)) :
    (bobProc peer g b x key : Proc) = .pre (.recvValue peer x) (bobProc₁ peer g b x key) := rfl

example (g : ZMod p) (peer : Pid) (b : L.Var ℕ) (x key : L.Var (ZMod p)) :
    (bobProc₁ peer g b x key : Proc) =
      .pre (.sendValue peer `(MechExpr| {g ^ $b})) (bobProc₂ b x key) := rfl

example (b : L.Var ℕ) (x key : L.Var (ZMod p)) :
    (bobProc₂ b x key : Proc) = .pre (.assign key `(MechExpr| {$x ^ $b})) 0 := rfl

-- The roles can be used inside larger processes that use selections.
example (g : ZMod p) (peer : Pid) (a : L.Var ℕ) (y key : L.Var (ZMod p)) :
    Process Pid L Bool PEmpty :=
  .recvLabel peer [(true, aliceProc peer g a y key), (false, 0)]

-- Evaluating a public value `{g ^ $e}`.
theorem eval_publicValue (σ : L.Store) (g : ZMod p) (e : L.Var ℕ) (n : ℕ) (hn : σ[e] = n) :
    LocalSig.Expr.Eval σ `(MechExpr| {g ^ $e}) (g ^ n) :=
  .call (.var e) (by rw [hn])

-- Evaluating a key computation `{$u ^ $e}`.
theorem eval_key (σ : L.Store) (u : L.Var (ZMod p)) (e : L.Var ℕ) (v : ZMod p) (n : ℕ)
    (hv : σ[u] = v) (hn : σ[e] = n) :
    LocalSig.Expr.Eval σ `(MechExpr| {$u ^ $e}) (v ^ n) :=
  .call (.pair (.call (.var u) rfl) (.var e)) (by rw [hv, hn])

end Roles

section Protocol

variable {Pid : Type} [DecidableEq Pid] {S : Sig Pid} {SelLabel ProcName : Type} {p : ℕ}

-- Every initial store admits a complete run with the expected key at both participants.
theorem complete_run (g : ZMod p) (alice bob : Pid) (hne : alice ≠ bob)
    (a : S.Var alice ℕ) (y aliceKey : S.Var alice (ZMod p))
    (b : S.Var bob ℕ) (x bobKey : S.Var bob (ZMod p))
    (hya : y.name ≠ a.name) (hxb : x.name ≠ b.name) (gs : S.Store) (a₀ b₀ : ℕ)
    (ha : (gs alice)[a] = a₀) (hb : (gs bob)[b] = b₀) :
    ∃ gs' μs, μs.length = 4 ∧
      (Cfg.lts (SelLabel := SelLabel) (ProcName := ProcName)).MTr
        ⟨net g alice bob a y aliceKey b x bobKey, gs⟩ μs ⟨0, gs'⟩ ∧
      (gs' alice)[aliceKey] = g ^ (a₀ * b₀) ∧ (gs' bob)[bobKey] = g ^ (a₀ * b₀) := by
  let aliceMsg := g ^ a₀
  let bobMsg := g ^ b₀
  let key := g ^ (a₀ * b₀)
  let cfg₁ : Cfg Pid S SelLabel ProcName := Cfg.mk
    (Function.update (Function.update (net g alice bob a y aliceKey b x bobKey)
      alice (aliceProc₁ bob a y aliceKey)) bob (bobProc₁ alice g b x bobKey))
    gs[⟨bob, x⟩ := aliceMsg]
  let cfg₂ : Cfg Pid S SelLabel ProcName := Cfg.mk
    (Function.update (Function.update cfg₁.net bob (bobProc₂ b x bobKey))
      alice (aliceProc₂ a y aliceKey))
    cfg₁.store[⟨alice, y⟩ := bobMsg]
  let cfg₃ : Cfg Pid S SelLabel ProcName := Cfg.mk (Function.update cfg₂.net alice 0)
    cfg₂.store[⟨alice, aliceKey⟩ := key]
  refine ⟨cfg₃.store[⟨bob, bobKey⟩ := key],
    [.com alice bob aliceMsg, .com bob alice bobMsg, .local alice, .local bob],
    rfl,
    .stepL (s2 := cfg₁) ?_ (.stepL (s2 := cfg₂) ?_ (.stepL (s2 := cfg₃) ?_ (.single _ ?_))),
    ?_, ?_⟩
  · refine Cfg.Tr.com (x := x) (e := `(MechExpr| {g ^ $a})) ?_
      (eval_publicValue _ g a _ ha) rfl
    refine Network.Tr.com ?_ ?_ rfl
    · simp only [net, Function.update_of_ne hne, Function.update_self]
      exact .pre
    · simp only [net, Function.update_self]
      exact .pre
  · refine Cfg.Tr.com (x := y) (e := `(MechExpr| {g ^ $b})) (v := bobMsg) ?_ ?_ rfl
    · refine Network.Tr.com ?_ ?_ rfl
      · simp only [cfg₁, Function.update_self]
        exact .pre
      · simp only [cfg₁, Function.update_of_ne hne, Function.update_self]
        exact .pre
    · refine eval_publicValue _ g b _ ?_
      simp [cfg₁, LocalSig.Store.getElem_subst_of_ne _ _ _ _ hxb.symm, hb]
  · refine Cfg.Tr.assign (x := aliceKey) (e := `(MechExpr| {$y ^ $a})) (v := key) ?_ ?_ rfl
    · refine Network.Tr.local rfl ?_ rfl
      simp only [cfg₂, Function.update_self]
      exact .pre
    · have := eval_key (cfg₂.store alice) y a bobMsg a₀
        (by simp [cfg₂])
        (by simp [cfg₂, cfg₁, Sig.Store.subst_eq_update,
          LocalSig.Store.getElem_subst_of_ne _ _ _ _ hya.symm, hne, ha])
      rwa [show bobMsg ^ a₀ = key by simp [bobMsg, key, ← pow_mul, Nat.mul_comm]] at this
  · refine Cfg.Tr.assign (x := bobKey) (e := `(MechExpr| {$x ^ $b})) (v := key) ?_ ?_ rfl
    · apply Network.Tr.local (prP := 0) rfl
      · simp only [cfg₃, cfg₂, Function.update_of_ne (Ne.symm hne), Function.update_self]
        exact .pre
      · funext q
        by_cases hqa : q = alice
        · subst hqa
          simp [cfg₃, Function.update_of_ne hne]
        · by_cases hqb : q = bob
          · subst hqb
            simp [cfg₃]
          · simp [cfg₃, cfg₂, cfg₁, net, Function.update_of_ne hqa, Function.update_of_ne hqb]
    · have := eval_key (cfg₃.store bob) x b aliceMsg b₀
        (by simp [cfg₃, cfg₂, cfg₁, Sig.Store.subst_eq_update, Ne.symm hne])
        (by simp [cfg₃, cfg₂, cfg₁, Sig.Store.subst_eq_update,
          LocalSig.Store.getElem_subst_of_ne _ _ _ _ hxb.symm, Ne.symm hne, hb])
      rwa [show aliceMsg ^ b₀ = key by simp [aliceMsg, key, ← pow_mul]] at this
  · simp [cfg₃, Sig.Store.subst_eq_update, hne, key]
  · simp [key]

end Protocol

section Choice

variable {Pid : Type} [DecidableEq Pid] {S : Sig Pid} {SelLabel ProcName : Type} {p : ℕ}

/-- Any exponent in `(0, p)`. A compiler can bind this relation to a random number generator. -/
def randomExponent (p : ℕ) : Unit → ℕ → Prop := fun _ n => 0 < n ∧ n < p

/-- Alice chooses her private exponent nondeterministically, then runs her role. -/
def aliceChoosing {L : LocalSig} (g : ZMod p) (bob : Pid) (a : L.Var ℕ)
    (peerPub key : L.Var (ZMod p)) : Process Pid L SelLabel ProcName :=
  .pre `(SPpre| a ≔ LocalSig.Expr.call (randomExponent p) (.val ())) (aliceProc bob g a peerPub key)

/-- For every choice of Alice's exponent, the protocol completes with the expected keys. -/
theorem complete_run_choosing (g : ZMod p) (alice bob : Pid) (hne : alice ≠ bob)
    (a : S.Var alice ℕ) (y aliceKey : S.Var alice (ZMod p))
    (b : S.Var bob ℕ) (x bobKey : S.Var bob (ZMod p))
    (hya : y.name ≠ a.name) (hxb : x.name ≠ b.name) (gs : S.Store) (b₀ : ℕ)
    (hb : (gs bob)[b] = b₀) (n : ℕ) (hn : randomExponent p () n) :
    ∃ gs' μs, μs.length = 5 ∧
      (Cfg.lts (SelLabel := SelLabel) (ProcName := ProcName)).MTr
        ⟨Function.update (net g alice bob a y aliceKey b x bobKey) alice
          (aliceChoosing g bob a y aliceKey), gs⟩ μs ⟨0, gs'⟩ ∧
      (gs' alice)[aliceKey] = g ^ (n * b₀) ∧ (gs' bob)[bobKey] = g ^ (n * b₀) := by
  obtain ⟨gs', μs, hlen, hrun, haliceKey, hbobKey⟩ :=
    complete_run (SelLabel := SelLabel) (ProcName := ProcName) g alice bob hne a y aliceKey b x
      bobKey hya hxb gs[⟨alice, a⟩ := n] n b₀ (by simp)
      (by rw [Sig.Store.subst_apply_of_ne _ _ _ _ _ (Ne.symm hne)]; exact hb)
  refine ⟨gs', .local alice :: μs, by simp [hlen], .stepL ?_ hrun, haliceKey, hbobKey⟩
  refine Cfg.Tr.assign (x := a) (e := .call (randomExponent p) (.val ())) (v := n) ?_
    (.call (.val ()) hn) rfl
  refine Network.Tr.local (prP := aliceProc bob g a y aliceKey) rfl ?_ ?_
  · simp only [Function.update_self]
    exact .pre
  · funext q
    by_cases hq : q = alice
    · subst hq
      simp [net, Function.update_of_ne hne]
    · simp [hq]

end Choice

end CslibTests.DiffieHellman

namespace CslibTests.DiffieHellman.Canonical

open Cslib Cslib.Mech Cslib.StatefulProcesses Cslib.Algorithms.StatefulProcesses.DiffieHellman

/-! Alice (`true`) and Bob (`false`) have separate local signatures. -/

inductive AliceName | exp | peerPub | key deriving DecidableEq

inductive BobName | exp | peerPub | key | log deriving DecidableEq

abbrev aliceSig : LocalSig where
  VarName := AliceName
  VarType
    | .exp => ℕ
    | .peerPub | .key => ZMod 7

-- Bob has an additional variable, which Alice does not have.
abbrev bobSig : LocalSig where
  VarName := BobName
  VarType
    | .exp => ℕ
    | .peerPub | .key => ZMod 7
    | .log => String

abbrev sig : Sig Bool
  | true => aliceSig
  | false => bobSig

def a : sig.Var true ℕ := ⟨.exp, rfl⟩
def y : sig.Var true (ZMod 7) := ⟨.peerPub, rfl⟩
def aliceKey : sig.Var true (ZMod 7) := ⟨.key, rfl⟩
def b : sig.Var false ℕ := ⟨.exp, rfl⟩
def x : sig.Var false (ZMod 7) := ⟨.peerPub, rfl⟩
def bobKey : sig.Var false (ZMod 7) := ⟨.key, rfl⟩

def g : ZMod 7 := 3

/-- Alice holds the exponent 2 and Bob holds the exponent 3. -/
def initial : sig.Store
  | true, .exp => (2 : ℕ)
  | true, .peerPub | true, .key => (0 : ZMod 7)
  | false, .exp => (3 : ℕ)
  | false, .peerPub | false, .key => (0 : ZMod 7)
  | false, .log => ""

-- Alice and Bob run the protocol with different local signatures.
example : ∃ gs' μs, μs.length = 4 ∧
    (Cfg.lts (S := sig) (SelLabel := Empty) (ProcName := Empty)).MTr
      ⟨net g true false a y aliceKey b x bobKey, initial⟩ μs ⟨0, gs'⟩ ∧
    (gs' true)[aliceKey] = g ^ (2 * 3) ∧ (gs' false)[bobKey] = g ^ (2 * 3) :=
  complete_run g true false (by decide) a y aliceKey b x bobKey (by decide) (by decide) initial
    2 3 rfl rfl

-- Variables of provably different types cannot alias.
example : y.name ≠ a.name := LocalSig.Var.name_ne_of_type_ne (fun h => by
  have : Finite ℕ := h ▸ (inferInstance : Finite (ZMod 7))
  exact not_finite ℕ) y a

end CslibTests.DiffieHellman.Canonical
