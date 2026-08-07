/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Cslib.Languages.StatefulProcesses.Network

/-!
# Diffie-Hellman Key Exchange in Stateful Processes

This module formalises the Diffie-Hellman key exchange protocol in `StatefulProcesses`.

## Implementation notes

The current implementation requires proofs that `p` is prime and that `g` is a primitive root modulo
`p`, but does not use these facts. They are reserved for future work on security results.
-/

@[expose] public section

namespace Cslib.Algorithms.StatefulProcesses.DiffieHellman

open Cslib.StatefulProcesses Cslib.Mech

/-! ## Basics -/

/-- Parameters of the DH protocol. -/
structure Params (Pid Var : Type*) where
  /-- Alice. -/
  alice : Pid
  /-- Bob. -/
  bob : Pid
  /-- Alice and Bob have different names. -/
  alice_neq_bob : alice ≠ bob
  /-- Alice's private key (secret). -/
  a : ℕ
  /-- Bob's private key (secret). -/
  b : ℕ
  /-- Bob's variable to store Alice's message. -/
  x : Var
  /-- Alice's variable to store Bob's message. -/
  y : Var
  /-- The variable used to store the shared key. -/
  s : Var
  /-- The prime modulus `p`. -/
  p : ℕ
  /-- `p` is prime. -/
  p_prime : Nat.Prime p
  /-- The generator `g`. -/
  g : ZMod p
  /-- `g` is a primitive root modulo `p`. -/
  g_primitive_root_p : IsPrimitiveRoot g (p - 1)
  /-- SelLabel type for instantiating stateful processes. -/
  SelLabel : Type*
  /-- ProcName type for instantiating stateful processes. -/
  ProcName : Type*

attribute [local grind .] Params.alice_neq_bob

/-- Computes the public DH message from a private exponent. -/
def computePublicMessage (p : ℕ) (g : ZMod p) (privateExp : ℕ) : ZMod p :=
  g ^ privateExp

/-- Computes the shared secret key from a private exponent and the other party's public message. -/
def computeSharedSecret (p : ℕ) (msg : ZMod p) (privateExp : ℕ) : ZMod p :=
  msg ^ privateExp

/-- Correctness of the DH computations: the encryption keys independently computed by the two
participants are the same. -/
theorem computePublicMessage_computeSharedSecret_eq (p : ℕ) (g : ZMod p) (a b : ℕ) :
    computeSharedSecret p (computePublicMessage p g b) a =
    computeSharedSecret p (computePublicMessage p g a) b := by
  simp only [computePublicMessage, computeSharedSecret]
  rw [← pow_mul, mul_comm, pow_mul]

/-! ## Behaviour -/

variable {Pid Var : Type*} (params : Params Pid Var)

/-- Function identifiers used in DH. -/
inductive FunId | computePublicMessage | computeSharedSecret

/-- Value type for DH. -/
inductive Params.Val | nat (n : ℕ) | zMod (z : ZMod params.p)

/-- Alice's expression for computing the public message. -/
abbrev aliceComputeMesg : Expr Var params.Val FunId :=
  Expr.call .computePublicMessage
    [.val <| .nat params.p, .val <| .zMod params.g, .val <| .nat params.b]

/-- Alice's expression for computing the shared secret. -/
abbrev aliceComputeSharedSecret : Expr Var params.Val FunId :=
  Expr.call .computeSharedSecret [params.y, .val <| .nat params.a]

/-- Bob's expression for computing the public message. -/
abbrev bobComputeMesg : Expr Var params.Val FunId :=
  Expr.call .computePublicMessage
    [.val <| .nat params.p, .val <| .zMod params.g, .val <| .nat params.b]

/-- Bob's expression for computing the shared secret. -/
abbrev bobComputeSharedSecret : Expr Var params.Val FunId :=
  Expr.call .computeSharedSecret [params.x, .val <| .nat params.a]

/-- Alice's program. -/
def alice : Process Pid Var params.Val FunId params.SelLabel params.ProcName :=
  `(SP| params.bob ! aliceComputeMesg params;
        params.bob ? params.y;
        params.s ≔ aliceComputeSharedSecret params;
        0)

/-- Bob's program. -/
def bob : Process Pid Var params.Val FunId params.SelLabel params.ProcName :=
  `(SP| params.alice ? params.x;
        params.alice ! bobComputeMesg params;
        params.s ≔ bobComputeSharedSecret params;
        0)

/-! ## Semantics -/

/-- Implementation of local function call evaluation. -/
def funEval : FunCallEval FunId params.Val
  | .computePublicMessage, [.nat p, .zMod g, .nat privateExp], v =>
    (h : p = params.p) → v = (.zMod <| h ▸ computePublicMessage p (h ▸ g) privateExp)
  | .computeSharedSecret, [.nat p, .zMod msg, .nat privateExp], v =>
    (h : p = params.p) → v = (.zMod <| h ▸ computeSharedSecret p (h ▸ msg) privateExp)
  | _, _, _ => False

/-- DH network. -/
def net [DecidableEq Pid] : Network Pid Var params.Val FunId params.SelLabel params.ProcName :=
  fun p : Pid =>
    if p = params.alice then alice params
    else if p = params.bob then bob params
    else 0

variable [DecidableEq Pid] [DecidableEq Var]

def _root_.Cslib.LTS.TrUnique (lts : LTS State Label) (s₁ : State) (μ : Label) (s₂ : State) :=
  lts.Tr s₁ μ s₂ ∧ ∀ μ' s₃, lts.Tr s₁ μ' s₃ → μ' = μ ∧ s₃ = s₂
  -- DeterministicStateLabel htr?

/-- Alice's program after one step. -/
@[local grind =]
def alice₁ : Process Pid Var params.Val FunId params.SelLabel params.ProcName :=
  `(SP| params.bob ? params.y; params.s ≔ aliceComputeSharedSecret params; 0)

/-- Alice's program after two steps. -/
@[local grind =]
def alice₂ : Process Pid Var params.Val FunId params.SelLabel params.ProcName :=
  `(SP| params.s ≔ aliceComputeSharedSecret params; 0)

/-- Bob's program after one step. -/
@[local grind =]
def bob₁ : Process Pid Var params.Val FunId params.SelLabel params.ProcName :=
  `(SP| params.alice ! bobComputeMesg params; params.s ≔ bobComputeSharedSecret params; 0)

/-- Bob's program after two steps. -/
@[local grind =]
def bob₂ : Process Pid Var params.Val FunId params.SelLabel params.ProcName :=
  `(SP| params.s ≔ bobComputeSharedSecret params; 0)

lemma net_uniqueTr₁ :
    Network.lts.TrUnique
      (net params) (.com params.alice (aliceComputeMesg params) params.bob params.x)
      (net params)[params.alice := alice₁ params][params.bob := bob₁ params] := by
  apply And.intro
  case left =>
    constructor
    case hsend =>
      simp only [net, alice]
      constructor
    case hrecv =>
      simp only [net, alice]
      split
      case isTrue => grind
      case isFalse => apply Process.Tr.pre
    case hn' =>
      grind
  case right =>
    intro μ s₃
    sorry

/-- Characterisation of the complete symbolic traces of DH. -/
theorem net_completeTraces :
    LTS.completeTraces (Network.lts (SelLabel := params.SelLabel) (ProcName := params.ProcName)) (net params) = fun μs =>
    μs = [
      Network.TrLabel.com params.alice (aliceComputeMesg params) params.bob params.x,
      .com params.bob (bobComputeMesg params) params.alice params.y,
      .local params.alice (.assign params.s <| aliceComputeSharedSecret params),
      .local params.bob (.assign params.s <| bobComputeSharedSecret params)
    ] ∨ μs = [
      .com params.alice (aliceComputeMesg params) params.bob params.x,
      .com params.bob (bobComputeMesg params) params.alice params.y,
      .local params.bob (.assign params.s <| bobComputeSharedSecret params),
      .local params.alice (.assign params.s <| aliceComputeSharedSecret params),
    ] := by
  ext μs
  apply Iff.intro <;> intro h
  case mp =>
    rcases h with ⟨net', hnet', hmtr⟩

    sorry
  sorry

abbrev Params.cfgLts {SelLabel ProcName : Type*} :=
  Cfg.lts (Pid := Pid) (Var := Var) (SelLabel := SelLabel) (ProcName := ProcName)
    (fun _ => False) (funEval params)

/-- Functional correctness for `net`. -/
theorem net_correct
    (hmtr : params.cfgLts.Tr
      ⟨net params, gs⟩ μs ⟨0, gs'⟩) :
    (gs' params.alice) params.s = (gs' params.bob) params.s  := by
  sorry

end Cslib.Algorithms.StatefulProcesses.DiffieHellman
