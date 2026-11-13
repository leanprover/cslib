/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Mathlib.Data.ZMod.Basic
public import Cslib.Languages.StatefulProcesses.Network

/-!
# Diffie-Hellman Key Exchange in Stateful Processes (testbed)

This module formalises the Diffie-Hellman key exchange protocol in `StatefulProcesses`.

It is also intended as a simple testbed to measure improvement on how CSLib deals with embedded DSLs
like Stateful Processes and reasoning on operational semantics.

Current aspects that stand out and could be more ergonomic are:
1. The protocol has two obvious symbolic traces, yet proving `net_completeTraces` is cumbersome.
  Perhaps an API for unique transitions could be partially helpful:
```
def _root_.Cslib.LTS.TrUnique (lts : LTS State Label) (s : State) (μ : Label) (s' : State) :=
  lts.Tr s μ s' ∧ ∀ μ' s'', lts.Tr s μ' s'' → μ' = μ ∧ s'' = s'
```
  The terms for `aliceProc` and `bobProc` after one and two steps of their executions are provided
  as reference for this endeavour.
2. As a consequence of (1), proving `net_fun_correct` is cumbersome.

## Implementation notes

The public parameters are a generator `g : ZMod p`, with the modulus `p` left implicit. Each role
takes only what its participant knows: the public parameters, the identity of its peer, and handles
to its own local variables.

Private exponents are local variables rather than Lean constants, so they live in the
participants' stores and never occur in the process terms or in their transition labels. As a
consequence, correctness statements assume that, in each role, the variable receiving the peer's
public value differs from the exponent, which the reception would otherwise overwrite.

The exponents can also be chosen by the roles themselves with a relational call, such as one
returning any exponent in `(0, p)`; see the tests for this variant.

The key-agreement computation does not require primality or a primitive root; security properties
would require additional assumptions.
-/

@[expose] public section

namespace Cslib.Algorithms.StatefulProcesses.DiffieHellman

open Cslib.Mech Cslib.StatefulProcesses

/-! ## Basics -/

/-- The two participants compute the same shared key. -/
theorem shared_secret_eq (p : ℕ) (g : ZMod p) (a b : ℕ) :
    (g ^ b) ^ a = (g ^ a) ^ b := by
  rw [← pow_mul, ← pow_mul, Nat.mul_comm]

/-! ## Behaviour -/

variable {L : LocalSig}

/-- Alice's program, the initiator. It sends `g ^ a` to `bob`, receives Bob's public value in
`peerPub`, and stores the shared key in `key`. The private exponent `a` is a local variable. -/
def aliceProc (bob : Pid) (g : ZMod p) (a : L.Var ℕ) (peerPub key : L.Var (ZMod p)) :
    Process Pid L SelLabel ProcName :=
  `(SP| bob ! {g ^ $a};
        bob ? peerPub;
        key ≔ {$peerPub ^ $a};
        0)

/-- Bob's program, the responder. It receives Alice's public value in `peerPub`, sends `g ^ b` to
`alice`, and stores the shared key in `key`. The private exponent `b` is a local variable. -/
def bobProc (alice : Pid) (g : ZMod p) (b : L.Var ℕ) (peerPub key : L.Var (ZMod p)) :
    Process Pid L SelLabel ProcName :=
  `(SP| alice ? peerPub;
        alice ! {g ^ $b};
        key ≔ {$peerPub ^ $b};
        0)

/-- Alice's program after its first communication. -/
def aliceProc₁ (bob : Pid) (a : L.Var ℕ) (peerPub key : L.Var (ZMod p)) :
    Process Pid L SelLabel ProcName :=
  `(SP| bob ? peerPub; key ≔ {$peerPub ^ $a}; 0)

/-- Alice's program after both communications. -/
def aliceProc₂ (a : L.Var ℕ) (peerPub key : L.Var (ZMod p)) : Process Pid L SelLabel ProcName :=
  `(SP| key ≔ {$peerPub ^ $a}; 0)

/-- Bob's program after its first communication. -/
def bobProc₁ (alice : Pid) (g : ZMod p) (b : L.Var ℕ) (peerPub key : L.Var (ZMod p)) :
    Process Pid L SelLabel ProcName :=
  `(SP| alice ! {g ^ $b}; key ≔ {$peerPub ^ $b}; 0)

/-- Bob's program after both communications. -/
def bobProc₂ (b : L.Var ℕ) (peerPub key : L.Var (ZMod p)) : Process Pid L SelLabel ProcName :=
  `(SP| key ≔ {$peerPub ^ $b}; 0)

/-! ## The protocol -/

variable [DecidableEq Pid] {S : Sig Pid}

/-- The protocol between Alice (`alice`) and Bob (`bob`), whose local signatures are `S alice` and
`S bob`. Alice's private exponent is in `a`, she receives Bob's public value in `y`, and she stores
the key in `aliceKey`. Bob's private exponent is in `b`, he receives Alice's public value in `x`,
and he stores the key in `bobKey`. -/
def net (g : ZMod p) (alice bob : Pid) (a : S.Var alice ℕ) (y aliceKey : S.Var alice (ZMod p))
    (b : S.Var bob ℕ) (x bobKey : S.Var bob (ZMod p)) : Network Pid S SelLabel ProcName :=
  Function.update (Function.update 0 alice (aliceProc bob g a y aliceKey)) bob
    (bobProc alice g b x bobKey)

/- Characterisation of the complete symbolic traces of DH. -/
proof_wanted net_completeTraces (g : ZMod p) (alice bob : Pid) (hne : alice ≠ bob)
    (a : S.Var alice ℕ) (y aliceKey : S.Var alice (ZMod p))
    (b : S.Var bob ℕ) (x bobKey : S.Var bob (ZMod p)) :
  (Network.lts (SelLabel := SelLabel) (ProcName := ProcName)).completeTraces
    (net g alice bob a y aliceKey b x bobKey) = {μs |
  μs = [
    Network.TrLabel.com alice `(MechExpr| {g ^ $a}) bob x,
    .com bob `(MechExpr| {g ^ $b}) alice y,
    .local alice (.assign aliceKey `(MechExpr| {$y ^ $a})),
    .local bob (.assign bobKey `(MechExpr| {$x ^ $b}))
  ] ∨ μs = [
    .com alice `(MechExpr| {g ^ $a}) bob x,
    .com bob `(MechExpr| {g ^ $b}) alice y,
    .local bob (.assign bobKey `(MechExpr| {$x ^ $b})),
    .local alice (.assign aliceKey `(MechExpr| {$y ^ $a}))
  ]}

/- Functional correctness over complete executions, for any initial values of the exponents. -/
proof_wanted net_fun_correct (g : ZMod p) (alice bob : Pid)
    (a : S.Var alice ℕ) (y aliceKey : S.Var alice (ZMod p))
    (b : S.Var bob ℕ) (x bobKey : S.Var bob (ZMod p))
    (hya : y.name ≠ a.name) (hxb : x.name ≠ b.name)
    {gs gs' : S.Store} {μs : List (Cfg.TrLabel Pid SelLabel)}
    (hmtr : (Cfg.lts (SelLabel := SelLabel) (ProcName := ProcName)).MTr
      ⟨net g alice bob a y aliceKey b x bobKey, gs⟩ μs ⟨0, gs'⟩) :
    (gs' alice)[aliceKey] = (gs' bob)[bobKey]

end Cslib.Algorithms.StatefulProcesses.DiffieHellman
