/-
Copyright (c) 2026 Christiano Braga. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christiano Braga
-/

module

public import Mathlib.Tactic
public import Cslib.Systems.Distributed.Protocols.Cryptographic.KeyExchange.Basic

@[expose] public section

/-!
# Diffie-Hellman protocol

Diffie-Hellman key exchange as an instance of `KeyExchangeProtocol` in a finite cyclic
group `G` of cardinality `q` with a generator `g`. Two parties sample private keys
`α, β : ZMod q`, publish `g ^ α.val` and `g ^ β.val`, and each raises the peer's public
value to its own private key. Correctness: both arrive at `g ^ (α · β).val`.

## Scope

This file formalizes only the *correctness* (agreement) of the exchange.

## Main declarations

* `DiffieHellman g q hq hg` — the protocol, extending `KeyExchangeProtocol (ZMod q) G G`.
  Two setup invariants are carried as fields:
  - `hq : Fintype.card G = q` pins down `q` as the cardinality of `G`. This is what lets
    private keys live in `ZMod q` faithfully: by Lagrange `x ^ Fintype.card G = 1` for every
    `x : G`, hence `hq` gives `x ^ q = 1`, so exponents depend only on their residue
    modulo `q`.
  - `hg : orderOf g = q` says `g` has order `q`. Combined with `hq`, it means
    `orderOf g = Fintype.card G`, which in a cyclic group is exactly the statement that `g`
    is a generator.
* `secret_eq` — `(g ^ β.val) ^ α.val = g ^ (α * β).val`: the algebraic core of agreement.

## Reference

* [Boneh, Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup], Section 10.4.2
-/

namespace Cslib.Systems.Distributed.Protocols.Cryptographic.KeyExchange.DH

open KeyExchange

class DiffieHellman {G : Type u} [Group G] [Fintype G] [IsCyclic G]
    (g : G) (q : ℕ) (hq : Fintype.card G = q) (hg : orderOf g = q)
    extends KeyExchangeProtocol (ZMod q) G G where
  pub α := g ^ α.val
  sharedSecret u α := u ^ α.val
  agreement := by
    intro α β
    show (g ^ β.val) ^ α.val = (g ^ α.val) ^ β.val
    rw [← pow_mul, ← pow_mul, mul_comm]

variable {G : Type u} [Group G] [Fintype G]
variable (g : G) (q : ℕ) (hq : Fintype.card G = q)
include hq

/-- In a finite group of cardinality `q`, exponents may be reduced modulo `q`. Together with
`ZMod.val_mul` this lets `ℕ`-valued exponents be treated as living in `ZMod q`. -/
private lemma pow_mod_q (x : G) (n : ℕ) :
    x ^ (n % q) = x ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n q]
  have hxq : x ^ q = 1 := hq ▸ pow_card_eq_one
  rw [pow_add, pow_mul, hxq, one_pow, one_mul]

/-- The Diffie-Hellman shared secret `(g ^ β.val) ^ α.val` equals `g ^ (α * β).val`,
independently of which party computes it. This is the algebraic core of `agreement`. -/
theorem secret_eq (α β : ZMod q) :
    (g ^ β.val) ^ α.val = g ^ (α * β).val := by
  rw [← pow_mul, ZMod.val_mul, mul_comm β.val α.val, pow_mod_q q hq]

end Cslib.Systems.Distributed.Protocols.Cryptographic.KeyExchange.DH
