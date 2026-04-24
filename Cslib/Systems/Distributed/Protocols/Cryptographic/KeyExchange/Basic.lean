/-
Copyright (c) 2026 Christiano Braga. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christiano Braga
-/

module

public import Mathlib.Tactic

@[expose] public section

/-!
# Key Exchange Protocol

An abstract typeclass capturing the structure of a two-party key-exchange protocol. A
protocol is given by three types — `PrivateKey`, `PublicValue`, `SharedSecret` — together
with:

* `pub : PrivateKey → PublicValue`, the value a party publishes;
* `sharedSecret : PublicValue → PrivateKey → SharedSecret`, what each party computes from
  the peer's public value and its own private key;
* `agreement`, the correctness law
  `sharedSecret (pub β) α = sharedSecret (pub α) β` for all `α, β`.

Concrete protocols (e.g. Diffie-Hellman) arise by instantiating the three types and
supplying the three fields. This file captures only the correctness equation; security
assumptions belong to concrete instances.

## Reference

* [Boneh, Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup], Section 10.4.1
-/

namespace Cslib.Systems.Distributed.Protocols.Cryptographic.KeyExchange

universe u v w

class KeyExchangeProtocol
    (PrivateKey : Type u) (PublicValue : Type v)
    (SharedSecret : Type w) where
  /-- Compute public value from private key. This is sent to the other party. -/
  pub : PrivateKey → PublicValue
  /-- Compute shared secret from received public value and own private key. -/
  sharedSecret : PublicValue → PrivateKey → SharedSecret
  /-- Agreement: both parties compute the same shared secret. -/
  agreement : ∀ (α β : PrivateKey),
    sharedSecret (pub β) α = sharedSecret (pub α) β

end Cslib.Systems.Distributed.Protocols.Cryptographic.KeyExchange
