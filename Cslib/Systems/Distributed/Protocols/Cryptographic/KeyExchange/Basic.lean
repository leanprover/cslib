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

A *key exchange protocol* allows two parties (Alice and Bob) to establish a shared secret
over an insecure channel.

The protocol proceeds as follows:

1. Alice picks a private key α, computes her public value pub(α), and sends it to Bob.
2. Bob picks a private key β, computes his public value pub(β), and sends it to Alice.
3. Alice computes the shared secret as sharedSecret(pub(β), α).
4. Bob computes the shared secret as sharedSecret(pub(α), β).

The fundamental correctness property (*agreement*) states that both parties compute the same
shared secret:

  sharedSecret(pub(β), α) = sharedSecret(pub(α), β)

Reference:

* [D. Boneh and V. Shoup,V., *A Graduate Course in Applied Cryptography*][BonehShoup],
  Section 10.4.
-/

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
