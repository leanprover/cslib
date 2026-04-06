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

Suppose p is a large prime and that q is a large prime dividing p − 1 (think of p as being very
large random prime, say 2048 bits long, and think of q as being about 256 bits long). We will be
doing arithmetic mod p, that is, working in ℤₚ. Recall that ℤₚ* is the set of nonzero elements
of ℤₚ. An essential fact is that since q divides p − 1, ℤₚ* has an element g of order q.
This means that gᑫ = 1 and that all of the powers gᵃ, for a = 0, …, q − 1, are distinct.
Let G := {gᵃ : a = 0, …, q − 1}, so that G is a subset of ℤₚ* of cardinality q. It is not hard
to see that G is closed under multiplication and inversion; that is, for all u, v ∈ G,
we have u·v ∈ G and u⁻¹ ∈ G. Indeed, gᵃ · gᵇ = gᵃ⁺ᵇ = gᶜ with c := (a + b) mod q, and (gᵃ)⁻¹ = gᵈ
with d := (−a) mod q. In the language of algebra, G is called a subgroup of the group ℤₚ*.

For every u ∈ G and integers a and b, it is easy to see that uᵃ = uᵇ if a ≡ b mod q.
Thus, the value of uᵃ depends only on the residue class of a modulo q. Therefore,
if α = [a]_q ∈ ℤ_q is the residue class of a modulo q, we can define uᵅ := uᵃ and this definition
is unambiguous. From here on we will frequently use elements of ℤ_q as exponents applied to
elements of G.

So now we have everything we need to describe the Diffie-Hellman key exchange protocol.
We assume that the description of G, including g ∈ G and q, is a system parameter that is
generated once and for all at system setup time and shared by all parties involved.
The protocol runs as follows:

1. Alice computes α ←ᴿ ℤ_q, u ← gᵅ, and sends u to Bob.
2. Bob computes β ←ᴿ ℤ_q, v ← gᵝ, and sends v to Alice.
3. Upon receiving v from Bob, Alice computes w ← vᵅ.
4. Upon receiving u from Alice, Bob computes w ← uᵝ.

The secret shared by Alice and Bob is:

  w = vᵅ = gᵅᵝ = uᵝ

Reference:

* [D. Boneh and V. Shoup,V., *A Graduate Course in Applied Cryptography*, One-time pad][BonehShoup],
  Section 10.4.
-/

instance DiffieHellmanKE {G : Type u} [CommGroup G] (g : G) (q : ℕ) :
    KeyExchangeProtocol (ZMod q) G G where
  pub := fun α => g ^ α.val
  sharedSecret := fun u α => u ^ α.val
  agreement := by
    intro α β
    show (g ^ β.val) ^ α.val = (g ^ α.val) ^ β.val
    rw [← pow_mul, ← pow_mul, mul_comm]

namespace Cslib.Systems.Distributed.Protocols.Cryptographic.DH

variable {G : Type u} [CommGroup G] {q : ℕ} [Fact q.Prime]
variable (g : G) (hG : ∀ x : G, x ^ q = 1)
include hG

/-
pow_mod_q — Exponents can be reduced mod q
  x ^ (n % q) = x ^ n

What it says: Exponentiating by n is the same as exponentiating by n mod q.

Why it's true: By the division algorithm, n = q · (n / q) + (n mod q). So:
  x^n = x^(q·(n/q) + n mod q) = x^(q·(n/q)) · x^(n mod q)
      = (x^q)^(n/q) · x^(n mod q) = 1^(n/q) · x^(n mod q) = x^(n mod q)

Why it matters: It lets you treat ℕ-valued exponents as living in ZMod q,
bridging Lean's natural number arithmetic with modular arithmetic.
-/
omit [Fact q.Prime] in
private lemma pow_mod_q (x : G) (n : ℕ) : x ^ (n % q) = x ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n q]
  rw [pow_add, pow_mul, hG x, one_pow, one_mul]

/-
secret_eq — The shared secret (gᵝ)ᵅ equals g^(α·β)
Computing the shared secret from the other party's public value
is the same as exponentiating the generator by the product of both private keys.
This is the key algebraic fact underlying the protocol — it
shows the shared secret can be characterized as g^(α·β), independent of which
party computes it.
-/
omit [Fact q.Prime] in
theorem secret_eq (α β : ZMod q) :
    (g ^ β.val) ^ α.val = g ^ (α * β).val := by
  rw [← pow_mul, ZMod.val_mul, mul_comm β.val α.val, pow_mod_q hG]

end Cslib.Systems.Distributed.Protocols.Cryptographic.DH
