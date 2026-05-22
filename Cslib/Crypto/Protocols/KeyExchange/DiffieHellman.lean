/-
Copyright (c) 2026 Christiano Braga. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christiano Braga
-/

module

public import Mathlib.Algebra.Module.Basic

/-!
# Diffie–Hellman primitive, founded on `Module F G`

The Diffie–Hellman primitive is the scalar action of a commutative ring `F` on
an additive abelian group `G`. Writing exponents additively, as Mathlib does
for elliptic-curve groups, the textbook `gᵃ` becomes `a • g`, and the textbook
exponent-product `(gᵃ)ᵇ = gᵃᵇ` becomes `b • (a • g) = (b * a) • g`. Every
Mathlib `Module` lemma applies directly to `dh`.

This file states only the primitive and the laws downstream protocols (X3DH,
PQXDH, Signal double-ratchet, MLS) cite. Hardness assumptions (DLog, CDH,
DDH) and concrete instantiations (X25519, X448) live in separate files.

## Notation correspondence

| Multiplicative textbook    | Additive (`Module F G`)        |
|----------------------------|--------------------------------|
| `gᵃ`                       | `a • g`                        |
| `(gᵃ)ᵇ = gᵃᵇ`              | `b • (a • g) = (b * a) • g`    |
| `gᵃ · gᵇ = gᵃ⁺ᵇ`           | `a • g + b • g = (a + b) • g`  |
| `(g · h)ᵃ = gᵃ · hᵃ`       | `a • (g + h) = a • g + a • h`  |

## Main declarations

* `dh a B` — the primitive `a • B`.
* `agreement` — `b • (a • B) = a • (b • B)`: the two parties agree on the
  shared point regardless of which side performs the final scalar action.
* `dh_add_left`, `dh_add_right` — scalar- and base-additivity of `dh`,
  cited by protocols that combine secrets or transcripts additively
  (X3DH/PQXDH).

## References

* [Boneh, Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup],
  Section 10.4.
* BAIF, *PostQuantumeXtendedDiffieHellman-model* (PQXDHLean/X3DH/DH.lean).
* Verified-zkEVM, *VCV-io*
  (VCVio/CryptoFoundations/HardnessAssumptions/DiffieHellman.lean).
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.KeyExchange.DH

variable {F : Type*} [CommRing F]
variable {G : Type*} [AddCommGroup G] [Module F G]

/-- Diffie–Hellman primitive: the scalar action `a • B`. Declared as `abbrev`
so that every Mathlib `Module` lemma applies definitionally. -/
abbrev dh (a : F) (B : G) : G := a • B

/-- **Agreement.** Two parties starting from a common base point `B`, with
private scalars `a` and `b`, compute the same shared point regardless of
which side performs the final scalar action. Both sides equal `(a * b) • B`. -/
theorem agreement (a b : F) (B : G) :
    dh b (dh a B) = dh a (dh b B) := by
  change b • (a • B) = a • (b • B)
  rw [← mul_smul, ← mul_smul, mul_comm]

/-- Scalar-additivity. Cited by protocols that combine secrets additively,
e.g. a long-term scalar added to an ephemeral one. -/
theorem dh_add_left (a b : F) (B : G) :
    dh (a + b) B = dh a B + dh b B :=
  add_smul a b B

/-- Base-additivity. Cited by protocols whose peer public values decompose
as sums of component public values, as in X3DH/PQXDH transcripts. -/
theorem dh_add_right (a : F) (B C : G) :
    dh a (B + C) = dh a B + dh a C :=
  smul_add a B C

end Cslib.Crypto.Protocols.KeyExchange.DH
