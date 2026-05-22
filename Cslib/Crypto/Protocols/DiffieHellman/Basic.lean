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
* `shared_eq_mul` — the shared point in canonical form:
  `b • (a • B) = (a * b) • B`.
* `agreement` — the two parties compute the same shared point; corollary
  of `shared_eq_mul`.

## References

* BAIF, [PostQuantumeXtendedDiffieHellman-model / PQXDHLean/X3DH/DH.lean](https://github.com/Beneficial-AI-Foundation/PostQuantumeXtendedDiffieHellman-model/blob/main/PQXDHLean/X3DH/DH.lean).
* Verified-zkEVM, [VCV-io / VCVio/CryptoFoundations/HardnessAssumptions/DiffieHellman.lean](https://github.com/Verified-zkEVM/VCV-io/blob/main/VCVio/CryptoFoundations/HardnessAssumptions/DiffieHellman.lean).
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.DiffieHellman

variable {F : Type*} [CommRing F]
variable {G : Type*} [AddCommGroup G] [Module F G]

/-- Diffie–Hellman primitive: the scalar action `a • B`. Declared as `abbrev`
so that every Mathlib `Module` lemma applies definitionally. -/
abbrev dh (a : F) (B : G) : G := a • B

/-- **Shared secret in canonical form.** Either party's computation lands
on `(a * b) • B` — a single closed expression independent of which side
performs the final scalar action. -/
theorem shared_eq_mul (a b : F) (B : G) :
    dh b (dh a B) = (a * b) • B := by
  change b • (a • B) = (a * b) • B
  rw [← mul_smul, mul_comm b a]

/-- **Agreement.** Two parties starting from a common base point `B`, with
private scalars `a` and `b`, compute the same shared point. Corollary of
`shared_eq_mul` by commutativity of multiplication in `F`. -/
theorem agreement (a b : F) (B : G) :
    dh b (dh a B) = dh a (dh b B) := by
  rw [shared_eq_mul, mul_comm a b, ← shared_eq_mul]

end Cslib.Crypto.Protocols.DiffieHellman
