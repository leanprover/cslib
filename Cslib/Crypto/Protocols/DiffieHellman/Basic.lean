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

DH is restricted here to **non-degenerate** modules. The class
`IsHonestGenerator F G` (declared below) asserts that some element of `G`
makes the scalar-to-point map a bijection, and every other declaration in
this file is gated on it via `include hg`. Degenerate modules (trivial,
rank > 1, torsion-bearing) satisfy `Module F G` but admit no honest
generator; DH's algebraic equations still hold on them, but its security
claims collapse, so they are excluded at the type level.

Downstream protocols (X3DH, PQXDH, Signal double-ratchet, MLS) consume
the primitive and its correctness laws. Hardness assumptions (DLog, CDH,
DDH) and concrete instantiations (X25519, X448) live in separate files;
the latter install `IsHonestGenerator F G` instances by exhibiting their
standard base point as `generator`.

## Notation correspondence

| Multiplicative textbook    | Additive (`Module F G`)        |
|----------------------------|--------------------------------|
| `gᵃ`                       | `a • g`                        |
| `(gᵃ)ᵇ = gᵃᵇ`              | `b • (a • g) = (b * a) • g`    |
| `gᵃ · gᵇ = gᵃ⁺ᵇ`           | `a • g + b • g = (a + b) • g`  |
| `(g · h)ᵃ = gᵃ · hᵃ`       | `a • (g + h) = a • g + a • h`  |

## Main declarations

* `IsHonestGenerator F G` — typeclass: `G` has a fixed honest generator —
  an element `generator : G` for which `(· • generator) : F → G` is a
  bijection. The minimal non-degeneracy condition; every other declaration
  in this file is gated on it.
* `dh a B` — the primitive `a • B`.
* `shared_eq_mul` — the shared point in canonical form:
  `b • (a • B) = (a * b) • B`.
* `agreement` — the two parties compute the same shared point; corollary
  of `shared_eq_mul`.

## References

* Verified-zkEVM, [VCV-io / VCVio/CryptoFoundations/HardnessAssumptions/DiffieHellman.lean](https://github.com/Verified-zkEVM/VCV-io/blob/main/VCVio/CryptoFoundations/HardnessAssumptions/DiffieHellman.lean) —
  VCV-io uses the same `Module F G` foundation as this file.
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.DiffieHellman

/-- `G`, viewed as an `F`-module, has a fixed **honest generator** — an
element `generator : G` for which the scalar-to-point map
`(fun a : F => a • generator)`, *"given a scalar `a`, return the point
`a • generator`"*, is a bijection.

The bijection packs two conditions:

* **surjective** — every point in `G` is reachable as `a • generator` for some
  scalar `a`; no spot is hidden from scalar sampling.
* **injective** — distinct scalars produce distinct points; equivalently, the
  generator has no torsion collisions that would collapse exponent counts.

This is the minimal non-degeneracy condition under which DH is
cryptographically meaningful. Degenerate modules (trivial; rank > 1;
torsion-bearing) satisfy `Module F G` but fail to admit any honest
generator, and DH's security claims collapse on them. Concrete
instantiations (X25519, X448) install an instance by exhibiting their
standard base point as `generator`. -/
class IsHonestGenerator (F G : Type*) [CommRing F] [AddCommGroup G] [Module F G] where
  /-- The chosen honest generator. -/
  generator : G
  /-- The scalar-to-point map at `generator` is a bijection. -/
  bijective : Function.Bijective (fun a : F => a • generator)

variable {F G : Type*} [CommRing F] [AddCommGroup G] [Module F G] [hg : IsHonestGenerator F G]

include hg in -- Necessary because a • B does not need hg, so the elaborator does not bind it.
              -- A degenerate module is cryptographically insecure.
/-- Diffie–Hellman primitive: the scalar action `a • B`. Gated unconditionally
on `[IsHonestGenerator F G]` (via `include hg` in this section) — this file
does not formalize DH on degenerate modules. -/
abbrev dh (a : F) (B : G) : G := a • B

omit hg in -- Because dh already carries hg.
/-- **Shared secret in canonical form.** Either party's computation lands
on `(a * b) • B` — a single closed expression independent of which side
performs the final scalar action. -/
theorem shared_eq_mul (a b : F) (B : G) :
    dh b (dh a B) = (a * b) • B := by
  change b • (a • B) = (a * b) • B
  rw [← mul_smul, mul_comm b a]

omit hg in -- Because dh already carries hg.
/-- **Agreement.** Two parties starting from a common base point `B`, with
private scalars `a` and `b`, compute the same shared point. Corollary of
`shared_eq_mul` by commutativity of multiplication in `F`. -/
theorem agreement (a b : F) (B : G) :
    dh b (dh a B) = dh a (dh b B) := by
  rw [shared_eq_mul, mul_comm a b, ← shared_eq_mul]

end Cslib.Crypto.Protocols.DiffieHellman
