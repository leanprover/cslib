/-
Copyright (c) 2026 Christiano Braga. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christiano Braga
-/

module

public import Mathlib.Algebra.Module.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Nat.Prime.Basic

/-!
# Diffie–Hellman primitive, founded on `Module F G`

The Diffie–Hellman primitive is the scalar action of a commutative ring `F` on
an additive abelian group `G`. Writing exponents additively, as Mathlib does
for elliptic-curve groups, the textbook `gᵃ` becomes `a • g`, and the textbook
exponent-product `(gᵃ)ᵇ = gᵃᵇ` becomes `b • (a • g) = (b * a) • g`. Every
Mathlib `Module` lemma applies directly to `dh`.

`dh` is gated on two **orthogonal** cryptographic prerequisites:

1. `IsHonestGenerator F G` — there is a fixed `generator : G` for which the
   scalar-to-point map is a bijection. Rules out *degenerate* modules
   (trivial, rank > 1, torsion-bearing), on which DLog is ill-defined.
2. `Fact (Nat.Prime (Fintype.card F))` — the scalar ring's cardinality is
   prime, so (via the bijection) `G` is a prime-order cyclic group. Rules
   out *composite-order* modules, on which Pohlig–Hellman reduces DLog in
   `G` to DLog in its prime-power subgroups — catastrophic for security.

The two conditions are independent: a bijection can hold on a
composite-order group (`ZMod 6 → ZMod 6` via the identity), and a
prime-order group can fail bijection (a degenerate non-faithful action).
Both gates are needed; both are forced onto `dh` via `include hg hp`.

On any module that fails either gate, DH's algebraic equations still hold,
but its cryptographic claims collapse, so they are excluded at the type
level.

Downstream protocols (X3DH, PQXDH, Signal double-ratchet, MLS) consume the
primitive and its correctness laws. Hardness assumptions (DLog, CDH, DDH)
and concrete instantiations (X25519, X448) live in separate files; the
latter install `IsHonestGenerator F G` and `Fact (Nat.Prime …)` instances
by exhibiting their standard base point and citing the established
primality of their subgroup order.

## Notation correspondence

| Multiplicative textbook    | Additive (`Module F G`)        |
|----------------------------|--------------------------------|
| `gᵃ`                       | `a • g`                        |
| `(gᵃ)ᵇ = gᵃᵇ`              | `b • (a • g) = (b * a) • g`    |
| `gᵃ · gᵇ = gᵃ⁺ᵇ`           | `a • g + b • g = (a + b) • g`  |
| `(g · h)ᵃ = gᵃ · hᵃ`       | `a • (g + h) = a • g + a • h`  |

## Main declarations

* `IsHonestGenerator F G` — typeclass: a fixed element `generator : G` for
  which `(· • generator) : F → G` is a bijection (non-degeneracy of the
  action).
* `dh a B` — the primitive `a • B`. Gated on
  `[IsHonestGenerator F G]` *and* `[Fact (Nat.Prime (Fintype.card F))]`
  (the latter is the prime-order condition, supplied independently).
* `shared_eq_mul` — the shared point in canonical form:
  `b • (a • B) = (a * b) • B`.
* `agreement` — the two parties compute the same shared point; corollary
  of `shared_eq_mul`.

## References

* [VCVio26] Tuma, Dao, Waters, Hicks, Hopper, *VCVio: Verified Cryptography in
  Lean via Oracle Effects and Handlers*, Cryptology ePrint 2026/899
  ([eprint.iacr.org/2026/899](https://eprint.iacr.org/2026/899)) — companion
  paper to the [VCV-io library](https://github.com/Verified-zkEVM/VCV-io),
  whose [DiffieHellman.lean]
  (https://github.com/Verified-zkEVM/VCV-io/blob/main/
                                    VCVio/CryptoFoundations/HardnessAssumptions/DiffieHellman.lean)
  uses the same `Module F G` foundation as this file and lifts it to the
  hardness layer (DLog/CDH/DDH experiments and reductions).
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.DiffieHellman

/-- `g` is an **honest generator** for the scalar action of `F` on `G` when
the map `(fun a : F => a • g) : F → G` is a bijection: surjective (every
point of `G` is reachable as `a • g`) and injective (distinct scalars
produce distinct points; no torsion collisions). This is the
*non-degeneracy* condition on the chosen generator, and is orthogonal to
any condition on the order of `G`.

Without the bijection, DLog is ill-defined or multi-valued, and the
discrete-log game is meaningless even before we consider hardness. -/
class IsHonestGenerator (F G : Type*) [CommRing F] [AddCommGroup G] [Module F G] where
  /-- The chosen honest generator. -/
  generator : G
  /-- The scalar-to-point map at `generator` is a bijection. -/
  bijective : Function.Bijective (fun a : F => a • generator)

variable {F G : Type*} [CommRing F] [AddCommGroup G] [Module F G]

section
variable [Fintype F] [hg : IsHonestGenerator F G] [hp : Fact (Nat.Prime (Fintype.card F))]
include hg hp
-- `dh` is gated on **two orthogonal cryptographic prerequisites**:
--   1. `IsHonestGenerator F G` — the action is faithful (bijection).
--   2. `Fact (Nat.Prime (Fintype.card F))` — the scalar ring's cardinality
--      is prime, so (under the bijection) `G` is a prime-order cyclic
--      group, avoiding Pohlig–Hellman.
-- `dh`'s body doesn't reference either typeclass, so we force their
-- inclusion via `include hg hp`.

/-- Diffie–Hellman primitive: the scalar action `a • B`. Gated unconditionally
on `[IsHonestGenerator F G]` and `[Fact (Nat.Prime (Fintype.card F))]` —
this file does not formalize DH on degenerate or composite-order modules. -/
abbrev dh (a : F) (B : G) : G := a • B
end

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
