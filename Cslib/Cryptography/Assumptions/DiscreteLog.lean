/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Cryptography.Foundations.SecurityGame
public import Mathlib.Data.ZMod.Basic

@[expose] public section

/-!
# The Discrete Logarithm Assumption

The **discrete logarithm (DL) assumption** states that no efficient
adversary, given a random group element `u = g^α` in a cyclic group
of prime order, can recover the exponent `α` with non-negligible
probability.

This is the foundational hardness assumption for Schnorr signatures,
Diffie-Hellman key exchange, and many zero-knowledge protocols.

## Main Definitions

* `CyclicGroupFamily` — a family of cyclic groups of prime order
  indexed by the security parameter, with an explicit exponentiation
  map `gpow : ZMod q → G`
* `DL_Adversary` — an adversary for the discrete log problem
* `DL_Game` — the DL security game
* `DL_Assumption` — the DL assumption (DL game is secure against
  admissible adversaries)

## Design Notes

We model cyclic groups abstractly via a family indexed by the security
parameter. The exponentiation map `gpow n : ZMod (order n) → Group n`
provides a group isomorphism from `(ZMod q, +)` to `(G, ·)`, capturing
the standard encoding of group elements via discrete logarithms.

## References

* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2014]
* [O. Goldreich, *Foundations of Cryptography, Vol. 1*][Goldreich2001]
-/

/-- A **family of cyclic groups of prime order** indexed by the security
parameter. At each level `n`:
- `Group n` is a finite commutative group of prime order `order n`
- `gpow n` is a group isomorphism from `(ZMod (order n), +)` to `(Group n, ·)`
- `gpow n 1 = generator n` identifies the canonical generator -/
structure CyclicGroupFamily where
  /-- The group type at security level `n` -/
  Group : ℕ → Type
  /-- The group order at security level `n` -/
  order : ℕ → ℕ
  /-- Each group is a commutative group -/
  groupInst : ∀ n, CommGroup (Group n)
  /-- Each group is finite -/
  fintypeInst : ∀ n, Fintype (Group n)
  /-- Each group has decidable equality -/
  decEqInst : ∀ n, DecidableEq (Group n)
  /-- Each group is nonempty -/
  nonemptyInst : ∀ n, Nonempty (Group n)
  /-- The order is positive -/
  order_pos : ∀ n, 0 < order n
  /-- The order is prime -/
  order_prime : ∀ n, Nat.Prime (order n)
  /-- The canonical generator -/
  generator : ∀ n, Group n
  /-- The exponentiation map `α ↦ g^α`, a group isomorphism
  `(ZMod q, +) → (G, ·)` -/
  gpow : ∀ n, ZMod (order n) → Group n
  /-- `g^0 = 1` -/
  gpow_zero : ∀ n, gpow n 0 = 1
  /-- `g^(a+b) = g^a · g^b` — `gpow` is a group homomorphism -/
  gpow_add : ∀ n (a b : ZMod (order n)),
    gpow n (a + b) = @HMul.hMul _ _ _ (@instHMul _ (groupInst n).toMul) (gpow n a) (gpow n b)
  /-- `g^1 = generator` -/
  gpow_generator : ∀ n, gpow n 1 = generator n
  /-- `gpow` is injective (hence bijective, since domain and codomain
  have the same finite cardinality) -/
  gpow_injective : ∀ n, Function.Injective (gpow n)
  /-- `gpow` is surjective — every group element has a discrete log -/
  gpow_surjective : ∀ n, Function.Surjective (gpow n)

attribute [instance] CyclicGroupFamily.groupInst CyclicGroupFamily.fintypeInst
  CyclicGroupFamily.decEqInst CyclicGroupFamily.nonemptyInst

namespace CyclicGroupFamily

variable (C : CyclicGroupFamily)

/-- `NeZero` instance for the order, required by many `ZMod` lemmas. -/
instance orderNeZero (n : ℕ) : NeZero (C.order n) :=
  ⟨Nat.pos_iff_ne_zero.mp (C.order_pos n)⟩

/-- `ZMod (order n)` is finite (for sampling). -/
noncomputable instance zmodFintype (n : ℕ) : Fintype (ZMod (C.order n)) :=
  ZMod.fintype (C.order n)

/-- `ZMod (order n)` is nonempty. -/
instance zmodNonempty (n : ℕ) : Nonempty (ZMod (C.order n)) := ⟨0⟩

/-- `ZMod (order n)` has decidable equality. -/
instance zmodDecEq (n : ℕ) : DecidableEq (ZMod (C.order n)) :=
  ZMod.decidableEq (C.order n)

/-- The discrete logarithm: the unique `α` such that `g^α = y`.
This is the inverse of `gpow`. It is noncomputable (computing it
is exactly the discrete log problem). -/
noncomputable def dlog (n : ℕ) (y : C.Group n) : ZMod (C.order n) :=
  (C.gpow_surjective n y).choose

/-- `g^(dlog y) = y` — the discrete log inverts `gpow`. -/
theorem gpow_dlog (n : ℕ) (y : C.Group n) :
    C.gpow n (C.dlog n y) = y :=
  (C.gpow_surjective n y).choose_spec

/-- `dlog (g^α) = α` — `dlog` inverts `gpow`. -/
theorem dlog_gpow (n : ℕ) (a : ZMod (C.order n)) :
    C.dlog n (C.gpow n a) = a :=
  C.gpow_injective n (by rw [C.gpow_dlog])

/-- The exponentiation map distributes over natural scalar multiplication:
`g^(k • α) = (g^α)^k`. -/
theorem gpow_nsmul (n : ℕ) (k : ℕ) (a : ZMod (C.order n)) :
    C.gpow n (k • a) = C.gpow n a ^ k := by
  induction k with
  | zero => simp [C.gpow_zero]
  | succ k ih =>
    rw [succ_nsmul, C.gpow_add, ih, pow_succ]

/-- `g^(c * α) = (g^α) ^ (ZMod.val c)` — connects ring multiplication
in `ZMod q` with group exponentiation. -/
theorem gpow_mul (n : ℕ) (c a : ZMod (C.order n)) :
    C.gpow n (c * a) = C.gpow n a ^ (ZMod.val c) := by
  rw [← C.gpow_nsmul n (ZMod.val c) a]
  congr 1
  rw [nsmul_eq_mul]
  have : (ZMod.val c : ZMod (C.order n)) = c := by
    rw [ZMod.natCast_val, ZMod.cast_id]
  rw [this]

/-- Negation: `g^(-α) = (g^α)⁻¹`. -/
theorem gpow_neg (n : ℕ) (a : ZMod (C.order n)) :
    C.gpow n (-a) = (C.gpow n a)⁻¹ := by
  have h : C.gpow n (-a) * C.gpow n a = 1 := by
    rw [← C.gpow_add, neg_add_cancel, C.gpow_zero]
  exact mul_eq_one_iff_eq_inv.mp h

/-- Subtraction: `g^(a - b) = g^a · (g^b)⁻¹`. -/
theorem gpow_sub (n : ℕ) (a b : ZMod (C.order n)) :
    C.gpow n (a - b) = C.gpow n a * (C.gpow n b)⁻¹ := by
  rw [sub_eq_add_neg, C.gpow_add, C.gpow_neg]

/-- Commutativity variant of `gpow_mul`: `g^(a * c) = (g^a) ^ val(c)`. -/
theorem gpow_mul' (n : ℕ) (a c : ZMod (C.order n)) :
    C.gpow n (a * c) = C.gpow n a ^ (ZMod.val c) := by
  rw [mul_comm, C.gpow_mul]

end CyclicGroupFamily

/-- A **discrete logarithm adversary**: given a group element `u`,
output a candidate exponent `α`. -/
structure DL_Adversary (C : CyclicGroupFamily) where
  /-- Given the security parameter and a group element, guess the
  discrete logarithm. -/
  guess : (n : ℕ) → C.Group n → ZMod (C.order n)

/-- The **discrete logarithm security game**: the challenger samples
`α ← ZMod q` uniformly and gives `u = g^α` to the adversary.
The adversary wins if it outputs `α' = α` (equivalently, `g^α' = u`). -/
noncomputable def DL_Game (C : CyclicGroupFamily) :
    SecurityGame (DL_Adversary C) :=
  SecurityGame.ofCoinGame
    (Coins := fun n => ZMod (C.order n))
    (fun A n α =>
      let u := C.gpow n α
      let α' := A.guess n u
      Cslib.Probability.boolToReal (decide (C.gpow n α' = u)))

/-- The **DL assumption** for a cyclic group family: the DL game is
secure against all adversaries in the admissible class. -/
def DL_Assumption (C : CyclicGroupFamily)
    (Admissible : DL_Adversary C → Prop) : Prop :=
  (DL_Game C).SecureAgainst Admissible

end
