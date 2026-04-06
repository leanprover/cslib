/-
Copyright (c) 2026 Christiano Braga. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christiano Braga
-/

module

public import Mathlib.Tactic
public import Cslib.Systems.Distributed.Protocols.Cryptographic.Sigma.Basic

@[expose] public section

/-!
# Schnorr Identification Protocol

Schnorr's Identification Protocol can be understood as an instance of a sigma protocol.

Let 𝔾 be a cyclic group of prime order q, and let g be a generator of 𝔾.
The prover's secret key is α ←ᴿ ℤ_q, and the corresponding public key is u := gᵅ ∈ 𝔾.

The protocol proceeds as in a sigma protocol, as follows:

1. Commitment: The prover picks αₜ ←ᴿ ℤ_q, computes uₜ := gᵅᵗ, and sends uₜ to the verifier.
2. Challenge: The verifier picks c ←ᴿ ℤ_q and sends c to the prover.
3. Response: The prover computes α_z := αₜ + α · c (mod q) and sends α_z to the verifier.
4. Verification: The verifier accepts if and only if gᵅᶻ = uₜ · uᶜ.

Reference:

* [D. Boneh and V. Shoup,V., *A Graduate Course in Applied Cryptography*,
  Schnorr Identification Protocol][BonehShoup], Section 19.1.
-/

section SchnorrHelpers

variable {G : Type u} [CommGroup G] {q : ℕ} [Fact q.Prime]
variable (hG : ∀ x : G, x ^ q = 1)
include hG

/-
pow_mod_q — Exponents can be reduced mod q.
Uses the division algorithm: n = q · (n / q) + (n mod q), then hG to collapse (x^q)^(n/q) to 1.
-/
omit [Fact q.Prime] in
private lemma pow_mod_q (y : G) (n : ℕ) : y ^ (n % q) = y ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n q]
  rw [pow_add, pow_mul, hG y, one_pow, one_mul]

/-
pow_val_mul — Multiplication in ℤ/qℤ corresponds to iterated exponentiation.
Combines ZMod.val_mul with pow_mod_q and pow_mul.
-/
omit [Fact q.Prime] in
private lemma pow_val_mul (y : G) (a b : ZMod q) :
    y ^ (a * b).val = (y ^ a.val) ^ b.val := by
  rw [ZMod.val_mul, pow_mod_q hG, pow_mul]

/-
pow_val_sub — Subtraction in ℤ/qℤ corresponds to division in G.
Shows y^(a-b) · y^b = y^a via ZMod.val_add and sub_add_cancel,
then concludes by dividing both sides by y^b.
-/
private lemma pow_val_sub (y : G) (a b : ZMod q) :
    y ^ (a - b).val = y ^ a.val * (y ^ b.val)⁻¹ := by
  have h : y ^ (a - b).val * y ^ b.val = y ^ a.val := by
    rw [← pow_add, ← pow_mod_q hG y ((a - b).val + b.val)]
    congr 1; rw [← ZMod.val_add, sub_add_cancel]
  exact eq_mul_inv_of_mul_eq h

end SchnorrHelpers

instance SchnorrProtocol {G : Type u} [CommGroup G] (g : G) (q : ℕ) [Fact q.Prime]
    (hG : ∀ x : G, x ^ q = 1) :
    SigmaProtocol G (ZMod q × ZMod q) G (ZMod q) (ZMod q) where
  rel      := fun x rw => x = g ^ rw.2.val
  commit   := fun _ rw => g ^ rw.1.val
  respond  := fun _ rw _ e => rw.1 + e * rw.2
  verify   := fun x a e z => g ^ z.val = a * x ^ e.val
  extract  := fun _ _ e z e' z' => (0, (z - z') * (e - e')⁻¹)
  complete := by
    intro s w e hrel
    subst hrel
    have hval : (w.1 + e * w.2).val = (w.1.val + e.val * w.2.val) % q := by
      simp [ZMod.val_add, ZMod.val_mul, Nat.add_mod,
          Nat.mod_eq_of_lt (Nat.mod_lt _ (Nat.Prime.pos (Fact.out)))]
    rw [hval, pow_mod_q hG, pow_add, mul_comm e.val w.2.val, pow_mul]
  sound := by
    intro x a e e' z z' hne hv hv'
    simp only
    have h1 : g ^ z.val * (g ^ z'.val)⁻¹ = x ^ e.val * (x ^ e'.val)⁻¹ := by
      rw [hv, hv']; group
      simp only [ZMod.natCast_val, Int.reduceNeg, zpow_neg, zpow_one, mul_inv_cancel_comm]
    have hdiff : g ^ (z - z').val = x ^ (e - e').val := by
      rw [pow_val_sub hG g z z', pow_val_sub hG x e e', h1]
    calc x
        = x ^ (1 : ZMod q).val := by rw [ZMod.val_one q, pow_one]
      _ = x ^ ((e - e') * (e - e')⁻¹).val := by
            congr 1; congr 1; exact (mul_inv_cancel₀ (sub_ne_zero.mpr hne)).symm
      _ = (x ^ (e - e').val) ^ (e - e')⁻¹.val := pow_val_mul hG x _ _
      _ = (g ^ (z - z').val) ^ (e - e')⁻¹.val := by rw [hdiff]
      _ = g ^ ((z - z') * (e - e')⁻¹).val := (pow_val_mul hG g _ _).symm
  shvzk :=
    ⟨fun x e => (g ^ (0 : ZMod q).val * (x ^ e.val)⁻¹, 0), by
      intro x e; simp only; group⟩

end
