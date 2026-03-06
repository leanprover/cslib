/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Cryptography.Assumptions.DiscreteLog
public import Cslib.Cryptography.Protocols.FiatShamir
public import Cslib.Cryptography.Protocols.SigmaProtocol

@[expose] public section

/-!
# Schnorr's Identification Protocol and Signature Scheme

Schnorr's protocol is the canonical Sigma protocol for proving
knowledge of a discrete logarithm. Given a cyclic group `G` of
prime order `q` with generator `g`, the prover demonstrates knowledge
of `α` such that `g^α = u` without revealing `α`.

## Main Definitions

* `SchnorrRelation` — the DL relation `R = { (α, u) : g^α = u }`
* `SchnorrProtocol` — Schnorr's Sigma protocol for `SchnorrRelation`
* `schnorrSpecialSoundness` — proof of special soundness
* `schnorrSpecialHVZK` — proof of special HVZK
* `SchnorrSignature` — the Schnorr signature scheme (Fiat-Shamir
  applied to the Schnorr protocol)

## Protocol Description

- **Commit**: Prover samples `α_t ← ZMod q`, sends `u_t = g^α_t`
- **Challenge**: Verifier sends `c ← ZMod q`
- **Respond**: Prover sends `α_z = α_t + α · c`
- **Verify**: Check `g^α_z = u_t · u^c`

## References

* [C.-P. Schnorr, *Efficient Signature Generation by Smart Cards*][Schnorr1991]
* Boneh-Shoup, *A Graduate Course in Applied Cryptography*, §19.1–19.2
* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2014]
-/

/-- The **discrete logarithm relation**: `(α, u) ∈ R` iff `g^α = u`.
This is the NP relation underlying Schnorr's protocol. -/
@[reducible] def SchnorrRelation (C : CyclicGroupFamily) : EffectiveRelation where
  Witness n := ZMod (C.order n)
  Statement n := C.Group n
  relation n α u := C.gpow n α = u

/-- Key generation for the Schnorr relation: `keyOf α = g^α`. -/
def SchnorrRelation.keyGen (C : CyclicGroupFamily) :
    (SchnorrRelation C).WithKeyGen where
  keyOf n α := C.gpow n α
  keyOf_valid _ _ := rfl

/-- **Schnorr's Sigma protocol** for the DL relation.

- Commitment: `u_t = g^α_t` for random `α_t`
- Challenge: `c ∈ ZMod q`
- Response: `α_z = α_t + α · c`
- Verify: `g^α_z = u_t · u^c`

The verification equation uses `y ^ (ZMod.val c)` for the group
exponentiation `u^c`, which is well-defined since the group has
order dividing `q`. -/
noncomputable def schnorr_commitUniform (C : CyclicGroupFamily) (n : ℕ)
    [Fintype (ZMod (C.order n))] [Nonempty (ZMod (C.order n))]
    [Fintype (C.Group n)] [Nonempty (C.Group n)]
    (f : C.Group n → ℝ) :
    Cslib.Probability.uniformExpect (ZMod (C.order n)) (fun r => f (C.gpow n r)) =
    Cslib.Probability.uniformExpect (C.Group n) f :=
  Cslib.Probability.uniformExpect_congr
    (Equiv.ofBijective (C.gpow n) ⟨C.gpow_injective n, C.gpow_surjective n⟩) f

@[reducible] noncomputable def SchnorrProtocol (C : CyclicGroupFamily) :
    SigmaProtocol (SchnorrRelation C) where
  Commitment n := C.Group n
  Challenge n := ZMod (C.order n)
  Response n := ZMod (C.order n)
  ProverRandomness n := ZMod (C.order n)
  commitmentFintype := C.fintypeInst
  commitmentNonempty := C.nonemptyInst
  commitmentDecEq := C.decEqInst
  challengeFintype := fun n => CyclicGroupFamily.zmodFintype C n
  challengeNonempty := fun n => CyclicGroupFamily.zmodNonempty C n
  challengeDecEq := fun n => CyclicGroupFamily.zmodDecEq C n
  responseFintype := fun n => CyclicGroupFamily.zmodFintype C n
  responseNonempty := fun n => CyclicGroupFamily.zmodNonempty C n
  proverRandomnessFintype := fun n => CyclicGroupFamily.zmodFintype C n
  proverRandomnessNonempty := fun n => CyclicGroupFamily.zmodNonempty C n
  commit n _w _y α_t := C.gpow n α_t
  respond n w _y α_t c := α_t + w * c
  verify n y u_t c α_z := decide (C.gpow n α_z = u_t * y ^ (ZMod.val c))
  completeness n w y r c hrel := by
    simp only [decide_eq_true_eq]
    -- hrel : C.gpow n w = y (the DL relation)
    change C.gpow n w = y at hrel
    rw [C.gpow_add, ← hrel, C.gpow_mul' n w c]

/-- **Special soundness** for the Schnorr protocol: from two accepting
conversations `(u_t, c, α_z)` and `(u_t, c', α_z')` with `c ≠ c'`,
the extractor computes `α = (α_z - α_z') / (c - c')`. -/
noncomputable def schnorrSpecialSoundness (C : CyclicGroupFamily) :
    (SchnorrProtocol C).SpecialSoundness where
  extract n _y _u_t c α_z c' α_z' := (α_z - α_z') * (c - c')⁻¹
  soundness n y u_t c α_z c' α_z' hne hv1 hv2 := by
    haveI : Fact (Nat.Prime (C.order n)) := ⟨C.order_prime n⟩
    -- hv1 : gpow α_z = u_t * y ^ val(c)
    -- hv2 : gpow α_z' = u_t * y ^ val(c')
    simp only [decide_eq_true_eq] at hv1 hv2
    -- We need: gpow ((α_z - α_z') * (c - c')⁻¹) = y
    change C.gpow n ((α_z - α_z') * (c - c')⁻¹) = y
    -- Let β = dlog y, then y = gpow β
    set β := C.dlog n y
    have hβ : C.gpow n β = y := C.gpow_dlog n y
    -- Let δ = dlog u_t
    set δ := C.dlog n u_t
    have hδ : C.gpow n δ = u_t := C.gpow_dlog n u_t
    -- Rewrite verification equations
    rw [← hβ, ← C.gpow_mul' n β c] at hv1
    rw [← hβ, ← C.gpow_mul' n β c'] at hv2
    rw [← hδ, ← C.gpow_add] at hv1 hv2
    -- By injectivity: α_z = δ + β * c and α_z' = δ + β * c'
    have inj1 := C.gpow_injective n hv1
    have inj2 := C.gpow_injective n hv2
    -- So α_z - α_z' = β * (c - c')
    have hdiff : α_z - α_z' = β * (c - c') := by
      rw [inj1, inj2]; ring
    -- Therefore (α_z - α_z') * (c - c')⁻¹ = β
    suffices h : (α_z - α_z') * (c - c')⁻¹ = β by rw [h]; exact hβ
    rw [hdiff]
    -- β * (c - c') * (c - c')⁻¹ = β in ZMod (C.order n)
    rw [mul_assoc]
    have hcc : (c - c' : ZMod (C.order n)) * (c - c')⁻¹ = 1 := by
      rw [ZMod.mul_inv_eq_gcd]
      have hprime := C.order_prime n
      have hne_zmod : (c - c' : ZMod (C.order n)) ≠ 0 := sub_ne_zero.mpr hne
      have hval_ne : (c - c' : ZMod (C.order n)).val ≠ 0 :=
        (ZMod.val_ne_zero _).mpr hne_zmod
      have hval_lt : (c - c' : ZMod (C.order n)).val < C.order n :=
        ZMod.val_lt _
      have hcop : Nat.Coprime (c - c' : ZMod (C.order n)).val (C.order n) :=
        ((Nat.Prime.coprime_iff_not_dvd hprime).mpr
          (fun hdvd => hval_ne (Nat.eq_zero_of_dvd_of_lt hdvd hval_lt))).symm
      simp [hcop.gcd_eq_one]
    rw [hcc, mul_one]

/-- **Special HVZK** for the Schnorr protocol: the simulator samples
`α_z ← ZMod q` and sets `u_t = g^α_z · u^(-c)`, producing a
transcript `(u_t, c, α_z)` that is accepting and has the same
distribution as a real transcript. -/
noncomputable def schnorrSpecialHVZK (C : CyclicGroupFamily) :
    (SchnorrProtocol C).SpecialHVZK where
  SimRandomness n := ZMod (C.order n)
  simRandomnessFintype := fun n => CyclicGroupFamily.zmodFintype C n
  simRandomnessNonempty := fun n => CyclicGroupFamily.zmodNonempty C n
  simulate n y c α_z :=
    let u_t := C.gpow n α_z * (y ^ (ZMod.val c))⁻¹
    (u_t, α_z)
  sim_accepting n y c α_z := by
    simp only [decide_eq_true_eq]
    -- Need: gpow α_z = (gpow α_z * (y ^ val c)⁻¹) * y ^ val c
    rw [inv_mul_cancel_right]
  sim_distribution n w y c hrel f := by
    -- Real: E_{α_t}[f(gpow α_t, α_t + w * c)]
    -- Sim:  E_{α_z}[f(gpow α_z * (y ^ val c)⁻¹, α_z)]
    -- The map α_t ↦ α_t + w * c is a bijection on ZMod q,
    -- so α_z := α_t + w * c is uniform when α_t is uniform.
    change C.gpow n w = y at hrel
    -- Reindex: α_t ↦ α_z = α_t + w * c (bijection on ZMod q)
    let σ : ZMod (C.order n) ≃ ZMod (C.order n) :=
      { toFun := fun α_t => α_t + w * c
        invFun := fun α_z => α_z - w * c
        left_inv := fun α_t => by ring
        right_inv := fun α_z => by ring }
    -- After reindexing by σ, the real distribution becomes:
    -- E_{α_z}[f(gpow(α_z - w*c), α_z)]
    -- which equals the simulated distribution since
    -- gpow(α_z - w*c) = gpow α_z * (y ^ val c)⁻¹
    -- Both sides are uniform averages over ZMod q.
    -- We show the functions agree pointwise after reindexing
    -- by σ : α_t ↦ α_t + w*c.
    -- The key: f(gpow α_t, α_t + w*c) = f(gpow(σ⁻¹(σ α_t)), σ(α_t))
    -- After summing over α_t vs α_z = σ(α_t), both give the same sum.
    simp only [Cslib.Probability.uniformExpect_eq]
    congr 1
    apply Finset.sum_equiv σ (by simp) (fun α_t _ => by
      simp only [σ, Equiv.coe_fn_mk]
      congr 1
      apply Prod.ext
      · -- gpow(α_t + w*c) * (y ^ val c)⁻¹ = gpow α_t
        rw [show (C.gpow n (α_t + w * c) * (y ^ ZMod.val c)⁻¹, α_t + w * c).1 =
          C.gpow n (α_t + w * c) * (y ^ ZMod.val c)⁻¹ from rfl,
          show (C.gpow n α_t, α_t + w * c).1 = C.gpow n α_t from rfl,
          C.gpow_add, C.gpow_mul' n w c, hrel, mul_inv_cancel_right]
      · -- α_t + w * c = σ(α_t)
        rfl)

/-- Schnorr has `1/|G|`-unpredictable commitments (since `g^r` is uniform). -/
theorem schnorr_unpredictable (C : CyclicGroupFamily) :
    (SchnorrProtocol C).UnpredictableCommitments
      (fun n => 1 / Fintype.card (C.Group n)) := by
  intro n _w _y t₀ _hw
  have h := schnorr_commitUniform C n (fun t => if t = t₀ then 1 else 0)
  simp only [] at h
  rw [h]
  simp only [Cslib.Probability.uniformExpect_eq, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  ring_nf
  exact le_refl _

/-- The **Schnorr signature scheme**: the Fiat-Shamir transform
applied to the Schnorr protocol.

- **Key generation**: sample `α ← ZMod q`, set `pk = g^α`, `sk = α`
- **Sign**: sample `α_t ← ZMod q`, compute `u_t = g^α_t`,
  `c = H(m, u_t)`, `α_z = α_t + α · c`, output `(u_t, α_z)`
- **Verify**: compute `c = H(m, u_t)`, check `g^α_z = u_t · pk^c` -/
noncomputable def SchnorrSignature (C : CyclicGroupFamily)
    (Message : ℕ → Type)
    [∀ n, DecidableEq (Message n)]
    (H : ∀ n, Message n → C.Group n → ZMod (C.order n)) :
    SignatureScheme where
  PublicKey n := C.Group n
  SecretKey n := ZMod (C.order n)
  Message := Message
  Signature n := C.Group n × ZMod (C.order n)
  Randomness n := ZMod (C.order n)
  publicKeyFintype := C.fintypeInst
  secretKeyFintype := fun n => CyclicGroupFamily.zmodFintype C n
  publicKeyNonempty := C.nonemptyInst
  secretKeyNonempty := fun n => CyclicGroupFamily.zmodNonempty C n
  randomnessFintype := fun n => CyclicGroupFamily.zmodFintype C n
  randomnessNonempty := fun n => CyclicGroupFamily.zmodNonempty C n
  KeyGenRandomness n := ZMod (C.order n)
  keyGenRandomnessFintype := fun n => CyclicGroupFamily.zmodFintype C n
  keyGenRandomnessNonempty := fun n => CyclicGroupFamily.zmodNonempty C n
  keyGen n α := (C.gpow n α, α)
  sign n sk m α_t :=
    let u_t := C.gpow n α_t
    let c := H n m u_t
    let α_z := α_t + sk * c
    (u_t, α_z)
  verify n pk m sig :=
    let (u_t, α_z) := sig
    let c := H n m u_t
    decide (C.gpow n α_z = u_t * pk ^ (ZMod.val c))

/-- The Schnorr signature scheme is **correct**: honestly generated
signatures always verify.

This follows directly from the completeness of the Schnorr protocol
(the verification equation `g^(α_t + α·c) = g^α_t · (g^α)^c`). -/
theorem SchnorrSignature.correct (C : CyclicGroupFamily)
    (Message : ℕ → Type) [∀ n, DecidableEq (Message n)]
    (H : ∀ n, Message n → C.Group n → ZMod (C.order n)) :
    (SchnorrSignature C Message H).Correct := by
  intro n α m r
  simp only [SchnorrSignature, decide_eq_true_eq]
  rw [C.gpow_add, C.gpow_mul' n α _]

/-- The direct `SchnorrSignature` equals the `FiatShamirSignature`
transform applied to the Schnorr Sigma protocol with `keyOf = gpow`. -/
theorem SchnorrSignature_eq_FiatShamir (C : CyclicGroupFamily)
    (Message : ℕ → Type) [∀ n, DecidableEq (Message n)]
    (H : ∀ n, Message n → C.Group n → ZMod (C.order n)) :
    SchnorrSignature C Message H =
      FiatShamirSignature (SchnorrProtocol C) Message H (SchnorrRelation.keyGen C) := by
  rfl

end
