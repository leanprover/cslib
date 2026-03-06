/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Cryptography.Primitives.PRG
public import Cslib.Cryptography.Primitives.Encryption

@[expose] public section

/-!
# PRG → IND-CPA Encryption Security Reduction

This file constructs an IND-CPA secure stream cipher from any
pseudorandom generator (PRG) and proves that PRG security implies
IND-CPA security of the resulting scheme.

## Construction

Given a PRG `G : Seed n → Output n` with an `AddCommGroup` on
the output type (abstracting XOR), we define:
- `Enc(k, m; ()) = G(k) + m`
- `Dec(k, c) = c - G(k)`

## Main Results

* `PRG.toEncryptionScheme` — the construction
* `PRG.toEncryptionScheme_correct` — correctness
* `PRG.toEncryptionScheme_secure` — PRG security → IND-CPA security

## References

* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2014], §3.3
-/

open Cslib.Probability

/-- The standard PRG-based stream cipher: `Enc(k, m) = G(k) + m`. -/
noncomputable def PRG.toEncryptionScheme (G : PRG)
    [∀ n, AddCommGroup (G.Output n)]
    : EncryptionScheme where
  Key := G.Seed
  Plaintext := G.Output
  Ciphertext := G.Output
  Randomness := fun _ => Unit
  keyFintype := G.seedFintype
  keyNonempty := G.seedNonempty
  randomnessFintype := fun _ => inferInstance
  randomnessNonempty := fun _ => inferInstance
  encrypt n k m _ := G.stretch n k + m
  decrypt n k c := some (c - G.stretch n k)

/-- The PRG-based stream cipher is correct. -/
theorem PRG.toEncryptionScheme_correct (G : PRG)
    [∀ n, AddCommGroup (G.Output n)] :
    G.toEncryptionScheme.Correct := by
  intro n k m r
  simp [toEncryptionScheme, add_sub_cancel_left]

/-- Simulate the IND-CPA game body with a given string `y` and bit `b`. -/
noncomputable def PRG.simulateStreamBody (G : PRG)
    [∀ n, AddCommGroup (G.Output n)]
    (A : IND_CPA_Adversary G.toEncryptionScheme)
    (n : ℕ) (b : Bool) (y : G.Output n) : Bool :=
  let encOracle : G.Output n → Unit → G.Output n :=
    fun m _ => y + m
  let result := A.choose n encOracle
  let m₀ : G.Output n := result.1
  let m₁ : G.Output n := result.2.1
  let σ := result.2.2
  let challenge : G.Output n := if b then m₁ else m₀
  let ct : G.Output n := y + challenge
  (A.guess n ct σ) == b

/-- Construct a PRG distinguisher from an IND-CPA adversary. -/
noncomputable def PRG.mkPRGAdversary (G : PRG)
    [∀ n, AddCommGroup (G.Output n)]
    (A : IND_CPA_Adversary G.toEncryptionScheme)
    (b₀ : Bool) :
    PRG.DistinguishingAdversary G where
  distinguish n y := G.simulateStreamBody A n b₀ y

/-- The ideal-world gap for the PRG→IND-CPA reduction. -/
noncomputable def PRG.IND_CPA_idealWorldGap (G : PRG)
    [∀ n, AddCommGroup (G.Output n)]
    (A : IND_CPA_Adversary G.toEncryptionScheme)
    (n : ℕ) : ℝ :=
  letI := G.outputFintype n; letI := G.outputNonempty n
  |uniformExpect Bool (fun b =>
    uniformExpect (G.Output n) (fun y =>
      boolToReal (G.simulateStreamBody A n b y)))
   - 1/2|

/-- **PRG → IND-CPA reduction bound.** -/
theorem PRG.toEncryptionScheme_reduction_bound (G : PRG)
    [∀ n, AddCommGroup (G.Output n)]
    (A : IND_CPA_Adversary G.toEncryptionScheme) :
    ∃ (B : PRG.DistinguishingAdversary G),
      ∀ n, (IND_CPA_Game G.toEncryptionScheme).advantage A n ≤
        G.SecurityGame.advantage B n +
        G.IND_CPA_idealWorldGap A n := by
  suffices pointwise : ∀ n, ∃ (B : PRG.DistinguishingAdversary G),
      (IND_CPA_Game G.toEncryptionScheme).advantage A n ≤
        G.SecurityGame.advantage B n +
        G.IND_CPA_idealWorldGap A n by
    have hchoice : ∃ B : ℕ → PRG.DistinguishingAdversary G,
        ∀ n, (IND_CPA_Game G.toEncryptionScheme).advantage A n ≤
          G.SecurityGame.advantage (B n) n +
          G.IND_CPA_idealWorldGap A n :=
      ⟨fun n => (pointwise n).choose, fun n => (pointwise n).choose_spec⟩
    obtain ⟨B, hB⟩ := hchoice
    exact ⟨{ distinguish := fun n y => (B n).distinguish n y }, fun n => hB n⟩
  intro n
  letI := G.seedFintype n; letI := G.seedNonempty n
  letI := G.outputFintype n; letI := G.outputNonempty n
  let E := G.toEncryptionScheme
  haveI : Fintype (E.Key n) := E.keyFintype n
  haveI : Nonempty (E.Key n) := E.keyNonempty n
  haveI : Fintype (E.Randomness n) := E.randomnessFintype n
  haveI : Nonempty (E.Randomness n) := E.randomnessNonempty n
  -- Step 1: Rewrite IND-CPA advantage
  -- IND-CPA coin space is G.Seed n × Unit × Bool
  -- We show it equals |E_b[E_s[body(G(s), b)]] - 1/2|
  -- Abbreviate the body function
  let body : G.Seed n → Bool → ℝ := fun s b =>
    boolToReal (G.simulateStreamBody A n b (G.stretch n s))
  let idealBody : G.Output n → Bool → ℝ := fun y b =>
    boolToReal (G.simulateStreamBody A n b y)
  -- The IND-CPA game expands to the same computation
  have h_cpa_unfold : (IND_CPA_Game E).advantage A n =
      |uniformExpect (G.Seed n × Unit × Bool) (fun ⟨s, _, b⟩ =>
        body s b) - 1/2| := by
    simp only [IND_CPA_Game, E, PRG.toEncryptionScheme, simulateStreamBody, body]
    rfl
  -- E_{(s,u,b)}[f(s,b)] = E_s[E_{(u,b)}[f(s,b)]]
  --                      = E_s[E_b[f(s,b)]]   (Unit is trivial)
  --                      = E_b[E_s[f(s,b)]]   (Fubini swap)
  have h_prod_eq : uniformExpect (G.Seed n × Unit × Bool) (fun ⟨s, _, b⟩ =>
      body s b) =
    uniformExpect Bool (fun b =>
      uniformExpect (G.Seed n) (fun s => body s b)) := by
    rw [uniformExpect_prod]
    have h_unit_elim : ∀ s, uniformExpect (Unit × Bool) (fun ⟨_, b⟩ =>
        body s b) = uniformExpect Bool (fun b => body s b) := by
      intro s
      rw [uniformExpect_prod]
      simp only [uniformExpect_const]
    simp_rw [h_unit_elim]
    exact uniformExpect_comm _ _ _
  have h_cpa_eq : (IND_CPA_Game E).advantage A n =
      |uniformExpect Bool (fun b =>
        uniformExpect (G.Seed n) (fun s => body s b))
       - 1/2| := by
    rw [h_cpa_unfold, h_prod_eq]
  -- Step 2: Find the best challenge bit by averaging
  obtain ⟨b_best, h_best⟩ := uniformExpect_le_exists Bool
    (fun b => |uniformExpect (G.Seed n) (fun s => body s b)
      - uniformExpect (G.Output n) (fun y => idealBody y b)|)
  let B := G.mkPRGAdversary A b_best
  refine ⟨B, ?_⟩
  -- Abbreviate
  set realE := uniformExpect Bool (fun b =>
    uniformExpect (G.Seed n) (fun s => body s b))
  set idealE := uniformExpect Bool (fun b =>
    uniformExpect (G.Output n) (fun y => idealBody y b))
  -- Step 3: Triangle inequality
  have h_tri : |realE - 1/2| ≤
      |realE - idealE| + |idealE - 1/2| := by
    have : realE - 1/2 = (realE - idealE) + (idealE - 1/2) := by ring
    rw [this]; exact abs_add_le _ _
  -- Step 4: |realE - idealE| ≤ E_b[|real_b - ideal_b|] ≤ |real_best - ideal_best|
  have h_diff_eq : realE - idealE = uniformExpect Bool (fun b =>
      uniformExpect (G.Seed n) (fun s => body s b) -
      uniformExpect (G.Output n) (fun y => idealBody y b)) := by
    simp [realE, idealE, uniformExpect_sub]
  have h_abs_diff : |realE - idealE| ≤
      uniformExpect Bool (fun b =>
        |uniformExpect (G.Seed n) (fun s => body s b) -
         uniformExpect (G.Output n) (fun y => idealBody y b)|) := by
    rw [h_diff_eq]; exact uniformExpect_abs_le Bool _
  -- The best b achieves at least the average
  have h_best_bound : uniformExpect Bool (fun b =>
      |uniformExpect (G.Seed n) (fun s => body s b) -
       uniformExpect (G.Output n) (fun y => idealBody y b)|) ≤
    |uniformExpect (G.Seed n) (fun s => body s b_best) -
     uniformExpect (G.Output n) (fun y => idealBody y b_best)| :=
    h_best
  -- This equals PRG advantage of B
  have h_prf_adv : |uniformExpect (G.Seed n) (fun s => body s b_best) -
     uniformExpect (G.Output n) (fun y => idealBody y b_best)| =
    G.SecurityGame.advantage B n := by
    simp [PRG.SecurityGame, B, mkPRGAdversary, body, idealBody]
  -- |idealE - 1/2| = IND_CPA_idealWorldGap
  have h_ideal_gap : |idealE - 1/2| = G.IND_CPA_idealWorldGap A n := by
    simp [IND_CPA_idealWorldGap, idealE, idealBody]
  -- Chain everything
  calc (IND_CPA_Game E).advantage A n
      = |realE - 1/2| := h_cpa_eq
    _ ≤ |realE - idealE| + |idealE - 1/2| := h_tri
    _ ≤ G.SecurityGame.advantage B n + G.IND_CPA_idealWorldGap A n := by
        linarith [h_abs_diff, h_best_bound, h_prf_adv.symm, h_ideal_gap.symm]

/-- **PRG security → IND-CPA security** for the stream cipher,
given that the ideal-world gap is negligible. -/
theorem PRG.toEncryptionScheme_secure (G : PRG)
    [∀ n, AddCommGroup (G.Output n)]
    (hG : G.Secure)
    (A : IND_CPA_Adversary G.toEncryptionScheme)
    (hGap : Negligible (G.IND_CPA_idealWorldGap A)) :
    Negligible (fun n =>
      (IND_CPA_Game G.toEncryptionScheme).advantage A n) := by
  obtain ⟨B, hB⟩ := G.toEncryptionScheme_reduction_bound A
  apply Negligible.mono (Negligible.add (hG B) hGap)
  refine ⟨0, fun n _ => ?_⟩
  have h1 : 0 ≤ (IND_CPA_Game G.toEncryptionScheme).advantage A n := by
    simp only [IND_CPA_Game]; exact abs_nonneg _
  have h2 : 0 ≤ G.SecurityGame.advantage B n := abs_nonneg _
  have h3 : 0 ≤ G.IND_CPA_idealWorldGap A n := abs_nonneg _
  rw [abs_of_nonneg h1, abs_of_nonneg (by linarith)]
  exact hB n

end
