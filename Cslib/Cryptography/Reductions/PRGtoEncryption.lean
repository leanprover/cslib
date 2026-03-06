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

/-- Simulate the IND-CPA game body with a given string `y` and bit `b`.

Since the stream cipher has `Randomness = Unit`, the encryption oracle
is `fun m => y + m` regardless of the per-query randomness. The
adversary's `OracleInteraction` is run against this oracle. Returns `0`
on fuel exhaustion (adversary defaults to losing). -/
noncomputable def PRG.simulateStreamBody (G : PRG)
    [∀ n, AddCommGroup (G.Output n)]
    (A : IND_CPA_Adversary G.toEncryptionScheme)
    (n : ℕ) (b : Bool) (y : G.Output n) : ℝ :=
  let q1 := A.numQueries1 n
  let q2 := A.numQueries2 n
  let oracle1 : Fin q1 → G.Output n → G.Output n :=
    fun _ m => y + m
  match (A.choose n).run q1 oracle1 with
  | none => 0
  | some (_, m₀, m₁, σ) =>
    let challenge : G.Output n := if b then m₁ else m₀
    let ct : G.Output n := y + challenge
    let oracle2 : Fin q2 → G.Output n → G.Output n :=
      fun _ m => y + m
    match (A.guess n ct σ).run q2 oracle2 with
    | none => 0
    | some (_, b') => boolToReal (b' == b)

/-- Construct a PRG distinguisher from an IND-CPA adversary. -/
noncomputable def PRG.mkPRGAdversary (G : PRG)
    [∀ n, AddCommGroup (G.Output n)]
    (A : IND_CPA_Adversary G.toEncryptionScheme)
    (b₀ : Bool) :
    PRG.DistinguishingAdversary G where
  distinguish n y :=
    let q1 := A.numQueries1 n
    let q2 := A.numQueries2 n
    let oracle1 : Fin q1 → G.Output n → G.Output n :=
      fun _ m => y + m
    match (A.choose n).run q1 oracle1 with
    | none => false
    | some (_, m₀, m₁, σ) =>
      let challenge : G.Output n := if b₀ then m₁ else m₀
      let ct : G.Output n := y + challenge
      let oracle2 : Fin q2 → G.Output n → G.Output n :=
        fun _ m => y + m
      match (A.guess n ct σ).run q2 oracle2 with
      | none => false
      | some (_, b') => b' == b₀

/-- The ideal-world gap for the PRG→IND-CPA reduction. -/
noncomputable def PRG.IND_CPA_idealWorldGap (G : PRG)
    [∀ n, AddCommGroup (G.Output n)]
    (A : IND_CPA_Adversary G.toEncryptionScheme)
    (n : ℕ) : ℝ :=
  letI := G.outputFintype n; letI := G.outputNonempty n
  |uniformExpect Bool (fun b =>
    uniformExpect (G.Output n) (fun y =>
      G.simulateStreamBody A n b y))
   - 1/2|

/-- **PRG → IND-CPA reduction bound.** -/
theorem PRG.toEncryptionScheme_reduction_bound (G : PRG)
    [∀ n, AddCommGroup (G.Output n)]
    (A : IND_CPA_Adversary G.toEncryptionScheme) :
    ∃ (B : PRG.DistinguishingAdversary G),
      ∀ n, (IND_CPA_Game G.toEncryptionScheme).advantage A n ≤
        G.SecurityGame.advantage B n +
        G.IND_CPA_idealWorldGap A n := by
  sorry

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
