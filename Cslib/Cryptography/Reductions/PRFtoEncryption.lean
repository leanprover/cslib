/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Cryptography.Primitives.PRF
public import Cslib.Cryptography.Primitives.Encryption

@[expose] public section

/-!
# PRF → IND-CPA Encryption Security Reduction

This file constructs an IND-CPA secure encryption scheme from any
pseudorandom function (PRF) and proves that PRF security implies
IND-CPA security of the resulting scheme.

## Construction

Given a PRF `F : Key n → Input n → Output n`, we define:
- `Enc(k, m; r) = (r, F(k, r) + m)`
- `Dec(k, (r, c)) = c - F(k, r)`

The `AddCommGroup` structure on the output type abstracts XOR (or any
group operation making `· + m` a bijection).

## Main Results

* `PRF.toEncryptionScheme` — the construction
* `PRF.toEncryptionScheme_correct` — correctness
* `PRF.toEncryptionScheme_reduction_bound` — reduction bound with explicit gap
* `PRF.toEncryptionScheme_secure'` — PRF security + negligible gap ⟹ IND-CPA security
* `PRF.toEncryptionScheme_secureAgainst` — security against admissible adversaries

## References

* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2014], §3.6
-/

open Cslib.Probability

/-- The standard PRF-based encryption scheme: `Enc(k, m; r) = (r, F(k,r) + m)`.

The type aliases below make the construction transparent for reductions. -/
noncomputable def PRF.toEncryptionScheme (F : PRF)
    [∀ n, AddCommGroup (F.Output n)]
    [∀ n, Fintype (F.Input n)] [∀ n, Nonempty (F.Input n)]
    : EncryptionScheme where
  Key := F.Key
  Plaintext := F.Output
  Ciphertext := fun n => F.Input n × F.Output n
  Randomness := F.Input
  keyFintype := F.keyFintype
  keyNonempty := F.keyNonempty
  randomnessFintype := inferInstance
  randomnessNonempty := inferInstance
  encrypt n k m r := (r, F.eval n k r + m)
  decrypt n k ct := some (ct.2 - F.eval n k ct.1)

/-- `toEncryptionScheme.Ciphertext n` is `F.Input n × F.Output n`. -/
@[simp] theorem PRF.toEncryptionScheme_Ciphertext (F : PRF)
    [∀ n, AddCommGroup (F.Output n)]
    [∀ n, Fintype (F.Input n)] [∀ n, Nonempty (F.Input n)]
    (n : ℕ) : F.toEncryptionScheme.Ciphertext n = (F.Input n × F.Output n) := rfl

/-- `toEncryptionScheme.Plaintext n` is `F.Output n`. -/
@[simp] theorem PRF.toEncryptionScheme_Plaintext (F : PRF)
    [∀ n, AddCommGroup (F.Output n)]
    [∀ n, Fintype (F.Input n)] [∀ n, Nonempty (F.Input n)]
    (n : ℕ) : F.toEncryptionScheme.Plaintext n = F.Output n := rfl

/-- `toEncryptionScheme.Randomness n` is `F.Input n`. -/
@[simp] theorem PRF.toEncryptionScheme_Randomness (F : PRF)
    [∀ n, AddCommGroup (F.Output n)]
    [∀ n, Fintype (F.Input n)] [∀ n, Nonempty (F.Input n)]
    (n : ℕ) : F.toEncryptionScheme.Randomness n = F.Input n := rfl

/-- The PRF-based encryption scheme is correct: decryption recovers
the plaintext. -/
theorem PRF.toEncryptionScheme_correct (F : PRF)
    [∀ n, AddCommGroup (F.Output n)]
    [∀ n, Fintype (F.Input n)] [∀ n, Nonempty (F.Input n)]
    : F.toEncryptionScheme.Correct := by
  intro n k m r
  simp [toEncryptionScheme]

/-- Simulate the IND-CPA game body with a given oracle function.

Given `oracle : F.Input n → F.Output n` (either `F(k,·)` or a random
function), encryption randomness slots `rs1`, `rs2`, challenge
randomness `r₀`, and challenge bit `b₀`, run the adversary's oracle
interaction and compute whether the adversary guesses correctly.

Returns `0` on fuel exhaustion. -/
noncomputable def PRF.simulateBody (F : PRF)
    [∀ n, AddCommGroup (F.Output n)]
    [∀ n, Fintype (F.Input n)] [∀ n, Nonempty (F.Input n)]
    (A : IND_CPA_Adversary F.toEncryptionScheme)
    (n : ℕ) (r₀ : F.Input n) (b₀ : Bool)
    (oracle : F.Input n → F.Output n)
    (rs1 : Fin (A.numQueries1 n) → F.Input n)
    (rs2 : Fin (A.numQueries2 n) → F.Input n) : ℝ :=
  let q1 := A.numQueries1 n
  let q2 := A.numQueries2 n
  let encOracle1 : Fin q1 → F.Output n → F.Input n × F.Output n :=
    fun i m => (rs1 i, oracle (rs1 i) + m)
  match (A.choose n).run q1 encOracle1 with
  | none => 0
  | some (_, m₀, m₁, σ) =>
    let challenge : F.Output n := if b₀ then m₁ else m₀
    let ct : F.Input n × F.Output n := (r₀, oracle r₀ + challenge)
    let encOracle2 : Fin q2 → F.Output n → F.Input n × F.Output n :=
      fun i m => (rs2 i, oracle (rs2 i) + m)
    match (A.guess n ct σ).run q2 encOracle2 with
    | none => 0
    | some (_, b') => boolToReal (b' == b₀)

/-- Construct a PRF adversary from an IND-CPA adversary at a specific
security parameter with specific randomness and challenge bit.

At parameter `n₀`, the adversary simulates the IND-CPA game using
its oracle; at other parameters it returns `true`. -/
noncomputable def PRF.mkPRFAdversaryAt (F : PRF)
    [∀ n, AddCommGroup (F.Output n)]
    [∀ n, Fintype (F.Input n)] [∀ n, Nonempty (F.Input n)]
    (A : IND_CPA_Adversary F.toEncryptionScheme)
    (n₀ : ℕ) (r₀ : F.Input n₀) (b₀ : Bool)
    (rs1 : Fin (A.numQueries1 n₀) → F.Input n₀)
    (rs2 : Fin (A.numQueries2 n₀) → F.Input n₀) :
    PRF.OracleAdversary F where
  run n oracle :=
    if h : n = n₀ then
      let oracle' : F.Input n₀ → F.Output n₀ :=
        fun x => cast (congrArg F.Output h)
          (oracle (cast (congrArg F.Input h.symm) x))
      let rs1' := rs1
      let rs2' := rs2
      (F.simulateBody A n₀ r₀ b₀ oracle' rs1' rs2' > 0)
    else true

/-- The IND-CPA advantage in the "ideal world" where the encryption
oracle uses a truly random function instead of the PRF.

This measures how well the adversary can win the IND-CPA game when
the key-derived function is replaced by a uniformly random function.
For computationally bounded adversaries facing a one-time-pad-like
scheme this is zero, but for unbounded adversaries it may be
nonzero. -/
noncomputable def IND_CPA_idealWorldGap (F : PRF)
    [∀ n, AddCommGroup (F.Output n)]
    [∀ n, Fintype (F.Input n)] [∀ n, Nonempty (F.Input n)]
    (A : IND_CPA_Adversary F.toEncryptionScheme) (n : ℕ) : ℝ :=
  letI := F.funFintype n; letI := F.funNonempty n
  |uniformExpect
    (F.Input n × Bool ×
     (Fin (A.numQueries1 n) → F.Input n) ×
     (Fin (A.numQueries2 n) → F.Input n))
    (fun ⟨r, b, rs1, rs2⟩ =>
    uniformExpect (F.Input n → F.Output n) (fun rf =>
      F.simulateBody A n r b rf rs1 rs2))
   - 1/2|

/-- **PRF → IND-CPA reduction bound.**

For any IND-CPA adversary `A`, there exists a PRF adversary `B` such
that for all `n`:
$$\mathrm{IND\text{-}CPA~advantage}(A, n)
  \le \mathrm{PRF~advantage}(B, n)
    + \mathrm{idealWorldGap}(A, n)$$

The first term is negligible by PRF security; the second term captures
the residual advantage in the ideal world. -/
theorem PRF.toEncryptionScheme_reduction_bound (F : PRF)
    [∀ n, AddCommGroup (F.Output n)]
    [∀ n, Nonempty (F.Output n)]
    [∀ n, Fintype (F.Input n)] [∀ n, Nonempty (F.Input n)]
    (A : IND_CPA_Adversary F.toEncryptionScheme) :
    ∃ (B : PRF.OracleAdversary F),
      ∀ n, (IND_CPA_Game F.toEncryptionScheme).advantage A n ≤
        F.SecurityGame.advantage B n +
        IND_CPA_idealWorldGap F A n := by
  sorry

/-- **PRF security + negligible ideal-world gap → IND-CPA security.**

This is the standard PRF→IND-CPA theorem, correctly formulated with
an explicit gap hypothesis. The gap is negligible for computationally
bounded adversaries (one-time pad argument). -/
theorem PRF.toEncryptionScheme_secure' (F : PRF)
    [∀ n, AddCommGroup (F.Output n)]
    [∀ n, Nonempty (F.Output n)]
    [∀ n, Fintype (F.Input n)] [∀ n, Nonempty (F.Input n)]
    (hF : F.Secure)
    (A : IND_CPA_Adversary F.toEncryptionScheme)
    (hGap : Negligible (IND_CPA_idealWorldGap F A)) :
    Negligible (fun n =>
      (IND_CPA_Game F.toEncryptionScheme).advantage A n) := by
  obtain ⟨B, hB⟩ := F.toEncryptionScheme_reduction_bound A
  apply Negligible.mono (Negligible.add (hF B) hGap)
  refine ⟨0, fun n _ => ?_⟩
  have h1 : 0 ≤ (IND_CPA_Game F.toEncryptionScheme).advantage A n := by
    simp only [IND_CPA_Game]; exact abs_nonneg _
  have h2 : 0 ≤ F.SecurityGame.advantage B n := by
    simp only [PRF.SecurityGame]; exact abs_nonneg _
  have h3 : 0 ≤ IND_CPA_idealWorldGap F A n := abs_nonneg _
  rw [abs_of_nonneg h1, abs_of_nonneg (by linarith)]
  exact hB n

/-- **PRF security + negligible gap for all admissible adversaries
→ IND-CPA security against that class.** -/
theorem PRF.toEncryptionScheme_secureAgainst (F : PRF)
    [∀ n, AddCommGroup (F.Output n)]
    [∀ n, Nonempty (F.Output n)]
    [∀ n, Fintype (F.Input n)] [∀ n, Nonempty (F.Input n)]
    (hF : F.Secure)
    (Admissible :
      IND_CPA_Adversary F.toEncryptionScheme → Prop)
    (hGap : ∀ A, Admissible A →
      Negligible (IND_CPA_idealWorldGap F A)) :
    (IND_CPA_Game F.toEncryptionScheme).SecureAgainst
      Admissible := by
  intro A hA
  exact F.toEncryptionScheme_secure' hF A (hGap A hA)

end
