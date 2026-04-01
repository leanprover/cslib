/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Cryptography.PerfectSecrecy.Encryption
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

@[expose] public section

/-!
# Perfect Secrecy: Definitions

Core definitions for perfect secrecy following [KatzLindell2021], Chapter 2.

## Main definitions

- `Cslib.Cryptography.PerfectSecrecy.EncScheme.ciphertextDist`:
  ciphertext distribution for a given message
- `Cslib.Cryptography.PerfectSecrecy.EncScheme.jointDist`:
  joint (message, ciphertext) distribution given a message prior
- `Cslib.Cryptography.PerfectSecrecy.EncScheme.marginalCiphertextDist`:
  marginal ciphertext distribution given a message prior
- `Cslib.Cryptography.PerfectSecrecy.EncScheme.posteriorMsgProb`:
  posterior probability `Pr[M = m | C = c]`
- `Cslib.Cryptography.PerfectSecrecy.EncScheme.PerfectlySecret`:
  perfect secrecy ([KatzLindell2021], Definition 2.3)
-/

namespace Cslib.Cryptography.PerfectSecrecy.EncScheme

universe u
variable {M K C : Type u}

/-- The distribution of `Enc_K(m)` when `K ← Gen`. -/
noncomputable def ciphertextDist (scheme : EncScheme M K C) (m : M) : PMF C := do
  let k ← scheme.gen
  scheme.enc k m

/-- Joint distribution of `(M, C)` given a message prior. -/
noncomputable def jointDist (scheme : EncScheme M K C) (msgDist : PMF M) : PMF (M × C) := do
  let m ← msgDist
  let c ← scheme.ciphertextDist m
  pure (m, c)

/-- Marginal ciphertext distribution given a message prior. -/
noncomputable def marginalCiphertextDist (scheme : EncScheme M K C)
    (msgDist : PMF M) : PMF C := do
  let m ← msgDist
  scheme.ciphertextDist m

/-- Posterior probability `Pr[M = m | C = c]`. -/
noncomputable def posteriorMsgProb (scheme : EncScheme M K C)
    (msgDist : PMF M) (c : C) (m : M) : ENNReal :=
  scheme.jointDist msgDist (m, c) / scheme.marginalCiphertextDist msgDist c

/-- An encryption scheme is perfectly secret if `Pr[M = m | C = c] = Pr[M = m]`
for every prior, message, and ciphertext with positive probability
([KatzLindell2021], Definition 2.3). -/
def PerfectlySecret (scheme : EncScheme M K C) : Prop :=
  ∀ (msgDist : PMF M) (m : M) (c : C),
    c ∈ (scheme.marginalCiphertextDist msgDist).support →
    scheme.posteriorMsgProb msgDist c m = msgDist m

end Cslib.Cryptography.PerfectSecrecy.EncScheme
