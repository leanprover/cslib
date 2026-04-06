/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Protocols.PerfectSecrecy.Encryption
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

@[expose] public section

/-!
# Perfect Secrecy: Definitions

Core definitions for perfect secrecy following [KatzLindell2020], Chapter 2.

## Main definitions

- `Cslib.Crypto.Protocols.PerfectSecrecy.EncScheme.ciphertextDist`:
  ciphertext distribution for a given message
- `Cslib.Crypto.Protocols.PerfectSecrecy.EncScheme.jointDist`:
  joint (message, ciphertext) distribution given a message prior
- `Cslib.Crypto.Protocols.PerfectSecrecy.EncScheme.marginalCiphertextDist`:
  marginal ciphertext distribution given a message prior
- `Cslib.Crypto.Protocols.PerfectSecrecy.EncScheme.posteriorMsgProb`:
  posterior probability `Pr[M = m | C = c]`
- `Cslib.Crypto.Protocols.PerfectSecrecy.EncScheme.posteriorMsgDist`:
  posterior message distribution as a `PMF` (defined in the internal file)
- `Cslib.Crypto.Protocols.PerfectSecrecy.EncScheme.PerfectlySecret`:
  perfect secrecy ([KatzLindell2020], Definition 2.3)
- `Cslib.Crypto.Protocols.PerfectSecrecy.EncScheme.CiphertextIndist`:
  ciphertext indistinguishability ([KatzLindell2020], Lemma 2.5)
-/

namespace Cslib.Crypto.Protocols.PerfectSecrecy.EncScheme

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

-- TODO: posteriorMsgProb is itself a distribution — define it as a PMF
-- (see posteriorMsgDist in Internal/PerfectSecrecy.lean) and express
-- PerfectlySecret in terms of equality of distributions.
/-- Posterior probability `Pr[M = m | C = c]`. -/
noncomputable def posteriorMsgProb (scheme : EncScheme M K C)
    (msgDist : PMF M) (c : C) (m : M) : ENNReal :=
  scheme.jointDist msgDist (m, c) / scheme.marginalCiphertextDist msgDist c

/-- An encryption scheme is perfectly secret if `Pr[M = m | C = c] = Pr[M = m]`
for every prior, message, and ciphertext with positive probability
([KatzLindell2020], Definition 2.3). -/
def PerfectlySecret (scheme : EncScheme M K C) : Prop :=
  ∀ (msgDist : PMF M) (m : M) (c : C),
    c ∈ (scheme.marginalCiphertextDist msgDist).support →
    scheme.posteriorMsgProb msgDist c m = msgDist m

/-- Ciphertext indistinguishability: the ciphertext distribution is the same
for all messages ([KatzLindell2020], Lemma 2.5). -/
def CiphertextIndist (scheme : EncScheme M K C) : Prop :=
  ∀ m₀ m₁ : M, scheme.ciphertextDist m₀ = scheme.ciphertextDist m₁

end Cslib.Crypto.Protocols.PerfectSecrecy.EncScheme
