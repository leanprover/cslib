/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Protocols.PerfectSecrecy.Encryption
public import Cslib.Probability.PMF
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

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
- `Cslib.Crypto.Protocols.PerfectSecrecy.EncScheme.posteriorMsgDist`:
  posterior message distribution `Pr[M | C = c]` as a `PMF`
- `Cslib.Crypto.Protocols.PerfectSecrecy.EncScheme.PerfectlySecret`:
  perfect secrecy ([KatzLindell2020], Definition 2.3)
- `Cslib.Crypto.Protocols.PerfectSecrecy.EncScheme.CiphertextIndist`:
  ciphertext indistinguishability ([KatzLindell2020], Lemma 2.5)
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.PerfectSecrecy.EncScheme

universe u
variable {M K C : Type u}

/-- The distribution of `Enc_K(m)` when `K ← Gen`. -/
noncomputable def ciphertextDist (scheme : EncScheme M K C) (m : M) : PMF C := do
  scheme.enc (← scheme.gen) m

/-- Joint distribution of `(M, C)` given a message prior. -/
noncomputable def jointDist (scheme : EncScheme M K C) (msgDist : PMF M) : PMF (M × C) := do
  let m ← msgDist
  return (m, ← scheme.ciphertextDist m)

/-- Marginal ciphertext distribution given a message prior. -/
noncomputable def marginalCiphertextDist (scheme : EncScheme M K C)
    (msgDist : PMF M) : PMF C := do
  scheme.ciphertextDist (← msgDist)

/-- The posterior message distribution `Pr[M | C = c]` as a probability
distribution, given a message prior and a ciphertext in the support of
the marginal distribution. -/
noncomputable def posteriorMsgDist (scheme : EncScheme M K C)
    (msgDist : PMF M) (c : C)
    (hc : c ∈ (scheme.marginalCiphertextDist msgDist).support) : PMF M :=
  Cslib.Probability.PMF.posteriorDist msgDist scheme.ciphertextDist c hc

@[simp]
theorem posteriorMsgDist_apply (scheme : EncScheme M K C)
    (msgDist : PMF M) (c : C)
    (hc : c ∈ (scheme.marginalCiphertextDist msgDist).support) (m : M) :
    scheme.posteriorMsgDist msgDist c hc m =
      scheme.jointDist msgDist (m, c) / scheme.marginalCiphertextDist msgDist c :=
  rfl

/-- An encryption scheme is perfectly secret if the posterior message
distribution equals the prior for every ciphertext with positive probability
([KatzLindell2020], Definition 2.3). -/
def PerfectlySecret (scheme : EncScheme M K C) : Prop :=
  ∀ (msgDist : PMF M) (c : C)
    (hc : c ∈ (scheme.marginalCiphertextDist msgDist).support),
    scheme.posteriorMsgDist msgDist c hc = msgDist

/-- Ciphertext indistinguishability: the ciphertext distribution is the same
for all messages ([KatzLindell2020], Lemma 2.5). -/
def CiphertextIndist (scheme : EncScheme M K C) : Prop :=
  ∀ m₀ m₁ : M, scheme.ciphertextDist m₀ = scheme.ciphertextDist m₁

end Cslib.Crypto.Protocols.PerfectSecrecy.EncScheme
