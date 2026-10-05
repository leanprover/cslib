/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Protocols.PerfectSecrecy.Encryption

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
  posterior message distribution `Pr[M | C = c]` as a regular conditional kernel
- `Cslib.Crypto.Protocols.PerfectSecrecy.EncScheme.PerfectlySecret`:
  perfect secrecy ([KatzLindell2020], Definition 2.3)
- `Cslib.Crypto.Protocols.PerfectSecrecy.EncScheme.CiphertextIndist`:
  ciphertext indistinguishability ([KatzLindell2020], Lemma 2.5)
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.PerfectSecrecy.EncScheme

open MeasureTheory ProbabilityTheory

variable {M K C : Type*} [MeasurableSpace M] [MeasurableSpace K] [MeasurableSpace C]

/-- The encryption channel, after sampling the key independently of the message. -/
noncomputable def ciphertextKernel (scheme : EncScheme M K C) : Kernel M C :=
  scheme.enc ∘ₖ (Kernel.const M scheme.gen ×ₖ Kernel.id)

instance (scheme : EncScheme M K C) : IsMarkovKernel scheme.ciphertextKernel := by
  unfold ciphertextKernel
  infer_instance

/-- The distribution of `Enc_K(m)` when `K ← Gen`. -/
noncomputable def ciphertextDist (scheme : EncScheme M K C) (m : M) : Measure C :=
  scheme.ciphertextKernel m

/-- The encryption channel at a message integrates encryption over the generated key. -/
theorem ciphertextDist_eq_comp (scheme : EncScheme M K C) (m : M) :
    scheme.ciphertextDist m =
      scheme.enc.comap (fun key => (key, m)) measurable_prodMk_right ∘ₘ scheme.gen := by
  simp only [ciphertextDist, ciphertextKernel, Kernel.comp_apply, Kernel.prod_apply,
    Kernel.const_apply, Kernel.id_apply, Measure.prod_dirac, Kernel.coe_comap]
  exact Measure.bind_map measurable_prodMk_right.aemeasurable scheme.enc.aemeasurable

instance (scheme : EncScheme M K C) (m : M) :
    IsProbabilityMeasure (scheme.ciphertextDist m) := by
  unfold ciphertextDist
  infer_instance

/-- Joint distribution of messages and ciphertexts given a message prior. -/
noncomputable abbrev jointDist (scheme : EncScheme M K C) (msgDist : Measure M) : Measure (M × C) :=
  msgDist ⊗ₘ scheme.ciphertextKernel

/-- Marginal ciphertext distribution given a message prior. -/
noncomputable abbrev marginalCiphertextDist (scheme : EncScheme M K C)
    (msgDist : Measure M) : Measure C :=
  scheme.ciphertextKernel ∘ₘ msgDist

/-- Mathlib's regular conditional distribution on messages given the ciphertext. -/
noncomputable abbrev posteriorMsgDist [StandardBorelSpace M] [Nonempty M]
    (scheme : EncScheme M K C) (msgDist : Measure M) [IsProbabilityMeasure msgDist] :
    Kernel C M :=
  posterior scheme.ciphertextKernel msgDist

/-- Messages and ciphertexts are independent for every probability prior.
This formulation of perfect secrecy also applies to continuous distributions
([KatzLindell2020], Definition 2.3). -/
def PerfectlySecret (scheme : EncScheme M K C) : Prop :=
  ∀ (msgDist : Measure M) [IsProbabilityMeasure msgDist],
    scheme.jointDist msgDist = msgDist.prod (scheme.marginalCiphertextDist msgDist)

/-- Ciphertext indistinguishability: the ciphertext distribution is the same
for all messages ([KatzLindell2020], Lemma 2.5). -/
def CiphertextIndist (scheme : EncScheme M K C) : Prop :=
  ∀ m₀ m₁ : M, scheme.ciphertextDist m₀ = scheme.ciphertextDist m₁

end Cslib.Crypto.Protocols.PerfectSecrecy.EncScheme
