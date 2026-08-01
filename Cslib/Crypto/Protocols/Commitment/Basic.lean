/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Protocols.Commitment.Defs

/-!
# Commitment Schemes

Basic results about information-theoretic commitment schemes.

## Main results

- `Scheme.perfectlyHiding_iff_statisticallyHiding_zero`: perfect hiding is
  statistical hiding with zero error
- `Scheme.subsingleton_of_perfectlyHiding_of_perfectlyBinding`: a scheme
  cannot be both perfectly hiding and perfectly binding unless any two
  messages are equal
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.Commitment.Scheme

open scoped NNReal

variable {Message Commitment Opening : Type*}

/-- Perfect hiding is exactly statistical hiding with zero error. -/
theorem perfectlyHiding_iff_statisticallyHiding_zero
    [Fintype Commitment] (scheme : Scheme Message Commitment Opening) :
    scheme.PerfectlyHiding ↔ scheme.StatisticallyHiding 0 := by
  simp [PerfectlyHiding, StatisticallyHiding]

/-- Enlarging the permitted error preserves statistical hiding. -/
theorem StatisticallyHiding.mono [Fintype Commitment]
    {scheme : Scheme Message Commitment Opening} {ε δ : ℝ≥0}
    (h : scheme.StatisticallyHiding ε) (hεδ : ε ≤ δ) :
    scheme.StatisticallyHiding δ :=
  fun message₀ message₁ => (h message₀ message₁).mono hεδ

/-- A scheme cannot be both perfectly hiding and perfectly binding unless any
two messages are equal. -/
theorem subsingleton_of_perfectlyHiding_of_perfectlyBinding
    (scheme : Scheme Message Commitment Opening)
    (hhide : scheme.PerfectlyHiding) (hbind : scheme.PerfectlyBinding) :
    Subsingleton Message := by
  refine ⟨fun message₀ message₁ => ?_⟩
  obtain ⟨commitment, hcommitment⟩ :=
    (scheme.commitmentDist message₀).support_nonempty
  obtain ⟨opening₀, hpair₀⟩ :=
    scheme.mem_support_commitmentDist_iff.mp hcommitment
  rw [hhide message₀ message₁] at hcommitment
  obtain ⟨opening₁, hpair₁⟩ :=
    scheme.mem_support_commitmentDist_iff.mp hcommitment
  exact hbind commitment message₀ opening₀ message₁ opening₁
    (scheme.accepts_of_mem_support hpair₀) (scheme.accepts_of_mem_support hpair₁)

end Cslib.Crypto.Protocols.Commitment.Scheme
