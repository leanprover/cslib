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

The main result is the hiding–binding trade-off: a perfectly binding scheme
places the commitment distributions of distinct messages at the maximum
statistical distance, so it cannot be statistically hiding for any error below
one. Hiding and binding can therefore not both hold unconditionally; real
schemes make at most one side information-theoretic and settle for a
computational version of the other.

## Main results

- `Scheme.subsingleton_of_statisticallyHiding_of_perfectlyBinding`: a scheme
  cannot be both statistically hiding with error below one and perfectly
  binding unless any two messages are equal
- `Scheme.PerfectlyBinding.statisticalDistance_commitmentDist_eq_one`: perfect
  binding forces distinct messages' commitment distributions to the maximum
  statistical distance
- `Scheme.subsingleton_of_perfectlyHiding_of_perfectlyBinding`: the perfect
  hiding case, with no finiteness assumption on commitments
- `Scheme.perfectlyHiding_iff_statisticallyHiding_zero`: perfect hiding is
  statistical hiding with zero error
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.Commitment.Scheme

open Cslib.Probability.PMF
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

/-- Distinct messages of a perfectly binding scheme have disjoint sets of
possible commitments. -/
theorem PerfectlyBinding.disjoint_support_commitmentDist
    {scheme : Scheme Message Commitment Opening} (hbind : scheme.PerfectlyBinding)
    {message₀ message₁ : Message} (hne : message₀ ≠ message₁) :
    Disjoint (scheme.commitmentDist message₀).support
      (scheme.commitmentDist message₁).support := by
  rw [Set.disjoint_left]
  intro commitment h₀ h₁
  obtain ⟨opening₀, hpair₀⟩ := scheme.mem_support_commitmentDist_iff.mp h₀
  obtain ⟨opening₁, hpair₁⟩ := scheme.mem_support_commitmentDist_iff.mp h₁
  exact hne (hbind commitment message₀ opening₀ message₁ opening₁
    (scheme.accepts_of_mem_support hpair₀) (scheme.accepts_of_mem_support hpair₁))

/-- In a perfectly binding scheme, the commitment distributions of distinct
messages are at the maximum statistical distance: an unbounded observer can
read the message off the commitment. -/
theorem PerfectlyBinding.statisticalDistance_commitmentDist_eq_one
    [Fintype Commitment] {scheme : Scheme Message Commitment Opening}
    (hbind : scheme.PerfectlyBinding) {message₀ message₁ : Message}
    (hne : message₀ ≠ message₁) :
    statisticalDistance (scheme.commitmentDist message₀)
      (scheme.commitmentDist message₁) = 1 :=
  statisticalDistance_eq_one_of_disjoint_support (hbind.disjoint_support_commitmentDist hne)

/-- **The hiding–binding trade-off.** A scheme cannot be both statistically
hiding with error below one and perfectly binding unless any two messages are
equal. The error bound is sharp: statistical hiding with error one holds
vacuously for every scheme. -/
theorem subsingleton_of_statisticallyHiding_of_perfectlyBinding
    [Fintype Commitment] (scheme : Scheme Message Commitment Opening) {ε : ℝ≥0}
    (hε : ε < 1) (hhide : scheme.StatisticallyHiding ε)
    (hbind : scheme.PerfectlyBinding) : Subsingleton Message := by
  refine ⟨fun message₀ message₁ => ?_⟩
  by_contra hne
  have hone := hbind.statisticalDistance_commitmentDist_eq_one hne
  have hle : statisticalDistance (scheme.commitmentDist message₀)
      (scheme.commitmentDist message₁) ≤ (ε : ℝ) := hhide message₀ message₁
  rw [hone] at hle
  exact absurd hle (by exact_mod_cast hε.not_ge)

/-- A scheme cannot be both perfectly hiding and perfectly binding unless any
two messages are equal. Unlike the statistical version, this needs no
finiteness assumption on the commitment type. -/
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
