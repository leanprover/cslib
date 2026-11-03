/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Protocols.Commitment.Scheme
public import Cslib.Probability.StatisticalDistance

/-!
# Commitment Schemes: Information-Theoretic Security

Hiding and binding for commitment schemes, in their information-theoretic forms
([BonehShoup2023], Section 8.12). Perfect hiding: every message yields the same
commitment distribution. Statistical hiding: any two commitment distributions
are within statistical distance `ε`. Perfect binding: no commitment can be
opened to two different messages, even by an unbounded committer.

Each definition is about a single, fixed scheme; statistical hiding carries an
explicit error bound, and the perfect notions have no error at all. The
asymptotic notions in the book — negligible statistical distance for families
of distributions ([BonehShoup2023], Definition 3.6), or security against
efficient adversaries (Section 8.12) — can be layered on top of these later.

## Main definitions

- `Scheme.PerfectlyHiding`: the commitment distributions are equal for every
  pair of messages
- `Scheme.StatisticallyHiding`: the commitment distributions are statistically
  close with error `ε`
- `Scheme.PerfectlyBinding`: no commitment has accepted openings to two
  different messages

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023]
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.Commitment.Scheme

open Cslib.Probability.PMF
open scoped NNReal

variable {Message Commitment Opening : Type*}

/-- A scheme is perfectly hiding when every message yields the same commitment
distribution, so a commitment reveals nothing about the message as long as its
opening is withheld ([BonehShoup2023], Section 8.12). -/
def PerfectlyHiding (scheme : Scheme Message Commitment Opening) : Prop :=
  ∀ message₀ message₁ : Message,
    scheme.commitmentDist message₀ = scheme.commitmentDist message₁

/-- A scheme is statistically hiding with error `ε` when the commitment
distributions of any two messages are within statistical distance `ε`
([BonehShoup2023], Definition 3.5 and Section 8.12). -/
def StatisticallyHiding [Fintype Commitment]
    (scheme : Scheme Message Commitment Opening) (ε : ℝ≥0) : Prop :=
  ∀ message₀ message₁ : Message,
    StatisticallyClose (scheme.commitmentDist message₀)
      (scheme.commitmentDist message₁) ε

/-- A scheme is perfectly binding when a commitment can be opened to at most
one message: any two accepted openings of the same commitment agree on the
message ([BonehShoup2023], Section 8.12). Different openings of the same
message are still allowed. -/
def PerfectlyBinding (scheme : Scheme Message Commitment Opening) : Prop :=
  ∀ commitment message₀ opening₀ message₁ opening₁,
    scheme.Accepts message₀ commitment opening₀ →
      scheme.Accepts message₁ commitment opening₁ →
        message₀ = message₁

end Cslib.Crypto.Protocols.Commitment.Scheme
