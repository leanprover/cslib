/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Init
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Commitment Schemes: Syntax and Correctness

The syntax of a commitment scheme ([BonehShoup2023], Section 8.12): committing
to a message samples a commitment-opening pair `(c, o)`, verification of a
claimed opening is deterministic, and honestly generated pairs always verify.

The algorithms are plain functions, with no efficiency or finiteness
assumptions. Security notions live in separate definitions, so the same syntax
can carry perfect, statistical, or computational security.

## Main definitions

- `Scheme`: commitment syntax with perfect correctness
- `Scheme.commitmentDist`: the public commitment distribution for a message
- `Scheme.mem_support_commitmentDist_iff`: a commitment is possible exactly
  when it has a possible opening
- `Scheme.Accepts`: the verifier's acceptance relation

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023]
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.Commitment

/-- A noninteractive, unkeyed commitment scheme over message, commitment, and
opening types ([BonehShoup2023], Section 8.12).

Committing is randomized and produces the commitment and opening together,
since the two may be correlated. Correctness requires that every
commitment-opening pair the honest committer can output is accepted by the
verifier; for a `PMF`, this says honest openings verify with probability
one. -/
structure Scheme (Message Commitment Opening : Type*) where
  /-- Randomized commitment and opening generation. -/
  commit (message : Message) : PMF (Commitment × Opening)
  /-- Deterministic verification of a claimed opening. -/
  verify (message : Message) (commitment : Commitment) (opening : Opening) : Bool
  /-- Every honestly generated commitment-opening pair verifies. -/
  correct : ∀ message commitment opening,
    (commitment, opening) ∈ (commit message).support →
      verify message commitment opening = true

namespace Scheme

variable {Message Commitment Opening : Type*}

/-- The public commitment distribution obtained by forgetting the opening. -/
noncomputable def commitmentDist (scheme : Scheme Message Commitment Opening)
    (message : Message) : PMF Commitment :=
  (scheme.commit message).map Prod.fst

/-- A commitment lies in the public distribution's support exactly when some
opening makes the corresponding pair an honest possible output. -/
theorem mem_support_commitmentDist_iff
    (scheme : Scheme Message Commitment Opening) {message : Message}
    {commitment : Commitment} :
    commitment ∈ (scheme.commitmentDist message).support ↔
      ∃ opening, (commitment, opening) ∈ (scheme.commit message).support := by
  simp [commitmentDist]

/-- The proposition that an opening is accepted for a commitment and message. -/
def Accepts (scheme : Scheme Message Commitment Opening) (message : Message)
    (commitment : Commitment) (opening : Opening) : Prop :=
  scheme.verify message commitment opening = true

/-- Every pair in the support of honest commitment is accepted. -/
theorem accepts_of_mem_support (scheme : Scheme Message Commitment Opening)
    {message : Message} {commitment : Commitment} {opening : Opening}
    (h : (commitment, opening) ∈ (scheme.commit message).support) :
    scheme.Accepts message commitment opening :=
  scheme.correct message commitment opening h

/-- Build a commitment scheme from deterministic commitment generation. -/
noncomputable def ofPure (commit : Message → Commitment × Opening)
    (verify : Message → Commitment → Opening → Bool)
    (correct : ∀ message, verify message (commit message).1 (commit message).2 = true) :
    Scheme Message Commitment Opening where
  commit message := PMF.pure (commit message)
  verify := verify
  correct message commitment opening h := by
    grind [PMF.mem_support_pure_iff]

end Scheme

end Cslib.Crypto.Protocols.Commitment
