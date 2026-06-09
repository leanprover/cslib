/-
Copyright (c) 2026 Benjamin Brastmckie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brastmckie
-/

import Cslib.Logics.Bimodal.Metalogic.Decidability.Tableau

/-!
# Trace Certificates for Tableau Rule Firings

This module defines the data types for instrumenting the tableau decision
procedure with rule-firing trace certificates. Every rule application during
proof search is recorded as a `TraceEntry` mirroring the Libal and Volpe
FPC schema `(precondition, rule, conclusion, branch_id)`. The certificate
is threaded through `expandBranchWithFuel` as a pure `StateM` layer so
that the existing termination/soundness proofs in `Saturation.lean`
remain valid.

## Main Definitions

- `ClosureReason` -- Witness type explaining why a branch closed
- `TraceEntry` -- A single trace event for a tableau rule firing
- `CertOutcome` -- Outcome classification (valid, countermodel, timeout)
- `ProofCertificate` -- Aggregate certificate collecting all trace events
- `ProofCertificate.empty` -- Empty certificate for a given formula
- `TraceFailure` -- Failure with preserved partial trace
- `TraceResult` -- Sum type: success or failure with partial trace

## References

* Libal and Volpe (2016) "Certification of Prefixed Tableau Proofs for
  Modal Logic" (GandALF/EPTCS 226, pp. 257-271) -- FPC schema.

Ported from BimodalLogic with universe-polymorphic `Formula Atom`
replacing monomorphic `Formula`.
-/

set_option linter.style.longLine false

namespace Cslib.Logic.Bimodal.Metalogic.Decidability

open Cslib.Logic.Bimodal

variable {Atom : Type*} [DecidableEq Atom] [Hashable Atom]

/-!
## Closure Reason Type

Defined here so TraceCertificate and Closure can both use it.
Closure.lean (Phase 3) will import this and add detection functions.
-/

/--
Witness for why a branch is closed.

Each constructor provides evidence of the contradiction:
- `contradiction`: Both T(phi) and F(phi) are present
- `botPos`: T(bot) is present (asserting falsum is true)
- `axiomNeg`: F(axiom) is present (negating a valid axiom)
-/
inductive ClosureReason (Atom : Type*) [DecidableEq Atom] : Type _ where
  /-- Branch contains both T(phi) and F(phi) at the same label. -/
  | contradiction (φ : Formula Atom) (label : Label)
  /-- Branch contains T(bot) at some label. -/
  | botPos (label : Label)
  /-- Branch contains F(phi) where phi is an axiom instance. -/
  | axiomNeg (φ : Formula Atom) (witness : Axiom φ) (label : Label)

/-!
## TraceEntry Inductive
-/

/--
A single trace entry for a tableau rule firing.

Mirrors the Libal and Volpe FPC schema
`(precondition, rule, conclusion, branch_id)`.

Constructors:
- `ruleFired`: A rule was applied to a source signed formula producing
  conclusion signed formulas.
- `branchCreated`: A new sub-branch was created during a split.
- `branchClosed`: A branch closed (with `ClosureReason`).
- `blockingFired`: Subset blocking detected a saturating time.
- `fuelExhausted`: Fuel budget was exhausted.
-/
inductive TraceEntry (Atom : Type*) [DecidableEq Atom]
    [Hashable Atom] : Type _ where
  /-- A tableau rule was applied. Carries the source signed formula
      (precondition), the rule applied, and the produced signed
      formulas (conclusion). `stepIndex` is a monotonic counter. -/
  | ruleFired (stepIndex : Nat) (rule : TableauRule) (sign : Sign)
      (formula : Formula Atom) (label : Label)
      (produced : List (SignedFormula Atom))
      (isPersistent : Bool) (branchDepth : Nat)
  /-- A new sub-branch was created during a split
      (branching rule). -/
  | branchCreated (stepIndex : Nat) (parentBranch : Nat)
      (newBranchId : Nat) (fromRule : TableauRule)
  /-- A branch closed, with a `ClosureReason` witness. -/
  | branchClosed (stepIndex : Nat) (branchId : Nat)
      (reason : ClosureReason Atom)
  /-- Subset blocking detected a saturating time point. -/
  | blockingFired (stepIndex : Nat) (blockedTime : TimeIndex)
      (ancestorTime : TimeIndex)
  /-- Fuel budget was exhausted. `fuelRemaining` is the budget that
      remained (typically `0`). -/
  | fuelExhausted (stepIndex : Nat) (fuelRemaining : Nat)

/-!
## Outcome Types
-/

/--
Outcome classification of a `ProofCertificate` run.

- `validProof`: All branches closed (formula is valid).
- `countermodel`: Saturated open branch found (formula is invalid).
- `timeout`: Fuel exhausted before decision.
- `blocked`: Subset blocking fired (sub-branch may be saturated).
-/
inductive CertOutcome : Type where
  | validProof
  | countermodel
  | timeout
  | blocked
  deriving Repr, Inhabited, DecidableEq, BEq

/-!
## ProofCertificate Structure
-/

/--
A proof certificate collecting all trace events during a tableau run.

`axiomFingerprint`, `branchingFactor`, and `maxDepth` are pre-computed
(incrementally during expansion) to support O(1) reads and O(n) writes.
`elapsedMs` is `0` in pure `decideWithTrace`; the `IO` wrapper fills
it in.
-/
structure ProofCertificate (Atom : Type*) [DecidableEq Atom]
    [Hashable Atom] where
  /-- The original formula being decided. -/
  formula : Formula Atom
  /-- The frame class used for the decision procedure. -/
  frameClass : FrameClass
  /-- The outcome of the proof attempt. -/
  outcome : CertOutcome
  /-- Sequential trace of all rule firings and state changes
      (in chronological order: most recent event at the head,
      oldest at the tail -- see `finalizeCertificate`). -/
  trace : List (TraceEntry Atom)
  /-- Total rule firings (cached for O(1) access). -/
  totalSteps : Nat
  /-- Per-rule-name firing counts. -/
  axiomFingerprint : Std.HashMap String Nat
  /-- Average branching factor across all branching rule events. -/
  branchingFactor : Float
  /-- Maximum branch depth observed. -/
  maxDepth : Nat
  /-- Time consumed (wall-clock, in ms). `0` in pure version. -/
  elapsedMs : Nat

namespace ProofCertificate

/--
Empty certificate for a given formula and frame class. All accumulators
are zero; the trace is empty.
-/
def empty (φ : Formula Atom) (fc : FrameClass := .Base) :
    ProofCertificate Atom :=
  { formula := φ
  , frameClass := fc
  , outcome := .timeout          -- provisional until result is known
  , trace := []
  , totalSteps := 0
  , axiomFingerprint := ∅
  , branchingFactor := 1.0       -- default (no branching events)
  , maxDepth := 0
  , elapsedMs := 0 }

/--
`Inhabited` instance for `ProofCertificate` (using `Formula.bot`
as the default formula).
-/
instance : Inhabited (ProofCertificate Atom) :=
  ⟨ProofCertificate.empty Formula.bot .Base⟩

end ProofCertificate

/-!
## Failure Types
-/

/--
A failure outcome carrying the partial trace for post-mortem analysis.

- `outOfFuel`: Fuel budget exhausted; the trace contains all events
  recorded up to the point of exhaustion.
- `unsaturatable`: Expansion stalled (no rule applies, but the branch
  is not yet saturated; this is an internal-condition failure).
- `applyRulePanic`: An internal inconsistency was detected during rule
  application (should not occur in practice).
-/
inductive TraceFailure (Atom : Type*) [DecidableEq Atom]
    [Hashable Atom] : Type _ where
  | outOfFuel (trace : List (TraceEntry Atom))
      (stepsCompleted : Nat)
  | unsaturatable (trace : List (TraceEntry Atom))
      (openBranch : Branch Atom)
  | applyRulePanic (trace : List (TraceEntry Atom))
      (rule : TableauRule) (sf : SignedFormula Atom)

/--
Sum type for a `decideWithTrace` call: success (carrying the full
certificate) or failure (carrying the partial trace).
-/
inductive TraceResult (Atom : Type*) [DecidableEq Atom]
    [Hashable Atom] : Type _ where
  | success (cert : ProofCertificate Atom)
  | failure (failure : TraceFailure Atom)

/-!
## Rule Name Mapping
-/

/--
Map a `TableauRule` to a stable, JSON-safe string name.

This is the canonical serialization for `axiomFingerprint` keys.
-/
def ruleToString : TableauRule → String
  | .andPos                  => "andPos"
  | .andNeg                  => "andNeg"
  | .orPos                   => "orPos"
  | .orNeg                   => "orNeg"
  | .impPos                  => "impPos"
  | .impNeg                  => "impNeg"
  | .negPos                  => "negPos"
  | .negNeg                  => "negNeg"
  | .boxPos                  => "boxPos"
  | .boxNeg                  => "boxNeg"
  | .diamondPos              => "diamondPos"
  | .diamondNeg              => "diamondNeg"
  | .boxTemporal             => "boxTemporal"
  | .allFuturePos            => "allFuturePos"
  | .allFutureNeg            => "allFutureNeg"
  | .allPastPos              => "allPastPos"
  | .allPastNeg              => "allPastNeg"
  | .someFuturePos           => "someFuturePos"
  | .someFutureNeg           => "someFutureNeg"
  | .somePastPos             => "somePastPos"
  | .somePastNeg             => "somePastNeg"
  | .untlPos                 => "untlPos"
  | .untlNeg                 => "untlNeg"
  | .sncePos                 => "sncePos"
  | .snceNeg                 => "snceNeg"
  | .denseIndicatorClosure   => "denseIndicatorClosure"
  | .densityRule             => "densityRule"
  | .priorUZ                 => "priorUZ"
  | .priorSZ                 => "priorSZ"
  | .z1Rule                  => "z1Rule"

/--
Compute the depth of a trace entry (used for `maxDepth`).
Returns `0` for non-`branchCreated` events and `newBranchId`
for `branchCreated`.
-/
def entryDepth : TraceEntry Atom → Nat
  | .branchCreated _ _ newBranchId _ => newBranchId
  | _                                 => 0

/--
Incrementally update the axiom fingerprint for a single `TraceEntry`.
No-op for non-`ruleFired` entries.
-/
def updateFingerprint (fp : Std.HashMap String Nat)
    (entry : TraceEntry Atom) : Std.HashMap String Nat :=
  match entry with
  | .ruleFired _ rule _ _ _ _ _ _ =>
      let key := ruleToString rule
      fp.insert key (fp.getD key 0 + 1)
  | _ => fp

/-!
## TraceM Monad
-/

/-- A trace-monad computation: `StateM` over `ProofCertificate`. -/
abbrev TraceM (Atom : Type u) [DecidableEq Atom] [Hashable Atom]
    (α : Type u) : Type u :=
  StateM (ProofCertificate Atom) α

namespace TraceM

variable {Atom : Type u} [DecidableEq Atom] [Hashable Atom]

/-- Get the current certificate. -/
def getCert : TraceM Atom (ProofCertificate Atom) := get

/-- Set the current certificate. -/
def setCert (cert : ProofCertificate Atom) :
    TraceM Atom PUnit := set cert

/--
Record a single trace event.

The certificate is updated as follows:
- `trace`: prepend the entry (O(1) cons; reversed at finalize time)
- `totalSteps`: increment by 1
- `axiomFingerprint`: increment the count for this rule
  (no-op for non-`ruleFired`)
- `maxDepth`: max with `entryDepth entry`
- `branchingFactor`: unchanged here (computed at finalize)
-/
def record (entry : TraceEntry Atom) : TraceM Atom PUnit := do
  modify fun cert =>
    let newTrace := entry :: cert.trace
    let newTotal := cert.totalSteps + 1
    let newFp := updateFingerprint cert.axiomFingerprint entry
    let newMaxDepth := max cert.maxDepth (entryDepth entry)
    { cert with
      trace := newTrace
      totalSteps := newTotal
      axiomFingerprint := newFp
      maxDepth := newMaxDepth
      : ProofCertificate Atom }

/--
Helper for the 28 `applyRule` arms: record a `ruleFired` event.

The function takes the `TableauRule`, the source signed formula's
components (sign, formula, label), the produced formulas, whether
the rule is persistent, and the branch depth.
-/
def recordRuleFired (rule : TableauRule) (sign : Sign)
    (formula : Formula Atom) (label : Label)
    (produced : List (SignedFormula Atom))
    (isPersistent : Bool) (branchDepth : Nat) :
    TraceM Atom PUnit := do
  let cert ← get
  let entry : TraceEntry Atom :=
    .ruleFired cert.totalSteps rule sign formula label
      produced isPersistent branchDepth
  record entry

end TraceM

end Cslib.Logic.Bimodal.Metalogic.Decidability
