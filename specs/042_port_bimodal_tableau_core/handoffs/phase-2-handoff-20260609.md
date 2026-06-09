# Phase 2 Handoff: Tableau Rules + TraceCertificate

## Status: COMPLETED

## What Was Done

### Tableau.lean (1,204 lines)
- Ported all 30 TableauRule constructors (andPos, andNeg, orPos, orNeg, impPos, impNeg, negPos, negNeg, boxPos, boxNeg, diamondPos, diamondNeg, boxTemporal, allFuturePos, allFutureNeg, allPastPos, allPastNeg, someFuturePos, someFutureNeg, somePastPos, somePastNeg, untlPos, untlNeg, sncePos, snceNeg, denseIndicatorClosure, densityRule, priorUZ, priorSZ, z1Rule)
- Ported RuleResult inductive (linear, branching, persistent, notApplicable)
- Ported 10 formula decomposition helpers (asNeg?, asAnd?, asOr?, asDiamond?, asSomePast?, asSomeFuture?, asAllFuture?, asAllPast?, asUntil?, asSince?)
- Ported full applyRule function (~600 lines of match arms)
- Ported isApplicable, findApplicableRule, findApplicableRuleWithApplied
- Ported isExpanded, findUnexpanded, findUnexpandedWithApplied
- Ported expandOnce, expandOnceWithApplied, ExpansionResult
- Ported AppliedSet type (Std.HashSet)
- Ported allRules, denseRules, discreteRules, allRulesForFC
- Ported countUnexpanded, totalUnexpandedComplexity
- Three simp theorems (branching_ne_notApplicable, linear_ne_notApplicable, persistent_ne_notApplicable)

### TraceCertificate.lean (350 lines)
- Defined ClosureReason inductive (moved from Closure.lean since TraceCertificate needs it)
- Ported TraceEntry inductive (ruleFired, branchCreated, branchClosed, blockingFired, fuelExhausted)
- Ported CertOutcome inductive (validProof, countermodel, timeout, blocked)
- Ported ProofCertificate structure with all fields
- Ported ProofCertificate.empty
- Ported TraceFailure and TraceResult
- Ported ruleToString (all 30 rules)
- Ported entryDepth, updateFingerprint
- Ported TraceM monad and helpers (getCert, setCert, record, recordRuleFired)

## Key Decisions
- ClosureReason was moved to TraceCertificate.lean (not Closure.lean) because TraceCertificate needs it and Closure is Phase 3
- TraceM uses universe-polymorphic `Type u` (not `Type *`) to avoid universe mismatch with PUnit
- ClosedBranch type deferred to Phase 3 (it belongs in Closure.lean)
- set_option linter.style.longLine false used in Tableau.lean for deeply nested let-bindings

## Verification
- Zero sorry in both files
- Zero vacuous definitions
- Zero new axioms
- Both files compile with lake build
- lean_verify confirms clean axiom usage (only propext, Quot.sound)

## Next Phase (3): AxiomMatcher + Closure
- ClosureReason is already defined (in TraceCertificate.lean)
- Closure.lean should import TraceCertificate.lean and add detection functions
- AxiomMatcher.lean extracts matchAxiom from ProofSearch.Core
