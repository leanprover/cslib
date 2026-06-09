# Teammate D (Horizons) Findings: Strategic Alignment and Abstraction Opportunities

**Task**: 50 — Burgess prior art and seed research for tasks 46-49
**Date**: 2026-06-09
**Focus**: Long-term abstraction strategy between Temporal/ and Bimodal/ metalogics

## Key Findings

### 1. The Formula Gap Is the Fundamental Obstacle to Abstraction

The temporal formula type (`Temporal.Formula`) has 5 constructors: `atom`, `bot`, `imp`, `untl`, `snce`. The bimodal formula type (`Bimodal.Formula`) has 6: the same 5 plus `box`. This means **every definition and proof in the chronicle construction is parameterized over a formula type**, and any shared abstraction must handle this difference.

The most natural abstraction boundary is: **anything that only mentions `untl`, `snce`, `imp`, `bot`, and derived temporal operators (G/H/F/P) is a candidate for sharing**. The box constructor is only relevant for the bimodal modal saturation (Bundle/) and the `bx_modal_equiv` relation on BXPoint.

### 2. FrameClass Is Already Isomorphic

Both logics define identical `FrameClass` inductives (`Base | Dense | Discrete`) with identical `LE` and `PartialOrder` instances. This is a concrete, immediate abstraction target — a shared `FrameClass` could live in `Foundations/Logic/Metalogic/` alongside the existing `DerivationSystem`.

### 3. Content Definitions Are Sharable But Blocked by Formula Types

The bimodal `TemporalContent.lean` (169 lines) defines `g_content`, `h_content`, `f_content`, `p_content`, `u_content`, `s_content` — all using only temporal operators. The temporal completeness in `Completeness.lean` re-derives these concepts inline (e.g., `futureSet`). These definitions are **structurally identical** across logics and could be parameterized over any formula type that has `all_future`, `all_past`, `some_future`, `some_past`, `untl`, `snce`.

### 4. DeductionSystem Abstraction Already Exists

`Foundations/Logic/Metalogic/Consistency.lean` already provides the abstract `DerivationSystem`, `SetConsistent`, `SetMaximalConsistent`, and Lindenbaum's lemma. Both Temporal and Bimodal instantiate this. The `DeductionTheorem` abstraction is also parameterized. This layer is solid and doesn't need changes.

### 5. BXCanonical Chronicle Is the Target, Not Bundle

The Bundle/ infrastructure (2,375 lines) handles the **Z-chain canonical model** construction — it's the "easy" completeness for base/dense frames using a countable chain of MCS. The BXCanonical/Chronicle/ (12,096 lines) is the **Burgess point-insertion method** for handling Until/Since. These are separate proof strategies, and the chronicle is what tasks 46-49 port.

The Bundle/ is relevant only as a dependency — Chronicle imports Bundle types like `TemporalContent`, `WitnessSeed`, `CanonicalFrame`. A temporal chronicle would import analogous temporal definitions instead.

### 6. The Single Sorry Is at the Chain Construction Level

The temporal `Completeness.lean` (418 lines) has exactly one `sorry` at line 416 — the main completeness theorem. The `sorry` sits at the step "Build a countermodel on Z". Tasks 46-49 don't fill this sorry directly (that's the Z-chain for base completeness). Instead, they build the chronicle machinery that tasks 38-40 (dense/discrete/continuous) will use.

Wait — re-reading the task descriptions more carefully, task 49 says "close the temporal completeness theorem, removing the final sorry." So the chronicle IS meant to fill this sorry, using a more general construction that also works for dense/discrete.

## Project Structure Analysis

### Import Flow
```
Foundations/Logic/Metalogic/Consistency.lean  (shared DerivationSystem, MCS)
    ↓                          ↓
Temporal/Metalogic/            Bimodal/Metalogic/
  DeductionTheorem.lean          Core/DeductionTheorem.lean
  MCS.lean                       Core/MaximalConsistent.lean
  Soundness.lean                 Soundness/
  Completeness.lean              Bundle/ + BXCanonical/ + Algebraic/
    ↓ (tasks 46-49)               ↓ (already done)
  Chronicle/                     BXCanonical/Chronicle/
```

### What Exists vs What's Needed

| Component | Temporal | Bimodal | Shared? |
|-----------|----------|---------|---------|
| FrameClass | ✓ (identical) | ✓ (identical) | Could share |
| DerivationSystem | ✓ (via Foundations) | ✓ (via Foundations) | Already shared |
| MCS + Lindenbaum | ✓ | ✓ | Already shared (Foundations) |
| DeductionTheorem | ✓ | ✓ | Separate (logic-specific) |
| Temporal content (g/h/f/p sets) | Inline in Completeness.lean | TemporalContent.lean (169 lines) | Could share |
| Chronicle types | Not yet | ChronicleTypes.lean (386 lines) | Could share |
| R-relation | Not yet | RRelation.lean (1,695 lines) | Could share |
| Point insertion | Not yet | PointInsertion.lean (3,556 lines) | Could share |
| Counterexample elimination | Not yet | CounterexampleElimination.lean (3,529 lines) | Could share |
| Chronicle construction | Not yet | ChronicleConstruction.lean (1,531 lines) | Could share |
| Truth lemma | Not yet | TruthLemma.lean (223 lines) | Partial |
| Countermodel extraction | Not yet | ChronicleToCountermodel*.lean (1,399 lines) | Partial |

## Abstraction Opportunity Assessment

### Tier 1: Easy Wins (do now, saves refactoring later)

**FrameClass unification**: Move `FrameClass` to `Foundations/Logic/Metalogic/FrameClass.lean`. Both logics import from there. Effort: ~1 hour, saves duplicated maintenance and is needed before any deeper sharing.

**Temporal content extraction**: Create `Foundations/Logic/Metalogic/TemporalContent.lean` with `g_content`, `h_content`, etc., parameterized over a typeclass like:
```lean
class HasTemporalOps (F : Type*) where
  all_future : F → F
  all_past : F → F
  some_future : F → F
  some_past : F → F
  untl : F → F → F
  snce : F → F → F
```
Both `Temporal.Formula` and `Bimodal.Formula` implement this. Effort: ~2-3 hours.

### Tier 2: Moderate Effort (design now, implement during task 41)

**DCS (Deductively Closed Sets)**: The `ClosedUnderDerivation`, `SetDeductivelyClosed`, `mcs_is_dcs` infrastructure in ChronicleTypes.lean is independent of bimodal formula structure. This could be added to `Foundations/Logic/Metalogic/Consistency.lean`.

**R-relation core definition**: The r-relation `r(A, β, C)` (Burgess 2.2) is defined purely in terms of Until/Since content. Its definition and the key closure lemma (Lemma 2.3: "if r(A,B) and γUδ ∈ A with δ ∉ B, then γ ∈ B and γUδ ∈ B") are logic-independent modulo `HasTemporalOps`.

### Tier 3: Premature Abstraction (copy-modify now, abstract in task 41)

**Point insertion**: The 3,556-line `PointInsertion.lean` has deeply interleaved formula manipulation and MCS reasoning. Abstracting this prematurely would create a fragile typeclass hierarchy. Better to have two concrete implementations and factor out the common structure later.

**Chronicle construction**: The omega-step construction depends on specific enumeration of defects and insertion mechanics. The pattern is identical but the details differ enough (bimodal has C5a/C6a/C5b/C6b; temporal only has C5/C6 without the modal component).

**Truth lemma**: The bimodal truth lemma has a `box` case that the temporal one doesn't. The other cases (atom, bot, imp, untl, snce) are structurally identical. But the truth lemma is short enough (223 lines) that duplicating it isn't costly.

## Strategic Recommendations

### Recommended Approach: "Copy-Adapt-Then-Abstract"

1. **Tasks 46-49**: Build temporal chronicle as a direct adaptation of bimodal BXCanonical/Chronicle/, with these modifications:
   - Remove all `Formula.box` references
   - Remove `bx_modal_equiv` and modal saturation
   - Replace `Bimodal.Formula` with `Temporal.Formula` everywhere
   - Replace bimodal MCS/DeductionTheorem with temporal versions
   - Simplify C5/C6 conditions (no modal component)

2. **During implementation**: Use identical naming conventions and structure so task 41 can identify common patterns:
   - Same file names: `RRelation.lean`, `ChronicleTypes.lean`, `PointInsertion.lean`, etc.
   - Same definition names where possible: `rRelation`, `rMaximal`, `chronicle_defect`, etc.
   - Same proof structure: Zorn's lemma for R-maximal, omega enumeration for defects

3. **Task 41 (later)**: Extract common structure into `Foundations/Logic/Metalogic/Chronicle/` using typeclasses. The two concrete implementations serve as the specification for what the abstraction must provide.

### One Exception: FrameClass Should Be Shared NOW

The `FrameClass` inductive is byte-for-byte identical across both logics. Unifying it before tasks 46-49 avoids creating yet another copy that needs to be refactored. It's small, self-contained, and has no downstream risk.

### Design Principle: Name Alignment Over Premature Parametricity

The biggest win for future abstraction isn't sharing code now — it's **ensuring the temporal chronicle uses the same conceptual vocabulary** as the bimodal one. If both use `rRelation`, `rMaximal`, `chronicle_defect`, `insert_point`, `counterexample_eliminated`, then task 41 becomes a straightforward extraction. If they diverge in naming, task 41 becomes archaeology.

## Alternative Approaches Worth Considering

### Verbrugge 2004 Step-by-Step Method

The Verbrugge/de Jongh/Veltman "completeness by construction" paper uses a simpler step-by-step construction that doesn't require the full chronicle machinery. For basic linear completeness (Theorems 1-2), it constructs the countermodel by iteratively adding points to satisfy ¬Gφ and ¬Hφ deficiencies. This is **closer to what the current temporal Completeness.lean sorry needs** — a Z-chain, not a chronicle.

However, for **dense completeness** (Theorem 3: Q-completeness), they use the same step-by-step method with interleaved density insertion. For **continuous completeness** (Theorem 4: R-completeness), they extend Q to R by filling gaps. These are simpler than Burgess's chronicle but handle G/H only, not Until/Since directly.

**Relevance**: The step-by-step method could fill the base completeness sorry more simply than the full chronicle. The chronicle is needed for Until/Since truth lemma on general linear orders. The two approaches are complementary, not competing.

### Venema 1993: Stavi Connectives and Expressive Completeness

Venema's paper on well-ordered frames uses **expressive completeness** of S/U to transfer completeness results. The idea is: if S/U is expressively complete over a frame class (equivalent to monadic first-order logic), then completeness for G/H transfers to completeness for S/U via syntactic translation.

This is an **alternative strategy** that could bypass the chronicle entirely for certain frame classes. However:
- It requires proving expressive completeness of S/U, which is Kamp's theorem — a significant formalization effort
- It uses the Stavi connectives (gap-detecting operators) as intermediaries
- It's better suited for specific frame classes (well-orders, ω) than for the general serial linear order

**Verdict**: Not relevant for tasks 46-49 (which follow Burgess directly), but potentially relevant for tasks 38-40 (dense/discrete/continuous specializations).

### Could Task 50 Reduce Task 41 Scope?

Yes, if the temporal chronicle is built with careful name alignment:
- Task 41's job is to "identify which abstractions yield genuine code savings." Having two concrete implementations with aligned names makes this identification trivial.
- Task 41's candidate abstractions (listed in its description) are already accurate. Having the temporal implementation will let task 41 validate each candidate with `diff` rather than speculation.
- Estimated reduction: task 41 drops from "Medium (8-12 hours)" to "Small (4-6 hours)" if naming is aligned.

## Confidence Level

- **FrameClass unification**: High — byte-identical, zero risk
- **Copy-adapt strategy for 46-49**: High — proven by bimodal success
- **Name alignment recommendation**: High — near-zero cost, high future payoff
- **Tier 2/3 abstraction timing**: Medium — the "right" abstraction boundary depends on implementation details not yet visible
- **Alternative approaches (Venema, Verbrugge)**: Medium — theoretically sound but outside the Burgess path that tasks 46-49 are designed for
