# Research Report: Task #50 — Burgess Prior Art and Seed Research for Tasks 46-49

**Task**: 50 — Research Burgess prior art and seed research for tasks 46-49
**Date**: 2026-06-09
**Mode**: Team Research (4 teammates)
**Session**: sess_1781036129_70af6f

## Summary

The Burgess 1982 chronicle construction for temporal Until/Since completeness maps cleanly to tasks 46-49. The bimodal BXCanonical/Chronicle/ infrastructure (12,096 lines) is **~90-95% purely temporal** in its core — the box modality only appears in integration files (Frame.lean, TruthLemma.lean, CanonicalModel.lean, ChronicleToCountermodel*.lean). A direct copy-adapt approach is recommended, with name alignment to prepare for future abstraction (task 41). Key risk: ~850-1000 lines of prerequisite infrastructure (g_content/h_content, witness seeds, DCS types from Bundle/) are unlisted in the current task descriptions. Revised total estimate: 5,000-8,600 lines vs the original 4,300-7,500.

## Key Findings

### 1. Literature Completeness (Teammate A — HIGH confidence)

Burgess 1982 Section 2 is self-contained: the entire completeness proof for S,U-tense logic over linear orders fits in Lemmas 2.1-2.11 (~5 pages). The construction has 4 distinct layers that map 1:1 to tasks 46-49:

| Task | Burgess Content | Bimodal Lines | Temporal Est. |
|------|----------------|---------------|---------------|
| 46 | R-relation, witnesses (2.2-2.5) | 2,405 | 1,200-2,000 |
| 47 | Point insertion (2.6-2.8) + types | 3,942 | 1,500-2,800 |
| 48 | Counterexample elim + construction (2.9-2.10) | 5,060 | 1,500-3,000 |
| 49 | Truth lemma + assembly (2.11) | 2,393 | 800-1,800 |
| **Total** | | **13,800** | **5,000-8,600** |

Xu 1988 provides a cleaner C0-C6 condition formulation suitable for Lean formalization. BdRV Theorem 7.15 = Burgess J₀ completeness (the exact target).

### 2. Infrastructure Audit (Teammate B — HIGH confidence)

The bimodal/temporal boundary is clean:
- **Zero box references** in: RRelation.lean, PointInsertion.lean, CounterexampleElimination.lean, ChronicleConstruction.lean (10,311 lines total)
- **Box-entangled**: Frame.lean (bx_modal_equiv), TruthLemma.lean (box_iff_mcs), CanonicalModel.lean (FMCS/BFMCS), ChronicleToCountermodel*.lean (dense/discrete box split)

The existing temporal infrastructure (phases 1-5) provides:
- Full MCS, Lindenbaum, DeductionTheorem, Soundness
- Partial canonical model: `CanonicalWorld`, `canonical_acc`, G/H truth lemma
- Single `sorry` at Completeness.lean:416 — exactly the gap the chronicle fills

### 3. Missing Prerequisites (Teammate C — HIGH confidence)

**Critical gap not in task descriptions**: The Chronicle files depend on Bundle/ infrastructure not listed in any task:

| Missing Component | Source | Lines | Needed By |
|-------------------|--------|-------|-----------|
| g_content/h_content definitions | Bundle/TemporalContent.lean | ~169 | All Chronicle files |
| Witness seed consistency | Bundle/WitnessSeed.lean | ~607 | RRelation, PointInsertion |
| DCS type + mcs_is_dcs | ChronicleTypes.lean | ~80 | ChronicleTypes |
| Propositional combinators | Theorems/Propositional/Core.lean | ~200 | All |
| Temporal derived theorems | Theorems/TemporalDerived.lean | ~150 | All |

**Recommendation**: Task 46 should explicitly include creating this prerequisite infrastructure as phase 0 deliverables.

### 4. Scope Estimate Revisions (Teammate C)

| Task | Original | Revised | Reason |
|------|----------|---------|--------|
| 46 | 800-1,500 | 1,200-2,000 | +prerequisite infrastructure (g_content, witness seeds, DCS) |
| 47 | 1,500-2,800 | 1,500-2,800 | Reasonable if task 46 prerequisites are solid |
| 48 | 1,500-3,000 | 1,500-3,000 | Reasonable (30-60% reduction from bimodal) |
| 49 | 500-1,200 | 800-1,800 | Countermodel extraction needs redesign (box-entangled) |

### 5. Abstraction Strategy (Teammate D — HIGH confidence)

**Recommended: Copy-Adapt-Then-Abstract**:
1. Tasks 46-49: Direct adaptation with identical naming conventions
2. Task 41 (later): Extract common structure — drops from 8-12h to 4-6h if naming aligned

**Tier 1 abstraction wins (safe to do now)**:
- **FrameClass**: Byte-identical across both logics → unify in `Foundations/Logic/Metalogic/`
- **Temporal content defs**: g_content/h_content could be parameterized over a `HasTemporalOps` typeclass

**Tier 2-3 (defer to task 41)**:
- Point insertion, chronicle construction, counterexample elimination — too tightly coupled for premature abstraction

**Critical design principle**: Use identical names (`rRelation`, `rMaximal`, `chronicle_defect`, etc.) so task 41 becomes extraction rather than archaeology.

## Synthesis

### Conflicts Resolved

1. **Scope estimates** (A vs C): Teammate A estimated 4,480-7,170 total; Teammate C estimated 5,000-8,600. Resolution: C's higher estimate is more accurate because it accounts for unlisted Bundle/ prerequisites. Adopted C's numbers.

2. **Abstraction timing** (B vs D): B recommended "direct port first, abstract later"; D recommended the same but flagged FrameClass as a safe immediate win. Resolution: Adopt both — copy-adapt strategy with FrameClass unification as the one exception.

3. **Countermodel extraction approach** (B vs C): B noted 50% transfer for ChronicleToCountermodelBasic; C identified it as heavily box-entangled needing complete redesign. Resolution: C is correct — the temporal countermodel is structurally simpler (just linear order + valuation, no modal accessibility), so task 49 should build new extraction rather than adapt the bimodal version.

### Gaps Identified

1. **Task 46 prerequisites**: Need explicit phase for g_content/h_content, witness seeds, DCS infrastructure (~850-1000 lines)
2. **Propositional combinators**: Temporal logic lacks derived theorem files that bimodal Chronicle imports
3. **Open guard semantics sorrys**: Bimodal RRelation.lean and PointInsertion.lean have sorry stubs — need to verify if these transfer to temporal or can be eliminated
4. **Dense/discrete interaction**: Base chronicle produces a dense model (ℚ); discrete completeness (task 39) may need different countermodel extraction. The chronicle construction itself handles both uniformly.
5. **Completeness.lean overlap**: Existing temporal Completeness.lean has CanonicalWorld/canonical_acc infrastructure that partially overlaps with what Frame.lean provides — need to reconcile

### Task Description Improvements

**Task 46** should add:
- Phase 0: Create prerequisite infrastructure (g_content, h_content, witness seeds, DCS, propositional combinators)
- Explicit mention of Bundle/TemporalContent.lean (169 lines) and Bundle/WitnessSeed.lean (607 lines) as sources
- Revised scope: 1,200-2,000 lines

**Task 47** should add:
- Note that the temporal version eliminates C5b/C6b for □ (only temporal C5a/C6a and S-mirrors)
- Note dependency on propositional combinators from task 46 phase 0

**Task 48** should add:
- Note that `[Denumerable (Formula Atom)]` instance is required (same as bimodal)
- The omega-chain enumeration structure is nearly identical to bimodal

**Task 49** should add:
- Explicit note that ChronicleToCountermodel*.lean is NOT directly adaptable (box-entangled)
- The temporal countermodel is simpler: chronicle frame (X, <, V) directly, no FMCS/BFMCS
- Revised scope: 800-1,800 lines
- Note interaction with Completeness.lean's existing CanonicalWorld infrastructure

## Teammate Contributions

| Teammate | Angle | Status | Confidence |
|----------|-------|--------|------------|
| A | Literature analysis (Burgess/Xu/BdRV) | completed | high |
| B | Bimodal infrastructure audit | completed | high |
| C | Gaps, risks, blind spots | completed | high |
| D | Abstraction strategy and horizons | completed | high |

## References

### Primary Sources
- Burgess 1982 "Axioms for tense logic I: Since and Until" — Section 2, Lemmas 2.1-2.11
- Xu 1988 "On some US-tense logics" — Definition 2.5, Theorem 2.8
- Blackburn/de Rijke/Venema 2002 "Modal Logic" — Section 7.2, Theorem 7.15

### Supplementary Sources
- Burgess 1984 "Basic Tense Logic" — general survey, no additional proof content
- Venema 2001 "Temporal Logic Survey" — frame conditions overview
- Venema 1993 "Since and Until" — Stavi connectives (alternative strategy, not for tasks 46-49)
- Verbrugge 2004 "Completeness by construction" — step-by-step method (complementary, for G/H only)
- GHR 1994 Ch.9 — expressive completeness context (Kamp's theorem)

### Codebase Sources
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/` — 12,096 lines (primary adaptation source)
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/` — Frame.lean, CanonicalChain.lean, OrderedSeedConsistency.lean, TruthLemma.lean, CanonicalModel.lean
- `Cslib/Logics/Bimodal/Metalogic/Bundle/` — TemporalContent.lean, WitnessSeed.lean (prerequisite infrastructure)
- `Cslib/Logics/Temporal/Metalogic/` — Completeness.lean (sorry target), MCS.lean, DeductionTheorem.lean, Soundness.lean
