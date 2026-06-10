# Research Report: Task #55

**Task**: 55 - Review and update ROADMAP.md with completions and mermaid diagram
**Started**: 2026-06-09T00:00:00Z
**Completed**: 2026-06-09T00:15:00Z
**Effort**: Small (1-2 hours)
**Dependencies**: None
**Sources/Inputs**: ROADMAP.md, specs/TODO.md, specs/state.json, specs/archive/state.json, Cslib/ directory tree
**Artifacts**: specs/055_update_roadmap_completions_and_diagram/reports/01_roadmap-review.md
**Standards**: report-format.md

## Executive Summary

- ROADMAP.md is largely accurate but has two major gaps: the "Remaining" section lists items that are now completed (Temporal metalogic completeness was completed via tasks 46-49), and the mermaid diagram is missing nodes and edges for the Temporal Syntax/Semantics infrastructure.
- The diagram is missing an explicit `TS` (Temporal Syntax) node and the `MM` node should show its dependency on `MB` (Modal Basic). The dashed edge from `TT` to `BT` is present and correct.
- The "Completed" table needs new rows for: Temporal syntax infrastructure (Context, BigConj, Subformulas), Temporal metalogic (full: DeductionThm + MCS + Soundness + Completeness — NOT just listed as remaining), and the chronicle-based completeness pipeline (tasks 46-49).
- Tasks 38, 39, 41 show [COMPLETED] in TODO.md task detail sections but "not_started" in state.json and [NOT STARTED] in the wave table — this is a state.json/TODO.md inconsistency. The actual code does NOT have Dense/Discrete completeness files yet (only FrameClass.Base in Completeness.lean, no DenseCompleteness.lean or DiscreteCompleteness.lean). These tasks are genuinely not started.

## Context & Scope

This research covers the current state of `specs/ROADMAP.md` and what actually exists in the codebase under `Cslib/`. The goal is to identify:
1. What ROADMAP.md currently says
2. What has actually been completed (based on archive/state.json and file existence)
3. What the mermaid diagram shows vs what it should show
4. Specific discrepancies and recommended updates

## Findings

### Current ROADMAP.md Content Summary

The ROADMAP.md (203 lines, last revised in task 45) contains:
- **Approach** section: describes four-level module structure with import flow
- **Module Dependency Structure**: a mermaid flowchart with nodes FC, FT, FM, MB, MM, TS, TT, TM, BS, BT, BM
- **Completed** table: 19 rows covering Foundations through Temporal metalogic
- **Remaining** table: 6 rows listing dense/discrete/continuous completeness items
- **Project Structure**: a directory tree showing `Cslib/` layout

### What Has Been Completed (from archive + codebase)

**Completed and correctly listed in ROADMAP.md:**
- Propositional Hilbert theorems (task 20): `Foundations/Logic/Theorems/`
- Modal proof system, S4/S5 theorems (task 21): `Foundations/Logic/Theorems/Modal/`
- Generic MCS foundations (task 29): `Foundations/Logic/Metalogic/Consistency.lean`
- Temporal proof system (task 22): `Logics/Temporal/ProofSystem/`
- Temporal theorems (task 22): `Logics/Temporal/Theorems/`
- Temporal semantics (task 23): `Logics/Temporal/Semantics/`
- Modal metalogic: DeductionTheorem, MCS, Soundness, Completeness (task 30): `Logics/Modal/Metalogic/`
- Bimodal syntax (task 2): `Logics/Bimodal/Syntax/`
- Bimodal semantics (task 3): `Logics/Bimodal/Semantics/`
- Bimodal proof system (task 4): `Logics/Bimodal/ProofSystem/`
- Perpetuity theorems (task 5): `Logics/Bimodal/Theorems/Perpetuity/`
- Frame conditions + Soundness (task 6): `Logics/Bimodal/FrameConditions/` + `Logics/Bimodal/Metalogic/Soundness/`
- Bimodal DeductionTheorem + MCS (task 7): `Logics/Bimodal/Metalogic/Core/`
- Base MCS completeness properties (task 34): `Logics/Bimodal/Metalogic/Completeness.lean`
- Separation theorem (task 10): `Logics/Bimodal/Metalogic/Separation/`
- BX conservative extension (task 11): `Logics/Bimodal/Metalogic/ConservativeExtension/`
- Tableau decision procedure (task 42): `Logics/Bimodal/Metalogic/Decidability/`
- Finite model property (task 43): `Logics/Bimodal/Metalogic/Decidability/FMP/`
- Dense completeness (bimodal, task 35): `Logics/Bimodal/Metalogic/BXCanonical/Completeness/Dense.lean`
- **Temporal metalogic (FULL, tasks 31/46/47/48/49)**: base completeness (`Completeness.lean`) + chronicle pipeline (`Chronicle/` — 10 files)

**Completed but missing from ROADMAP.md "Completed" table:**
- Temporal Syntax infrastructure (Formula + Context + BigConj + Subformulas): completed in task 2 (originally "bimodal syntax" but extended temporal syntax) and fully present at `Logics/Temporal/Syntax/`
- Temporal chronicle pipeline for completeness (tasks 46-49): `Logics/Temporal/Metalogic/Chronicle/` (10 files: RRelation.lean, Frame.lean, CanonicalChain.lean, OrderedSeedConsistency.lean, PointInsertion.lean, ChronicleConstruction.lean, CounterexampleElimination.lean, TruthLemma.lean, ChronicleToCountermodel.lean, ChronicleTypes.lean)
- Additional temporal metalogic support files: `TemporalContent.lean`, `WitnessSeed.lean`, `PropositionalHelpers.lean`, `GeneralizedNecessitation.lean`, `CompletenessHelpers.lean`
- Bimodal Theorems auxiliary files: `Logics/Bimodal/Theorems/Combinators.lean`, `Logics/Bimodal/Theorems/GeneralizedNecessitation.lean`, `Logics/Bimodal/Theorems/TemporalDerived.lean`
- Embedding infrastructure: `Logics/Bimodal/Embedding/` (ModalEmbedding, PropositionalEmbedding, TemporalEmbedding)

**Actually completed but listed in ROADMAP.md "Remaining":**
- "Temporal metalogic: DeductionTheorem, MCS, Soundness, Completeness" — this IS completed (task 31 + subtasks 46-49 closed all sorries)
  - Note: This entry in the Completed table reads: "Temporal metalogic: DeductionTheorem, MCS, Soundness, Completeness | Logics/Temporal/Metalogic/" which is CORRECT — it IS in the completed table already. But the Remaining table still lists:
    - "Dense temporal completeness" — NOT yet done (task 38, not_started)
    - "Discrete temporal completeness" — NOT yet done (task 39, not_started)
    - "Continuous temporal completeness" — NOT yet done (task 40, blocked)

**Remaining and correctly listed:**
- Discrete bimodal completeness (task 36): blocked, upstream sorries
- Continuous bimodal completeness (task 37): blocked, upstream not started
- Dense temporal completeness (task 38): NOT started (despite [COMPLETED] in TODO.md task detail — this is a TODO.md inconsistency; no code exists)
- Discrete temporal completeness (task 39): NOT started (same issue)
- Continuous temporal completeness (task 40): blocked
- Abstract shared completeness infrastructure (task 41): NOT started (despite [COMPLETED] in TODO.md task detail — same inconsistency)

### TODO.md / state.json Inconsistency

Tasks 38, 39, 41 show [COMPLETED] in their individual task detail blocks in TODO.md but:
1. state.json shows them as `"status": "not_started"`
2. The wave table at the top of TODO.md shows them as [NOT STARTED]
3. No code exists in the codebase for these items (no DenseCompleteness.lean, DiscreteCompleteness.lean, etc.)
4. The task descriptions in TODO.md that say [COMPLETED] appear to be stale metadata that wasn't cleaned up

**Conclusion**: Tasks 38, 39, 41 are genuinely NOT started. The [COMPLETED] markers in TODO.md task details are incorrect and should be fixed as part of the ROADMAP.md update.

### Current Mermaid Diagram Analysis

The current diagram:
```
subgraph F ["Foundations/Logic"]
    FC["Connectives\nProofSystem"]
    FT["Theorems/\nPropositional + Modal"]
    FM["Metalogic/\nConsistency"]
end
subgraph M ["Logics/Modal"]
    MB["Basic\n(Syntax + Kripke Semantics)"]
    MM["Metalogic\n(DeductionThm + MCS + Soundness + Completeness)"]
end
subgraph T ["Logics/Temporal"]
    TS["Syntax + Semantics\nProofSystem"]
    TT["Theorems"]
    TM["Metalogic\n(DeductionThm + MCS + Soundness + Completeness)"]
end
subgraph B ["Logics/Bimodal"]
    BS["Syntax + Semantics\nProofSystem"]
    BT["Theorems\n(incl. Perpetuity)"]
    BM["Metalogic\n(Core + Soundness + Bundle + Algebraic\nBXCanonical + Separation + ConservativeExt + Decidability)"]
end

FC --> MB
FC --> BS
FT --> MM
FT --> TT
FT --> BT
FM --> MM
FM --> TM
FM --> BM
MB --> MM
TS --> TM
TT -.->|theorem reuse| BT
BS --> BT
BS --> BM
BT --> BM
```

**Issues with the current diagram:**
1. Missing edge: `FC --> TS` — the Temporal module uses `Connectives` and `ProofSystem` from Foundations just as Bimodal does. The `TS` node imports `Foundations/Logic/ProofSystem.lean` and `Foundations/Logic/Connectives.lean`.
2. Missing edge: `FT --> TM` — Temporal metalogic imports from `Foundations/Logic/Theorems/` (propositional theorems). This is parallel to `FT --> MM`.
3. Missing edge: `MB --> MM` is present (correct). But there is no corresponding `TS --> TM` connection to Foundations Theorems.
4. The `TS` node combines "Syntax + Semantics + ProofSystem" — these are actually three separate subcomponents. The ROADMAP shows them as one node `TS`, but the Bimodal subgraph splits them more explicitly. This is a design choice that could be clarified.
5. The `BM` node description does NOT include "Soundness" explicitly even though `Logics/Bimodal/Metalogic/Soundness/` exists (it's separate from `FrameConditions`). The text "Core + Soundness + Bundle + Algebraic\nBXCanonical + Separation + ConservativeExt + Decidability" actually does include "Soundness" in the BM node, but the separate `FrameConditions/` directory also contains soundness-related items that feed into `BM`.
6. Missing edges for Bimodal: `FC --> TS` mirror pattern: there is no `FC --> TS` but there IS `FC --> BS`. Given that TS and BS are parallel, this asymmetry may be intentional or may be an omission.
7. The `Embedding/` module (`Logics/Bimodal/Embedding/`) exists in the codebase but has no node or edge in the diagram.

**Recommended diagram corrections:**
- Add `FC --> TS` edge (Foundations/Connectives + ProofSystem imported by Temporal)
- Add `FT --> TM` edge (Temporal metalogic imports Foundations propositional theorems)
- Consider whether to add a note about the Embedding module
- The `TM` node description is accurate — it does include the full metalogic

### Recommended ROADMAP.md Updates

#### Completed Table Updates

Add these rows to the "Completed" table:

| Component | Module |
|-----------|--------|
| Temporal syntax infrastructure (Context, BigConj, Subformulas) | `Logics/Temporal/Syntax/` |
| Temporal chronicle completeness pipeline (R-relation, point insertion, chronicle construction, truth lemma) | `Logics/Temporal/Metalogic/Chronicle/` |
| Bimodal embedding (PropositionalEmbedding, ModalEmbedding, TemporalEmbedding) | `Logics/Bimodal/Embedding/` |

Note: "Temporal metalogic: DeductionTheorem, MCS, Soundness, Completeness" is already in the Completed table and is correct — base completeness was achieved through tasks 31/46-49.

#### Remaining Table Updates

The Remaining table is essentially correct. The 6 items listed are genuinely not yet done:
1. Discrete bimodal completeness (blocked)
2. Continuous bimodal completeness (blocked)
3. Dense temporal completeness (not started)
4. Discrete temporal completeness (not started)
5. Continuous temporal completeness (blocked)
6. Abstract shared completeness infrastructure (not started, depends on 3+4+5)

However, items 3 and 4 should be distinguished from item 5 (blocked vs not started) for clarity.

#### Mermaid Diagram Updates

Add these edges:
```
FC --> TS     (Foundations feeds Temporal, mirroring FC --> BS)
FT --> TM     (Temporal metalogic uses Foundations theorems, mirroring FT --> MM)
```

No new nodes are needed — the existing nodes adequately represent the module structure.

#### Project Structure Tree Updates

The ROADMAP.md project structure tree is missing some new directories that were created:
- `Logics/Temporal/Metalogic/Chronicle/` with 10 files
- `Logics/Temporal/Metalogic/` additional support files (TemporalContent, WitnessSeed, PropositionalHelpers, GeneralizedNecessitation, CompletenessHelpers)
- `Logics/Bimodal/Embedding/` directory

The tree should be updated to reflect the current actual structure.

## Decisions

- The Completed/Remaining sections are the primary focus — the diagram corrections are secondary but important for accuracy.
- Tasks 38, 39, 41 TODO.md [COMPLETED] markers should be corrected to [NOT STARTED] as part of this update.
- The Project Structure tree should be updated to match the current filesystem.

## Risks & Mitigations

- **Risk**: Incorrectly marking tasks as complete when they are not.
  - **Mitigation**: Verify against actual code files before marking anything as complete. Confirmed Dense/Discrete temporal completeness does NOT exist.
- **Risk**: Missing edges in mermaid diagram could mislead about import structure.
  - **Mitigation**: Cross-reference with actual import statements in key files.

## Context Extension Recommendations

- **Topic**: Temporal metalogic completion status
- **Gap**: The chronicle-based completeness approach (tasks 46-49) is a major achievement not documented in ROADMAP.md
- **Recommendation**: Add a brief note in the Completed table about the chronicle pipeline

## Appendix

### Verification: No Dense/Discrete Temporal Completeness Files

```
find Cslib/ -name "*Dense*" -o -name "*Discrete*"
# Only returns bimodal files: DenseFMP.lean, DiscreteFMP.lean, DenseSoundness.lean, etc.
# No DenseCompleteness.lean or DiscreteCompleteness.lean in Temporal/
```

### Temporal Metalogic Chronicle Files (all new since ROADMAP was last updated)

```
Cslib/Logics/Temporal/Metalogic/Chronicle/
├── CanonicalChain.lean       (task 46)
├── ChronicleConstruction.lean (task 48)
├── ChronicleToCountermodel.lean (task 49)
├── ChronicleTypes.lean       (task 47/48)
├── CounterexampleElimination.lean (task 48)
├── Frame.lean                (task 46)
├── OrderedSeedConsistency.lean (task 46)
├── PointInsertion.lean       (task 47)
├── RRelation.lean            (task 46)
└── TruthLemma.lean           (task 49)
```

### Completed Tasks Not In ROADMAP.md Completed Table

- Task 15: Complete embedding lattice (atom simp lemmas, PL.toBimodal path)
- Task 16: Formula type consistency (DecidableEq on Modal.Proposition)
- Task 32: Fix untl/snce argument order convention (correct convention now matches Burgess 1982)
- Task 33: Audit noncomputable temporal instances (removed 39 unnecessary markers)
- Task 46: Temporal R-relation (Burgess Chronicle approach)
- Task 47: Temporal point insertion
- Task 48: Temporal chronicle construction
- Task 49: Temporal truth lemma + completeness (the big one)
