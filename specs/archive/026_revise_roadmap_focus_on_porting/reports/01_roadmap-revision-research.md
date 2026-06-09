# Research Report: Task #26 — Revise ROADMAP.md to Focus on Porting

**Task**: 26 - Revise ROADMAP.md to focus on porting across all four logic levels
**Started**: 2026-06-09
**Completed**: 2026-06-09
**Effort**: ~1 hour
**Dependencies**: Task 24 (completed — prior ROADMAP rewrite)
**Sources/Inputs**: specs/ROADMAP.md, specs/TODO.md, Cslib/ source tree, BimodalLogic/ source tree and README, specs/019_explore_modular_logic_factoring/reports/01_factoring-synthesis.md
**Artifacts**: specs/026_revise_roadmap_focus_on_porting/reports/01_roadmap-revision-research.md
**Standards**: report-format.md

---

## Executive Summary

- The current ROADMAP.md (written by Task 24) devotes its opening section to a detailed technical explanation of TM bimodal logic — operators, task semantics, and axiom systems — with the rest of the document focused on bimodal porting phases
- The revision should lead with the *porting effort across all four levels* (Propositional, Modal, Temporal, Bimodal) and treat the bimodal theory description as background context, not the central topic
- The correct GitHub link for BimodalLogic is `https://github.com/benbrastmckie/BimodalLogic` — the paper link must NOT appear in the revised ROADMAP
- The revised ROADMAP should reflect that Tasks 20 (Foundations), 21 (Modal), 22–23 (Temporal) are just as important to the porting effort as Tasks 2–11 (Bimodal)

---

## Context & Scope

Task 24 (completed 2026-06-08) rewrote ROADMAP.md from scratch to provide a comprehensive overview of the BimodalLogic → CSLib porting project. The user's feedback: the document is **too focused on the Bimodal/ theory**. The revision (Task 26) must rebalance the document so that all four logic levels receive equal emphasis, with TM bimodal logic background present but as secondary context rather than the leading topic.

### What the current ROADMAP gets right

- Accurate modular factoring design decisions
- Correct task dependency structure (6-wave graph)
- Correct component accounting table
- Correct "Current State of CSLib" inventory
- Correct import hierarchy diagram
- Correct success metrics

### What must change

1. **Leading section "What is TM Bimodal Logic?"** — This is 30+ lines of technical detail (operators, task semantics, axiom systems) placed *before* the rationale for porting. It should be moved to a later position and trimmed, with the link to BimodalLogic serving as the pointer for readers who want full details. The paper link (`possible_worlds.pdf`) must be removed entirely.

2. **"Why Port to CSLib?" section** — This is good but should be expanded into the primary narrative, leading with the four-level structure: Foundations (propositional), Modal, Temporal, Bimodal. Currently the section is a brief paragraph that only mentions the four levels in passing.

3. **"Porting Phases"** — The phases are accurately described, but the framing treats "Phase 1: Foundations" and "Phase 2: Modal and Temporal" as preliminary setup before the "real" bimodal work. The revised framing should treat each phase as a valuable deliverable in its own right, not as scaffolding for the bimodal port.

4. **Title/opening** — The title "Porting BimodalLogic to CSLib" is accurate but should be followed immediately by a sentence that names all four levels, not a technical description of bimodal logic.

---

## Findings

### 1. Current ROADMAP Structure (Problem Analysis)

The current document structure:
```
Title: Porting BimodalLogic to CSLib
1. What is TM Bimodal Logic?        ← 30+ lines technical detail
   - Primitive Connectives (table)
   - Task Semantics (paragraph)
   - Axiom Systems (table)
2. Why Port to CSLib?               ← Brief (1 paragraph)
3. Design Decisions (Modular Factoring)
4. Import Hierarchy
5. Current State of CSLib
6. Porting Phases
   - Phase 1: Foundations (Task 20)
   - Phase 2: Modal and Temporal (Tasks 21, 22)
   - Phase 3: Temporal Semantics (Task 23)
   - Phase 4: Bimodal Porting (Tasks 2–11)
7. Task Dependency Structure
8. Component Accounting
9. Success Metrics
```

The problem: ~40% of the opening content is about TM bimodal logic theory (operators, semantics, axioms). A reader sees technical logic before understanding why they should care about the porting effort.

### 2. The Four Logic Levels and Their Tasks

From the codebase and TODO.md:

| Level | CSLib Target | Tasks | Lines | Status |
|-------|-------------|-------|-------|--------|
| **Propositional** | `Foundations/Logic/Theorems/` | 20 | ~2,400 | NOT STARTED |
| **Modal** | `Logics/Modal/ProofSystem/` + `Modal/Theorems/` | 16, 21 | ~1,600 | NOT STARTED |
| **Temporal** | `Logics/Temporal/ProofSystem/` + `Temporal/Theorems/` + `Temporal/Semantics/` | 22, 23 | ~1,500 + ~400–600 new | NOT STARTED |
| **Bimodal** | `Logics/Bimodal/` | 2–11 | ~30,000+ | NOT STARTED |

The Propositional, Modal, and Temporal levels together represent ~5,500–6,100 lines — entirely extractable and reusable components that benefit any logic that uses the Foundations layer. These deserve prominent treatment.

### 3. What BimodalLogic Contains (Source Map)

From reading the BimodalLogic source tree (`Theories/Bimodal/`):

**Maps to Foundations (Propositional):**
- `Theorems/Combinators.lean` → `Foundations/Logic/Theorems/Combinators.lean`
- `Theorems/ContextualProofs.lean` → `Foundations/Logic/Theorems/ContextualProofs.lean`
- `Syntax/BigConj.lean` (generic part) → `Foundations/Logic/Theorems/BigConj.lean`
- `Theorems/` Propositional/{Core,Connectives,Reasoning} → `Foundations/Logic/Theorems/Propositional/`

**Maps to Modal level:**
- `Theorems/ModalS4.lean` + `Theorems/ModalS5.lean` → `Logics/Modal/Theorems/`
- `Theorems/GeneralizedNecessitation.lean` → `Logics/Modal/Theorems/`
- `ProofSystem/Derivation.lean` (modal fragment) → `Logics/Modal/ProofSystem/`

**Maps to Temporal level:**
- `Theorems/TemporalDerived.lean` → `Logics/Temporal/Theorems/`
- `FrameConditions/FrameClass.lean` (linear/dense/discrete) → `Logics/Temporal/Theorems/`
- Temporal `ProofSystem.lean` extensions → `Logics/Temporal/ProofSystem/`
- `Semantics/` (new standalone version) → `Logics/Temporal/Semantics/` (Task 23: new infrastructure, not a direct port)

**Maps to Bimodal level (inherently bimodal):**
- `Syntax/` (Formula, Context, Subformulas, BigConj concrete)
- `Semantics/` (TaskFrame, WorldHistory, TaskModel, Truth, Validity)
- `ProofSystem/` (42-axiom Hilbert system, DerivationTree, Derivable)
- `Theorems/Perpetuity.lean`
- `FrameConditions/` (bimodal frame soundness)
- `Metalogic/` (Core: MCS/DeductionTheorem; Bundle/BXCanonical: completeness; Decidability: tableau)

### 4. BimodalLogic Repository Description

From the BimodalLogic README: The repository is at `https://github.com/benbrastmckie/BimodalLogic` (the README shows the CI badge pointing to `benbrastmckie/ProofChecker` but the repository URL per the task description is `https://github.com/benbrastmckie/BimodalLogic`).

The README describes TM as "a bimodal fragment of the Logos" implementing soundness and completeness for reasoning about future contingency in non-deterministic dynamical systems. It covers 246 Lean files, ~84,547 lines.

**Key point**: The ROADMAP should link to `https://github.com/benbrastmckie/BimodalLogic` as the pointer for readers who want full technical detail on TM. The paper link must NOT appear.

### 5. Modular Factoring Rationale (from Task 19)

The central principle from Task 19: **Every component lives at the most general level it can compile at.**

This means the porting effort is NOT primarily about getting bimodal content into CSLib — it is about identifying which content is purely propositional, purely modal, purely temporal, and using that analysis to maximize reusability. The bimodal content is the *largest* portion but not the most architecturally significant.

The revised ROADMAP should lead with this principle and show how it drives the four-level structure, rather than leading with bimodal theory.

### 6. What the DeductionTheorem Decision Shows

One design decision (DeductionTheorem stays per-logic, not in Foundations) illustrates the modular factoring principle well: even though DeductionTheorem is propositionally stated, it requires structural induction over the concrete `DerivationTree` inductive, which is per-logic. This is a useful example of WHY careful classification is needed — and it belongs under Design Decisions, not in the TM theory description.

---

## Recommendations for Revised ROADMAP

### Structure

```
Title: Porting BimodalLogic to CSLib

[Opening: What this effort is — 2 sentences naming all four levels]

## Overview
[The porting mission: extract and organize ~84,547 lines from BimodalLogic 
into four standalone CSLib modules. Named link to BimodalLogic repo.]

## Modular Factoring Design
[Central principle + component placement table — moved earlier]

## What CSLib Gains
[What each of the four levels contributes, treated as equal deliverables]

## Background: TM Bimodal Logic
[Trimmed description: ~10 lines max. Link to BimodalLogic for full detail.
NO paper link. Explain what TM is, why it motivated the four-level structure.]

## Import Hierarchy
[The existing diagram is correct — keep it]

## Current State of CSLib
[Existing inventory — keep it]

## Porting Phases
[All four phases treated as first-class deliverables]

## Task Dependency Structure
[Existing wave table — keep it]

## Component Accounting
[Existing table — keep it]

## Success Metrics
[Revise to include Modal and Temporal milestones more prominently]
```

### Key Content Changes

1. **Remove the paper link** from `## What is TM Bimodal Logic?`
2. **Move TM background** to a later section titled "Background: TM Bimodal Logic"
3. **Trim TM background** to ~10 lines: what TM is, pointer to BimodalLogic repo
4. **Lead with the four-level porting mission** — the opening section should name Propositional, Modal, Temporal, and Bimodal equally
5. **Expand "Why Port to CSLib?"** into an "What CSLib Gains" section that gives each level a bullet point
6. **Reframe Phases 1–3** as valuable standalone deliverables, not just prerequisites for bimodal porting
7. **Correct the BimodalLogic link** — use `https://github.com/benbrastmckie/BimodalLogic` (the current ROADMAP links to `https://github.com/benbrastmckie/ProofChecker` which is the old name)

### Tone Guidance

The current ROADMAP reads as "here is the bimodal logic system we want to port." The revised ROADMAP should read as "here is a modular porting effort that produces four standalone libraries, the largest of which happens to be a bimodal logic." The end result matters (bimodal), but the architectural principle (modularity) and the intermediate deliverables (Foundations, Modal, Temporal) are what make the effort interesting to a CSLib maintainer.

---

## Decisions

- The correct link for BimodalLogic is `https://github.com/benbrastmckie/BimodalLogic`
- No link to the paper should appear anywhere in the revised ROADMAP
- The TM description should be trimmed to ~10 lines and positioned as background (after the porting mission is established)
- All four levels (Propositional/Modal/Temporal/Bimodal) should be named in the opening paragraph
- The modular factoring principle ("every component lives at its most general level") should appear early

---

## Risks & Mitigations

- **Risk**: Trimming TM background too aggressively loses context a maintainer needs. **Mitigation**: Retain 2–3 sentences about what TM is (S5 modal + Since/Until tense operators) and link to BimodalLogic for the full formal description.
- **Risk**: The revised document loses the useful axiom table. **Mitigation**: The axiom table (Base/Dense/Continuous/Discrete) belongs in the BimodalLogic repo README, not in the CSLib ROADMAP. Remove it.
- **Risk**: Phase 4 (bimodal, ~30,000 lines) still dominates by line count. **Mitigation**: Frame the phases section with a note that Phase 4 is the largest by volume but Phases 1–3 complete first and unlock Phase 4.

---

## Context Extension Recommendations

- None identified. The ROADMAP revision is scoped to a single document and requires no new context files.
