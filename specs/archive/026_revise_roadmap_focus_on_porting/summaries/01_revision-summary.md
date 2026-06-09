# Implementation Summary: Task #26

**Completed**: 2026-06-08
**Duration**: ~30 minutes

## Overview

Revised `specs/ROADMAP.md` to shift focus from TM bimodal logic theory to the
four-level porting effort (Propositional, Modal, Temporal, Bimodal). The document
now leads with the porting mission and modular factoring principle, treats all four
phases as first-class deliverables, and positions a brief TM background section
later in the document with a link to the BimodalLogic repository.

## What Changed

- `specs/ROADMAP.md` — Restructured section order and revised content:
  - **Removed**: "What is TM Bimodal Logic?" section from the leading position,
    including the Primitive Connectives table, Task Semantics paragraph, Axiom
    Systems table, and paper link (`possible_worlds.pdf`)
  - **Added**: Opening paragraph naming all four levels and the modular factoring
    principle; "What CSLib Gains" section with substantive per-level bullets
  - **Added**: "Background: TM Bimodal Logic" section (~10 lines) positioned after
    the porting mission and design sections, linking to the BimodalLogic repo
  - **Fixed**: BimodalLogic link from `ProofChecker` to
    `https://github.com/benbrastmckie/BimodalLogic`
  - **Reframed**: "Porting Phases" section to treat Phases 1–3 as standalone
    deliverables, not prerequisites; added framing sentence before Phase 4
  - **Revised**: Success metrics expanded to give equal weight to Propositional,
    Modal, and Temporal milestones
  - **Preserved**: Import hierarchy diagram, Current State of CSLib inventory,
    Task Dependency Structure wave table, Component Accounting table, Design
    Decisions section, and all other accurate content

## Decisions

- Removed the full axiom table (Base/Dense/Continuous/Discrete) from ROADMAP — it
  belongs in the BimodalLogic README, not in the CSLib porting roadmap
- Retained 2-3 sentences of TM description so a maintainer has enough context
  without needing to follow the external link
- Kept the wave table unchanged (no task number changes in scope)

## Plan Deviations

- None (implementation followed plan)

## Verification

- Build: N/A (markdown-only)
- Tests: N/A
- Files verified:
  - No `ProofChecker` URL in document: confirmed (grep returned no results)
  - No `possible_worlds.pdf` link: confirmed (grep returned no results)
  - BimodalLogic link correct: confirmed (`https://github.com/benbrastmckie/BimodalLogic`)
  - Opening paragraph names all four levels: confirmed
  - TM background section is ~10 lines, positioned after porting mission: confirmed
  - Wave table, component accounting, import hierarchy preserved: confirmed

## Notes

The revised ROADMAP reads as a four-level porting effort where the bimodal content
is the largest phase but not the only deliverable. Phases 1–3 (~6,800 lines) are
framed as independently valuable, and Phase 4 (~30,000 lines) is presented as
the culmination that depends on the earlier phases being complete.
