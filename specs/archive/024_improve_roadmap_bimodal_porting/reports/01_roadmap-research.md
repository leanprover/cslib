# Research Report: Task #24

**Task**: 24 - Improve ROADMAP.md with BimodalLogic porting overview
**Started**: 2026-06-08T00:00:00Z
**Completed**: 2026-06-08T01:00:00Z
**Effort**: Medium (3-5 hours)
**Dependencies**: Task 19 (completed - provided the modular factoring design)
**Sources/Inputs**: specs/ROADMAP.md, specs/TODO.md, BimodalLogic/ repository, CSLib Cslib/ source, task 19 summaries
**Artifacts**: specs/024_improve_roadmap_bimodal_porting/reports/01_roadmap-research.md
**Standards**: report-format.md

---

## Executive Summary

- The current ROADMAP.md contains a technically accurate but terse 4-phase porting plan. It is missing a narrative introduction that explains _what_ BimodalLogic is, _why_ it is being ported to CSLib, and _what the maintainer of CSLib needs to know_ to evaluate and act on these tasks.
- BimodalLogic (also known as the ProofChecker repository) contains ~84,547 lines of Lean 4 code covering TM bimodal logic: syntax, task semantics, a 42-axiom Hilbert proof system, and metalogic (soundness, completeness, decidability, separation, conservative extension). Of these, ~6,800 lines factor into reusable Foundations/Modal/Temporal modules; ~30,000+ lines are inherently bimodal and target `Cslib/Logics/Bimodal/`.
- The improved ROADMAP.md should open with: (1) a plain-English description of TM logic and its motivation, (2) the modular factoring rationale (design decisions), (3) what CSLib already has, (4) the task list with a link to TODO.md, and (5) the dependency wave structure and success metrics.

---

## Context & Scope

Task 24 is a documentation/markdown task. Its output is an improved `specs/ROADMAP.md` that a CSLib maintainer encountering the project for the first time could read and understand: what is being ported, from where, why it is organized the way it is, and what the current status is.

The research phase reads all primary sources and synthesizes them into a structured briefing. The implementation phase (task plan) will produce the actual new ROADMAP.md.

---

## Findings

### Current State of ROADMAP.md

The existing ROADMAP.md (178 lines, generated 2026-06-08 from task 19) contains:

- A phase-by-phase table (4 phases: Foundations, Modal+Temporal, Temporal Semantics, Bimodal)
- A dependency wave table
- Component accounting table
- Success metrics

**What is missing**:
1. No description of what TM bimodal logic _is_ or what the BimodalLogic repository contains
2. No explanation of _why_ this logic belongs in CSLib
3. No description of the modular factoring _rationale_ (why things go in Foundations vs. Bimodal)
4. No description of what CSLib already has today (current state)
5. No link to TODO.md for the detailed task list
6. No summary of the key design decisions (DeductionTheorem stays per-logic, diamond-avoidance pattern, etc.)
7. No note on the Zulip coordination / PR process (task 12)

### BimodalLogic Repository Overview

**Location**: `/home/benjamin/Projects/BimodalLogic/` (also on GitHub as `benbrastmckie/ProofChecker`)

**Scale** (from README.md):
- 246 Lean files
- ~84,547 lines of code
- ~41,584 comment lines
- Excludes Boneyard/ dead code

**Motivation**: BimodalLogic implements the **Bimodal Logic of Tense and Modality (TM)** — a formal system combining S5 modal operators with Since/Until linear tense operators. It supports verified reasoning about future contingency in non-deterministic dynamical systems via a **task semantics** that evaluates formulas at both a world-history and a time point.

**Paper**: "The Construction of Possible Worlds" (Brast-McKie, 2025) — provides the compositional semantics grounded in non-deterministic dynamical systems.

**Formula Language**: 5 primitive connectives: `⊥ (bot), → (imp), □ (box), U (until), S (since)`. All other operators are derived.

**Axiom Systems** (4 variants):
| System | Axioms | Standard Model | Status |
|--------|--------|----------------|--------|
| Base | 37 | — | Sound + Complete |
| Dense | 38 | ℚ | Sound + Complete |
| Continuous | 39 | ℝ | Incomplete |
| Discrete | 40 | ℤ | Sound + Completeness pending |

**Directory Structure**:
```
Theories/Bimodal/
├── Syntax/              # Formula, Atom, Context, BigConj, Subformulas (1,427 lines)
├── Semantics/           # TaskFrame, WorldHistory, TaskModel, Truth, Validity (1,822 lines)
├── ProofSystem/         # Axioms, Derivation, Derivable, Substitution (1,631 lines)
├── Theorems/            # Combinators, Propositional, ModalS4/S5, TemporalDerived, Perpetuity
│   ├── Combinators.lean         (675 lines)
│   ├── ContextualProofs.lean    (451 lines)
│   ├── GeneralizedNecessitation.lean (240 lines)
│   ├── ModalS4.lean             (468 lines)
│   ├── ModalS5.lean             (859 lines)
│   ├── TemporalDerived.lean     (788 lines)
│   ├── Perpetuity/              (2,051 lines — Bridge, Helpers, Principles)
│   └── Propositional/           (1,722 lines — Core, Connectives, Reasoning)
├── FrameConditions/     # Frame predicates, FrameClass type
└── Metalogic/           # Soundness, completeness, decidability, separation, conservative ext.
    ├── Core/            # DeductionTheorem, MCS theory (1,360 lines)
    ├── BXCanonical/     # Chronicle-based canonical model (2,605 lines)
    ├── Bundle/          # BFMCS base completeness construction (6,218 lines)
    ├── Decidability/    # Tableau, decision procedure, FMP (6,606 lines in core files)
    ├── WeakCanonical/   # Reynolds/Doets discrete pipeline (51,332 lines total)
    └── ConservativeExtension/ # Conservative extension result
```

**Active Sorry Obligations**: Discrete completeness (WeakCanonical/Separation/, WeakCanonical/Transfer.lean) — pending formalization of standard model-theoretic results (Doets 1989).

### CSLib Project Overview

**Location**: `/home/benjamin/Projects/cslib/`

**What CSLib is**: The Lean library for Computer Science, aiming to formalize CS theories and tools. Official: https://www.cslib.io/. Uses Lean 4 with Mathlib dependency.

**Current Logic Infrastructure** (already in CSLib):

```
Cslib/
├── Foundations/
│   └── Logic/
│       ├── Connectives.lean     # HasBot, HasImp, HasBox, HasUntil, HasSince typeclasses;
│       │                        # PropositionalConnectives, ModalConnectives, TemporalConnectives,
│       │                        # BimodalConnectives; LukasiewiczDerived
│       ├── ProofSystem.lean     # ModusPonens, Necessitation, TemporalNecessitation;
│       │                        # HasAxiom* typeclasses; PropositionalHilbert, ModalHilbert,
│       │                        # ModalS5Hilbert, TemporalBXHilbert; Propositional/Modal/
│       │                        # TemporalBX tag types
│       ├── Axioms.lean          # Axiom abbreviations (K, T, B, S4, S5, etc.)
│       ├── InferenceSystem.lean # InferenceSystem typeclass, DerivableIn
│       └── LogicalEquivalence.lean
├── Logics/
│   ├── Propositional/
│   │   ├── Defs.lean            # PL.Proposition inductive, derived connectives, Theory
│   │   ├── Embedding.lean       # PL -> Modal embedding (Proposition.toModal)
│   │   └── NaturalDeduction/Basic.lean
│   ├── Modal/
│   │   ├── Basic.lean           # Modal.Proposition inductive, Model (World, Atom, r, v),
│   │   │                        # Kripke semantics (Satisfies, Valid, entails)
│   │   ├── Cube.lean            # Modal logic cube relationships
│   │   └── Denotation.lean      # Denotational semantics
│   ├── Temporal/
│   │   └── Syntax/
│   │       └── Formula.lean     # Temporal.Formula inductive {atom,bot,imp,untl,snce},
│   │                            # TemporalConnectives instance
│   └── Bimodal/
│       ├── Syntax/
│       │   └── Formula.lean     # Bimodal.Formula inductive {atom,bot,imp,box,untl,snce},
│       │                        # BimodalConnectives instance
│       └── Embedding/
│           ├── ModalEmbedding.lean    # Modal.Proposition.toBimodal, simp lemmas, Coe instance
│           └── TemporalEmbedding.lean # Temporal.Formula.toBimodal
```

**What does NOT yet exist** (to be ported):
- `Cslib/Foundations/Logic/Theorems/` — propositional Hilbert theorems (Task 20)
- `Cslib/Logics/Modal/ProofSystem/` and `Modal/Theorems/` — modal DerivationTree + S4/S5 theorems (Task 21)
- `Cslib/Logics/Temporal/ProofSystem/` and `Temporal/Theorems/` and `Temporal/Semantics/` — temporal proof system, theorems, semantics (Tasks 22, 23)
- `Cslib/Logics/Bimodal/Syntax/` (beyond Formula.lean), `Bimodal/Semantics/`, `Bimodal/ProofSystem/`, `Bimodal/Theorems/`, `Bimodal/FrameConditions/`, `Bimodal/Metalogic/` (Tasks 2-11)

**Total Lean lines currently in CSLib**: ~25,588 (all modules)

### Design Decisions from Task 19 (Modular Factoring)

Task 19 (completed 2026-06-08) produced the key architectural insight through team research. The central finding was:

**Modular factoring principle**: Every component from BimodalLogic should live at the most general level it can compile at, to maximize reusability and minimize duplication.

**Where components live**:

| Component | Where | Rationale |
|-----------|-------|-----------|
| Combinators (I,B,C,S) | `Foundations/Logic/Theorems/` | Need only `[PropositionalHilbert S]`; no box/temporal |
| Propositional/{Core,Connectives,Reasoning} | `Foundations/Logic/Theorems/` | Pure propositional; usable by all four logics |
| ContextualProofs (weakening, cut) | `Foundations/Logic/Theorems/` | Pure propositional; generic `[PropositionalHilbert S]` |
| BigConj (generic version) | `Foundations/Logic/Theorems/` | Generic over `[PropositionalHilbert S]` |
| DeductionTheorem | `Bimodal/Metalogic/Core/` (per-logic) | Requires structural induction on concrete `DerivationTree` — cannot be ported generically |
| Modal.DerivationTree + ModalS5Hilbert instance | `Modal/ProofSystem/` | Pure modal; serves modal logic standalone |
| GeneralizedNecessitation + ModalS4/S5 theorems | `Modal/Theorems/` | Pure `[ModalHilbert S]` / `[ModalS5Hilbert S]` |
| Temporal axiom abbrevs + HasAxiom* typeclasses | `Foundations/Logic/ProofSystem.lean` additions | Infrastructure usable by both Temporal and Bimodal |
| TemporalBXHilbert restructuring | `Foundations/Logic/ProofSystem.lean` | Interface layer |
| Temporal.DerivationTree + TemporalBXHilbert instance | `Temporal/ProofSystem/` | Temporal standalone |
| TemporalDerived theorems | `Temporal/Theorems/` | Pure `[TemporalBXHilbert S]` |
| Temporal frame condition typeclasses | `Temporal/ProofSystem/` | Abstract typeclasses; usable by Temporal standalone |
| Temporal semantics on LinearOrder | `Temporal/Semantics/` | New infrastructure enabling standalone temporal soundness |
| Perpetuity theorems | `Bimodal/Theorems/Perpetuity/` | Uses both box and until/since; inherently bimodal |
| All bimodal-specific content | `Bimodal/` | Requires both modal and temporal constructors |

**Key design decisions**:

1. **DeductionTheorem stays per-logic** (Task 7, not Task 20): The deduction theorem requires structural induction on the concrete `DerivationTree` inductive. It cannot be ported generically to Foundations because `DerivationTree` is concrete, not typeclass-polymorphic. (Team research finding #7.)

2. **BimodalTMHilbert diamond-avoidance pattern** (Task 22): The `BimodalTMHilbert` typeclass extends individual temporal `HasAxiom*` classes directly (mirroring the `BimodalConnectives` pattern), providing a manual `TemporalBXHilbert` instance. This avoids the typeclass diamond that would arise from extending both `ModalHilbert` and `TemporalBXHilbert`.

3. **Task 5 scope reduction**: Perpetuity theorems reduced from ~7,300 lines to ~800 lines. All other derived theorem content (combinators, propositional, modal, temporal) was factored into Tasks 20-22.

4. **Temporal semantics as new infrastructure** (Task 23): The standalone temporal semantics on `LinearOrder` does not exist in BimodalLogic (which only has task frame semantics). It is new development that enables temporal soundness/completeness proofs without bimodal machinery.

### Task Dependency Structure and Wave Ordering

**6-wave dependency graph** (from TODO.md):

| Wave | Tasks | Unlocked by | Can start immediately? |
|------|-------|-------------|------------------------|
| 1 | 2, 12, 15, 16, 17, 18, 20, 24 | No logic-task dependencies | Yes |
| 2 | 3, 21, 22 | 2, 16, 20 | After Wave 1 |
| 3 | 4, 23 | 2, 20, 22 | After Wave 2 |
| 4 | 5, 6, 11 | 3, 4, 21, 22 | After Wave 3 |
| 5 | 7 | 4, 5 | After Wave 4 |
| 6 | 8, 9, 10 | 4, 5, 6, 7 | After Wave 5 |

**Foundations-first invariant**: Task 20 is Wave 1. Tasks 21 and 22 depend on Task 20. All bimodal tasks (Wave 3+) depend on at minimum Foundations (Task 20) or Temporal infrastructure (Task 22). This enforces: Foundations → Modal/Temporal → Bimodal.

**External dependency**: Task 2 has an external dependency on BimodalLogic:291 (toolchain upgrade in the source repository).

### Completed vs. Remaining Work

**Completed**:
- Task 19: Modular factoring research + task graph restructuring
- Formula types: `Bimodal.Formula`, `Temporal.Formula`, `Modal.Proposition`, `PL.Proposition` — all with derived connectives and `BimodalConnectives`/`TemporalConnectives`/`ModalConnectives`/`PropositionalConnectives` instances
- Embedding functions: `Modal.Proposition.toBimodal`, `Temporal.Formula.toBimodal` (with simp lemmas and `Coe` instances)
- Foundation connective typeclasses: full `HasBot/HasImp/HasBox/HasUntil/HasSince`, bundled classes, `LukasiewiczDerived`
- Proof system interface: `ModusPonens`, `Necessitation`, `HasAxiom*` typeclasses, `PropositionalHilbert`, `ModalHilbert`, `ModalS5Hilbert`, `TemporalBXHilbert` tags

**Not yet started (all 0 lines of proof code ported)**:
- Task 20: ~2,400 lines of propositional theorems to `Foundations/Logic/Theorems/`
- Task 21: ~1,600 lines of modal proof system + theorems to `Modal/ProofSystem/` + `Modal/Theorems/`
- Task 22: ~1,500 lines of temporal infrastructure to `Temporal/ProofSystem/` + `Temporal/Theorems/`
- Task 23: ~400-600 lines of new temporal semantics to `Temporal/Semantics/`
- Tasks 2-11: ~30,000+ lines of bimodal content to `Bimodal/`
- Task 12: CSLib PR coordination (planning complete, no PRs submitted yet)
- Tasks 15, 16: Small fixes (embedding completeness, formula type consistency)

---

## Decisions

- The improved ROADMAP.md should be written for a CSLib maintainer who has never read the BimodalLogic codebase. It should explain the mathematical content and motivation before the engineering details.
- The document should clearly link to `specs/TODO.md` for detailed task descriptions rather than duplicating all task descriptions.
- The phase/wave structure already in ROADMAP.md is correct and should be kept; the narrative introduction and design decisions sections need to be added.
- The current ROADMAP.md accurately reflects the architecture decided by task 19. The improved version should acknowledge task 19 as the design source while making the content accessible without reading the task 19 artifacts.

---

## Risks & Mitigations

- **Risk**: Making the document too long and detailed — it becomes hard to scan. **Mitigation**: Use a clear heading hierarchy. Put the "what is TM logic" narrative near the top; put line counts and detailed task specs further down. Use tables for the wave structure and component accounting.
- **Risk**: Outdated information — task statuses change as work proceeds. **Mitigation**: Keep status information in one place (TODO.md); the ROADMAP should describe the _plan_ and reference TODO.md for current status.
- **Risk**: Confusing the BimodalLogic directory structure (which uses `Theories/Bimodal/`) with the CSLib target structure (`Cslib/Logics/Bimodal/`). **Mitigation**: Use a clear source/target table for each module.

---

## Appendix

### Key Source Files Read

- `/home/benjamin/Projects/cslib/specs/ROADMAP.md` — current roadmap (178 lines)
- `/home/benjamin/Projects/cslib/specs/TODO.md` — full task list (452 lines)
- `/home/benjamin/Projects/BimodalLogic/README.md` — BimodalLogic overview
- `/home/benjamin/Projects/cslib/Cslib/Foundations/Logic/Connectives.lean` — typeclass infrastructure
- `/home/benjamin/Projects/cslib/Cslib/Foundations/Logic/ProofSystem.lean` — proof system typeclasses
- `/home/benjamin/Projects/cslib/Cslib/Logics/Bimodal/Syntax/Formula.lean` — Bimodal.Formula
- `/home/benjamin/Projects/cslib/Cslib/Logics/Temporal/Syntax/Formula.lean` — Temporal.Formula
- `/home/benjamin/Projects/cslib/Cslib/Logics/Bimodal/Embedding/ModalEmbedding.lean` — embedding
- `/home/benjamin/Projects/cslib/specs/019_explore_modular_logic_factoring/summaries/02_implementation-summary.md` — task 19 decisions

### BimodalLogic Line Counts (Active Modules, Excl. Boneyard)

| Module | Lines |
|--------|-------|
| Syntax/ | ~1,427 |
| Semantics/ | ~1,822 |
| ProofSystem/ | ~1,631 |
| Theorems/ (top-level) | ~3,569 |
| Theorems/Perpetuity/ | ~2,051 |
| Theorems/Propositional/ | ~1,722 |
| Metalogic/Core/ | ~1,360 |
| Metalogic/BXCanonical/ | ~2,605 |
| Metalogic/Bundle/ | ~6,218 |
| Metalogic/Decidability/ (core) | ~6,606 |
| Metalogic/WeakCanonical/ (total) | ~51,332 |
| **Total (active)** | **~84,547** |

Note: The WeakCanonical/ total includes the large Separation/Hierarchy/ files which contain the pending sorry obligations for discrete completeness.
