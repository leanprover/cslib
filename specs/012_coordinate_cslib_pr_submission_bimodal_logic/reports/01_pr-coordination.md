# Research Report: Task #12 — Coordinate cslib PR Submission

**Task**: 12 - Coordinate cslib PR submission for Bimodal Logic integration
**Started**: 2026-06-08T00:45:00Z
**Completed**: 2026-06-09T00:30:00Z
**Effort**: Ongoing (tracked separately)
**Dependencies**: None (runs in parallel with tasks 2-23)
**Sources/Inputs**: CONTRIBUTING.md, GOVERNANCE.md, ORGANISATION.md, README.md, lakefile.toml, Cslib/Init.lean, existing Formula.lean, state.json, TODO.md
**Artifacts**: specs/012_coordinate_cslib_pr_submission_bimodal_logic/reports/01_pr-coordination.md
**Standards**: report-format.md

---

## Executive Summary

- cslib is an independent Lean 4 CS library hosted at `github.com/leanprover/cslib` (not a Mathlib fork), with its own maintainer team and contribution process
- The project explicitly welcomes logic contributions (temporal logic, modal logics listed as target areas); Zulip pre-coordination is mandatory for "major developments" before any PR
- CI requires: `lake build` (zero errors), `lake test`, `lake exe checkInitImports`, `lake lint`, `lake exe lint-style`, `lake shake --add-public --keep-implied --keep-prefix`, zero sorry, Apache 2.0 headers, and PR titles prefixed with `feat:` / `fix:` etc.
- Recommended approach: open a Zulip thread first (proposing modular architecture + 14-PR wave plan), confirm namespace with maintainers, then proceed wave by wave

---

## Context and Scope

This task coordinates submission of 14 PRs to the cslib repository:
- 4 standalone module PRs: PR-Foundations (task 20), PR-Modal (task 21), PR-Temporal-Infra (task 22), PR-TempSem (task 23)
- 10 Bimodal porting PRs: tasks 2-11

The research covers the cslib contribution model, CI requirements, namespace conventions, PR process, and Zulip coordination protocol.

---

## Findings

### Repository Identity

cslib (`github.com/leanprover/cslib`) is **not** a Mathlib fork. It is an independent library for formalising Computer Science theories in Lean 4. It depends on Mathlib as a library (`require mathlib`) but is a distinct project with its own governance. PRs go to `leanprover/cslib`, not to Mathlib.

Key links:
- GitHub: https://github.com/leanprover/cslib
- Zulip: https://leanprover.zulipchat.com/ (CSLib channels)
- Website: https://www.cslib.io/
- Open contribution board: https://github.com/leanprover/cslib/projects?query=is%3Aopen

### Contribution Model

1. **PR required for all changes** — each PR needs approval by at least one relevant maintainer
2. **Pre-coordination for major work** — explicitly required for "major developments" via Zulip or GitHub issue before starting. The contribution guide calls out new frameworks, cross-cutting abstractions, and new topic areas as requiring prior discussion.
3. **AI use disclosure** — cslib follows the Mathlib AI policy: if AI tools are used, explain which tools and how in the PR description. This is mandatory and important for our use case.
4. **Working groups** — cslib organises sustained work via working groups with a Zulip channel. For a 14-PR bimodal integration, proposing a working group is appropriate (see below).

### Key Maintainers to Engage

- **Lead**: Fabrizio Montesi (@fmontesi) — University of Southern Denmark
- **Area**: Kim Morrison (@kim-em) — CI/CD, Lean FRO
- **Technical leads**: Alexandre Rademaker (@arademaker), Sorrachai Yingchareonthawornchai (@sorrachai)
- **Reviewers**: Eric Wieser (@eric-wieser) — Google DeepMind (strong Lean/Mathlib background), Thomas Waring (@thomaskwaring)

The logic contributions most naturally fall under @fmontesi's area (logics are explicitly listed in the ORGANISATION.md and CONTRIBUTING.md Logics section).

### Namespace Decision

Current cslib structure under `Cslib/Logics/`:
- `Bimodal/` — exists, contains `Syntax/Formula.lean` + embeddings
- `Modal/` — exists
- `Temporal/` — exists
- `HML/`, `LinearLogic/`, `Propositional/`

The current namespace in Formula.lean is `Cslib.Logic.Bimodal` (note: `Logic` not `Logics`). The directory is `Cslib/Logics/` but the namespace uses `Logic`. This inconsistency should be clarified with maintainers before starting the porting tasks.

Target namespaces to confirm:
- `Cslib.Foundations.Logic.*` for propositional theorems (task 20)
- `Cslib.Logic.Modal.*` or `Cslib.Logics.Modal.*` for modal (task 21)
- `Cslib.Logic.Temporal.*` or `Cslib.Logics.Temporal.*` for temporal (tasks 22-23)
- `Cslib.Logic.Bimodal.*` for bimodal (tasks 2-11)

**This is the most critical question to resolve via Zulip before starting task 2.**

### CI Requirements (from CONTRIBUTING.md and lakefile.toml)

| Check | Command | Notes |
|-------|---------|-------|
| Build | `lake build` | Zero errors required |
| Tests | `lake test` | CslibTests suite |
| Init imports | `lake exe checkInitImports` | All files must import `Cslib.Init` |
| Environment linters | `lake lint` | Mathlib-style linters |
| Text linters | `lake exe lint-style` | Auto-fixable with `--fix` |
| Import shake | `lake shake --add-public --keep-implied --keep-prefix` | Minimize imports |
| Syntax linters | (appear during `lake build`) | `linter.all` warnings |
| Sorry check | `grep -r sorry` | Zero sorry in submitted files |
| Copyright headers | Manual | Apache 2.0 format |

The `lakefile.toml` shows `leanOptions` with `weak.linter.mathlibStandardSet = true`, meaning Mathlib's standard linter set applies. Some linters are explicitly disabled (pythonStyle, checkInitImports as `weak` — but checkInitImports is tested via the `lake exe checkInitImports` script separately).

**Per-file checklist for every ported file:**
1. Add copyright header: `Copyright (c) 2026 [Authors]. All rights reserved. / Released under Apache 2.0 license as described in the file LICENSE. / Authors: [names]`
2. Add `public import Cslib.Init` (first import, before any other)
3. Add `module` keyword (or `module -- shake: keep-all` if needed)
4. Update namespace to cslib convention
5. Run `lake shake` locally (use `-- shake: keep` comments for tactic-required imports)
6. Run `lake lint` locally
7. Run `lake build` with zero errors
8. Confirm zero sorry

### PR Title Convention

Required prefix from `feat`, `fix`, `doc`, `style`, `refactor`, `test`, `chore`, `perf`. Optionally followed by `(area)`:

Examples for our PRs:
- `feat(Foundations/Logic): add Hilbert theorem infrastructure (Combinators, Propositional, ContextualProofs, BigConj)`
- `feat(Logics/Modal): add Modal proof system and theorems (DerivationTree, S4/S5, GenNec)`
- `feat(Logics/Temporal): add Temporal proof system infrastructure and theorems`
- `feat(Logics/Bimodal): add Bimodal syntax infrastructure (Context, BigConj, Subformulas)`

### PR Size Guidelines

CONTRIBUTING.md does not state an explicit line limit but emphasizes "keeping PRs small and self-contained." Based on analogous projects (Mathlib typically prefers PRs under 500 lines; cslib is less strict): aim for 1,500-3,500 lines per PR. The Decidability PR (task 9, ~10k lines) should be proactively discussed with maintainers and may need to be split into 9a (Core tableau/decision procedure) and 9b (FMP).

### Zulip Coordination Protocol

From CONTRIBUTING.md, the recommended Zulip channels:
- `#CSLib` channels for general coordination
- `#CSLib: Code Reasoning` exists for the Boole area
- For logics: likely `#CSLib` general or a new channel to propose

**Proposed working group proposal format** (Zulip message or GitHub issue):
- **Topic**: Bimodal Temporal Logic (TM) formalization
- **Execution plan**: 14-PR wave structure (4 standalone + 10 bimodal), dependency order outlined
- **Collaborators**: Benjamin Brastmckie (author of BimodalLogic source)
- Include: brief description of TM logic (S5 modal + linear temporal over task frames), motivation (verified decision procedure, completeness, ~30k lines from BimodalLogic), overview of modular architecture (Foundations → Modal/Temporal → Bimodal)

### PR Wave Submission Order

**Wave 1 (independent, start after Zulip confirmation):**
- PR-Foundations (task 20): ~2,400 lines to `Cslib/Foundations/Logic/Theorems/`

**Wave 2 (after PR-Foundations merged):**
- PR-Modal (task 21): ~1,600 lines to `Cslib/Logics/Modal/ProofSystem/` + `Theorems/`
- PR-Temporal-Infra (task 22): ~1,500 lines to `Cslib/Logics/Temporal/ProofSystem/` + `Theorems/`
- PR-Bimodal-Syntax (task 2): ~2,500 lines to `Cslib/Logics/Bimodal/Syntax/` (independent of tasks 20-22 if namespace confirmed)

**Wave 3 (after Wave 2 merged):**
- PR-TempSem (task 23): ~400-600 lines
- PR-Semantics (task 3): ~2,200 lines to `Cslib/Logics/Bimodal/Semantics/`
- PR-ProofSystem (task 4): ~2,000 lines (depends on 2, 20, 22)

**Wave 4:**
- PR-FrameConditions (task 6): ~2,370 lines (depends on 3, 4)
- PR-Perpetuity (task 5): ~800 lines (depends on 4, 21, 22)
- PR-ConservativeExt (task 11): ~1,500 lines (depends on 4) — independent of 5-9

**Wave 5:**
- PR-MCS (task 7): ~2,500 lines (depends on 4, 5)

**Wave 6:**
- PR-Completeness (task 8): ~15,000+ lines (depends on 6, 7) — discuss size/splitting proactively
- PR-Decidability (task 9): ~10,000 lines (depends on 4, 7) — plan to split 9a/9b
- PR-Separation (task 10): ~3,500 lines (depends on 4, 5, 7)

### Review Cycle Management

- Address reviewer feedback within 48 hours to maintain momentum
- For any PR under active review, do not submit the dependent PR until review is complete
- The completeness PR (task 8) contains a sorry in the chronicle construction; port it as-is and include an issue/note in the PR description. Maintainers may request it be removed before merging.
- Track review status in this task (task 12) by updating the PR submission order section

---

## Decisions

1. **cslib is the correct target** — not Mathlib. PRs go to `github.com/leanprover/cslib`.
2. **Zulip pre-coordination is mandatory** — must happen before submitting PR-Bimodal-Syntax (task 2).
3. **Namespace inconsistency to resolve** — `Cslib.Logic.*` vs `Cslib.Logics.*` must be confirmed with maintainers.
4. **AI usage disclosure required** — include in every PR description which AI tools were used.
5. **Working group proposal recommended** — for a 14-PR effort, proposing a working group is the right coordination mechanism.
6. **Completeness sorry requires disclosure** — flag in PR 8 description and track as a known open item.

---

## Risks and Mitigations

| Risk | Likelihood | Mitigation |
|------|------------|------------|
| Namespace rejection/change after work started | Medium | Confirm namespace via Zulip before task 2 starts |
| Maintainer requests architectural changes | Medium | Open Zulip thread early; get buy-in on modular architecture |
| Large PRs (tasks 8, 9) require splitting | High | Pre-plan 9a/9b split; check with maintainers on 8 before submitting |
| Sorry in completeness proof (task 8) blocks merge | High | Flag proactively in PR description; track BimodalLogic:sorry-elimination upstream |
| Review latency stalls dependent PRs | Medium | Submit PRs early; ping Zulip after 1 week without review |
| AI use policy creates review friction | Low | Disclose clearly in every PR description per Mathlib AI policy |
| lakefile.toml linter incompatibilities | Low | Run full CI suite locally before each PR submission |

---

## Context Extension Recommendations

- **Topic**: cslib contribution workflow patterns
- **Gap**: No documented context file for cslib-specific PR submission conventions (CI commands, PR title format, Zulip coordination protocol)
- **Recommendation**: Create `.claude/context/project/cslib-contribution-guide.md` summarizing CI checklist, PR title format, and Zulip coordination steps for reuse across all porting tasks

---

## Appendix

### CI Command Reference (run locally before each PR)

```bash
# From cslib repo root:
lake build                                    # Must pass with zero errors
lake test                                     # Run CslibTests
lake exe checkInitImports                     # All files import Cslib.Init
lake lint                                     # Environment linters
lake exe lint-style                           # Text linters (use --fix to auto-fix)
lake shake --add-public --keep-implied --keep-prefix  # Minimize imports
grep -r "sorry" Cslib/Logics/Bimodal/        # Zero sorry check
```

### Copyright Header Template

```lean
/-
Copyright (c) 2026 Benjamin Brastmckie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brastmckie
-/
```

### Zulip Working Group Proposal Template

**Zulip message draft** (post to `#CSLib` or `#new streams` channel):

> **Proposal: Bimodal Temporal Logic (TM) working group / PR series**
>
> I'm planning to contribute a formalization of Bimodal Temporal Logic (TM) to cslib. TM combines S5 modal logic with linear temporal logic (Until/Since) over task frames, and has a verified decision procedure (tableau), completeness proof, and separation theorem — approximately 30,000 lines of Lean 4 from the BimodalLogic project.
>
> **Proposed structure** (modular, 14 PRs):
> - Wave 1: Propositional Hilbert theorems to `Cslib/Foundations/Logic/Theorems/` (~2,400 lines)
> - Wave 2: Modal proof system + theorems (~1,600), Temporal infrastructure + theorems (~1,500), Bimodal syntax (~2,500)
> - Waves 3-6: Bimodal semantics, proof system, soundness, completeness, decidability, separation
>
> **Questions before starting:**
> 1. Namespace: should I use `Cslib.Logic.Bimodal.*` or `Cslib.Logics.Bimodal.*`? (I see `Cslib.Logic.Bimodal` in existing Formula.lean but the directory is `Cslib/Logics/Bimodal/`)
> 2. Would a working group with a dedicated Zulip channel be appropriate for coordinating this?
> 3. Any concerns about scope / placement in the library?
>
> Note: portions of this formalization were developed with AI assistance (Claude); I will disclose this in each PR description per the Mathlib AI policy.

### References

- CONTRIBUTING.md: `/home/benjamin/Projects/cslib/CONTRIBUTING.md`
- GOVERNANCE.md: `/home/benjamin/Projects/cslib/GOVERNANCE.md`
- ORGANISATION.md: `/home/benjamin/Projects/cslib/ORGANISATION.md`
- lakefile.toml: `/home/benjamin/Projects/cslib/lakefile.toml`
- CSLib whitepaper: https://arxiv.org/abs/2602.04846
- Mathlib AI policy: https://leanprover-community.github.io/contribute/index.html#use-of-ai
- Mathlib style guide: https://leanprover-community.github.io/contribute/style.html
