# Research Report: Task #1

**Task**: Integrate BimodalLogic results into cslib
**Date**: 2026-06-08
**Mode**: Team Research (4 teammates)

## Summary

BimodalLogic is a large Lean 4 library (~211 source files, ~85k lines) formalizing bimodal temporal logic TM — combining S5 modal logic with linear temporal operators (Until/Since) over task frame semantics. It contains a substantial sorry-free core (~87 files, ~50k lines) covering Syntax, Semantics, a Hilbert proof system (42 axioms), Soundness (base/dense/discrete), MCS theory, Decidability via analytic tableaux, Finite Model Property, Separation theorem, and Conservative Extension. The advanced completeness modules (Bundle, BXCanonical, WeakCanonical) have ~35 active sorries across 11 files. cslib explicitly welcomes temporal logic contributions (listed in CONTRIBUTING.md), has no temporal logic content, and the existing Modal module (~270 lines, 3 files) uses a different architecture that won't conflict. Integration requires significant adaptation: Lean 4.27→4.31 toolchain upgrade, full namespace rename, `module`/`public import`/`@[expose]` adoption, copyright headers, Mathlib-style linting, and documentation. We recommend 10 modular PRs ordered by dependency, targeting `Cslib/Logics/Temporal/`.

## Key Findings

### Primary Approach (from Teammate A)

BimodalLogic's `Formula` type uses 6 primitive constructors (atom, bot, imp, box, untl, snce) with ~20 derived operators. The proof system has 42 axiom constructors organized across 8 layers (propositional, S5 modal, BX temporal, interaction, uniformity, Prior, Z1, density) with frame class classification. Semantics uses task frames with world histories parameterized over an ordered additive commutative group D.

cslib's existing `Cslib.Logics.Modal` is fundamentally different — simpler `Proposition` type (atom/neg/and/diamond), semantic `Satisfies` relation, no proof system. The two do not conflict; BimodalLogic content belongs in a new directory, not merged into Modal.

Teammate A proposed a 3-tier classification:
- **Tier 1** (standalone, sorry-free): Syntax, ProofSystem, Semantics, Soundness, MCS Core (~6 PRs)
- **Tier 2** (sorry-free, larger): Theorems, Decidability, FrameConditions, Substitution
- **Tier 3** (has sorries, future): Bundle, BXCanonical, WeakCanonical, some Theorems

### Alternative Approaches (from Teammate B)

Teammate B produced a complete 9-layer dependency graph and proposed 10 ordered PRs:

| PR | Content | Lines | Dependencies | Sorry-free |
|----|---------|-------|--------------|------------|
| 1 | Temporal Syntax (Atom, Formula, Context, BigConj, Subformulas) | ~2,500 | Mathlib only | Yes |
| 2 | Task Frame Semantics (TaskFrame, WorldHistory, TaskModel, Truth, Validity) | ~2,200 | PR 1 | Yes |
| 3 | Proof System (Axioms, Derivation, Derivable, Substitution, Linearity) | ~2,000 | PR 1 | Yes |
| 4 | Derived Theorems — Propositional/Modal (Combinators, Propositional/*, ContextualProofs) | ~3,000 | PR 3 | Yes |
| 5 | Frame Conditions + Soundness (FrameClass, SoundnessLemmas, Dense/Discrete Soundness) | ~3,500 | PR 2 + PR 3 | Yes |
| 6 | Deduction Infrastructure + MCS Theory (DeductionTheorem, MCS, RestrictedMCS) | ~2,500 | PR 3 + PR 4 | Yes |
| 7 | Strong Completeness | ~520 | PR 5 + PR 6 | Yes |
| 8 | Decidability + Tableau + FMP (SignedFormula, Tableau, Closure, Saturation, FMP/*) | ~10,000 | PR 3 + PR 6 | Yes |
| 9 | Separation Theorem (WeakCanonical/Separation/* — 11 files) | ~3,500 | PR 3 + PR 4 + PR 6 | Yes |
| 10 | Conservative Extension (ExtFormula, ExtDerivation, Substitution, Lifting) | ~1,500 | PR 3 | Yes |

Suggested PR title format: `feat(Logics/Temporal): bimodal temporal logic syntax`

Namespace mapping: `Bimodal.* → Cslib.Logic.Temporal.*`

### Gaps and Shortcomings (from Critic)

**35 active sorries** in 11 files (plus 29 in excluded Boneyard):
- `Bundle/SuccRelation.lean` (7), `BXCanonical/Chronicle/ChronicleToCountermodel.lean` (6), `WeakCanonical/TruthLemma.lean` (6), `WeakCanonical/EFGames/StaviCompleteness.lean` (3), `Bundle/SuccExistence.lean` (3), plus 5 more files with 1 each

**Critical risks identified:**
1. Lean 4.27→4.31 is a 4-version gap; `module`, `public import`, `@[expose] public section` all need adding
2. No copyright headers in BimodalLogic; cslib requires Apache 2.0 with named authors
3. BimodalLogic sets `autoImplicit := false`; cslib uses autoImplicit
4. Custom tactics (`modal_search`, `apply_axiom`, `modal_t`) need evaluation for portability
5. `plausible` dependency used in tests — not needed for library integration

**Content to exclude:**
- Boneyard/ (~27k lines, 29 sorries)
- Tests/ (~11k lines, uses `plausible`)
- Automation/ executables (~19k lines, ML tooling)
- docs/, latex/, typst/ (paper artifacts)

**Open questions:**
1. Does cslib accept sorry in any form? (Likely not)
2. Who holds copyright for Apache 2.0 headers?
3. Should custom automation tactics be ported?
4. Naming: `Bimodal` vs `Temporal` vs `TenseModal`?

### Strategic Horizons (from Teammate D)

**Strong strategic fit.** cslib's CONTRIBUTING.md explicitly lists "Temporal logic" as a wanted contribution under Pillar 1 > Logics. cslib currently has zero temporal logic content.

**Cross-connection opportunities:**
1. **InferenceSystem integration**: BimodalLogic's proof system should instantiate `HasInferenceSystem` typeclass
2. **LTS connection**: Task frames relate to `Cslib.Foundations.Semantics.LTS` — task relations generalize LTS transitions indexed by duration
3. **OmegaSequence.Temporal**: Existing `Cslib.Foundations.Data.OmegaSequence.Temporal` deals with temporal properties of infinite sequences
4. **Modal Cube extension**: The S5 fragment of TM relates to `Cslib.Logics.Modal.Cube.S5`
5. **Process algebra**: CCS temporal behavior could get logical characterization via bimodal logic
6. **Future temporal logics**: Infrastructure enables LTL, CTL, CTL* contributions

**Adaptation level**: Significant — cannot go in as-is. Needs namespace rename, import restructuring, `module`/`@[expose]` adoption, documentation, linting compliance, and Mathlib version migration.

## Synthesis

### Conflicts Resolved

**1. Target namespace/path**: Teammates disagreed:
- A: `Cslib/Logics/Bimodal/` (namespace `Cslib.Logics.Bimodal`)
- B: `Cslib/Logics/Temporal/` (namespace `Cslib.Logic.Temporal`)
- C: `Cslib.Logics.Bimodal` or `Cslib.Logics.TenseModal`
- D: Multiple options including `Cslib.Logics.Modal.Bimodal`

**Resolution**: This should be discussed with cslib maintainers before starting. The strongest candidates are `Cslib.Logics.Temporal` (aligns with CONTRIBUTING.md wording and is broader — enabling future LTL/CTL additions) or `Cslib.Logics.Bimodal` (more precise for this specific logic). Recommend proposing on Zulip before proceeding. Note B's observation that cslib has a path/namespace discrepancy: `Cslib/Logics/Modal/` (path) vs `Cslib.Logic.Modal` (namespace) — follow the established cslib pattern.

**2. PR count**: Teammates suggested 5-10 PRs. All agree on the dependency ordering: Syntax first, then Semantics and ProofSystem in parallel, then downstream. B's 10-PR plan is the most detailed and well-reasoned. Adopt B's plan as the baseline, noting PRs 1-3 are the critical foundation.

**3. Sorry count discrepancy**: C counted 35 active sorries (most reliable — based on file-by-file grep excluding Boneyard). D reported 209 (likely counting all occurrences including Boneyard and comments). Use C's count: 35 active sorries in 11 files.

### Gaps Identified

1. **Porting effort estimation**: No teammate attempted a concrete estimate of the Lean 4.27→4.31 migration work per file. This is the largest unknown — could range from mechanical (30 min/file) to substantial (hours/file if Mathlib APIs changed).
2. **Test of a single file**: Nobody actually tried porting one BimodalLogic file to cslib to validate the approach. A proof-of-concept port of `Syntax/Formula.lean` would derisk the entire plan.
3. **Maintainer communication**: CONTRIBUTING.md says to discuss "new foundational frameworks" on Zulip before starting. This hasn't been done and is a prerequisite.
4. **Custom tactics portability**: BimodalLogic's `modal_search`, `apply_axiom`, and proof search automation haven't been evaluated for compatibility with cslib's linter/style requirements.

### Recommendations

1. **Discuss with cslib maintainers on Zulip** before any implementation — confirm namespace, PR strategy, and whether the scope is welcome
2. **Start with a proof-of-concept port** of PR 1 (Syntax — ~5 files, ~2,500 lines) to validate the toolchain migration and discover porting patterns
3. **Follow B's 10-PR plan** as the implementation roadmap, submitting PRs sequentially (PR 1 first, each subsequent PR depends on earlier ones being merged)
4. **Exclude all sorry-containing files** from initial PRs — PRs 1-10 are all sorry-free
5. **Exclude** Boneyard, Tests, Automation executables, docs/latex/typst
6. **Add copyright headers** (Apache 2.0, author name) to every file
7. **Adapt each file** for cslib conventions: `import Cslib.Init`, `module` declarations, `public import`, `@[expose] public section`, Mathlib-style docstrings, linting compliance
8. **Run `lake shake`** on each PR to minimize imports
9. **Evaluate InferenceSystem integration** during PR 3 (ProofSystem) — the axiom/derivation types may benefit from instantiating `HasInferenceSystem`
10. **Defer custom tactics** to a later PR after core theory is merged

## Teammate Contributions

| Teammate | Angle | Status | Confidence | Key Contribution |
|----------|-------|--------|------------|-----------------|
| A | Primary structure/mapping | completed | high | Detailed module map, 3-tier classification |
| B | Dependencies/PR strategy | completed | high | 9-layer dependency graph, 10-PR plan with titles |
| C | Critic/risks | completed | high | Sorry inventory, style mismatches, open questions |
| D | Strategic horizons | completed | high | Strategic fit analysis, cross-connection opportunities |

## References

- BimodalLogic source: `/home/benjamin/Projects/BimodalLogic/`
- cslib source: `/home/benjamin/Projects/cslib/`
- cslib CONTRIBUTING.md: Lists temporal logic as wanted
- cslib existing Modal: `Cslib/Logics/Modal/` (3 files, ~270 lines)
- Teammate A report: `specs/001_integrate_bimodal_logic_results/reports/01_teammate-a-findings.md`
- Teammate B report: `specs/001_integrate_bimodal_logic_results/reports/01_teammate-b-findings.md`
- Teammate C report: `specs/001_integrate_bimodal_logic_results/reports/01_teammate-c-findings.md`
- Teammate D report: `specs/001_integrate_bimodal_logic_results/reports/01_teammate-d-findings.md`
