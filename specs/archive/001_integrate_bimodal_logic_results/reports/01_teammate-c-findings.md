# Teammate C (Critic) Findings: BimodalLogic → cslib Integration

**Date**: 2026-06-08
**Confidence Level**: High

## Key Findings

The integration faces five major categories of risk: toolchain version gap, sorry-laden metalogic modules, fundamental architectural mismatches between the two codebases, massive scale of the source material, and a significant amount of content that doesn't belong in a community library.

## Proof Completeness

**64 total sorry instances** across the codebase:
- **29 sorries** in `Boneyard/` (dead/archived code — exclude entirely)
- **35 sorries** in active `Metalogic/` modules

**Files with active sorries (outside Boneyard)**:
| File | Sorry Count | Notes |
|------|-------------|-------|
| `Metalogic/Bundle/SuccRelation.lean` | 7 | Successor relation properties |
| `Metalogic/BXCanonical/Chronicle/ChronicleToCountermodel.lean` | 6 | Countermodel construction |
| `Metalogic/WeakCanonical/TruthLemma.lean` | 6 | Truth lemma cases (documented non-critical) |
| `Metalogic/WeakCanonical/EFGames/StaviCompleteness.lean` | 3 | Stavi completeness |
| `Metalogic/Bundle/SuccExistence.lean` | 3 | Successor existence proofs |
| `Metalogic/BXCanonical/Frame.lean` | 1 | Frame reflexivity |
| `Metalogic/WeakCanonical/ChronicleExtraction.lean` | 1 | Chronicle extraction |
| `Metalogic/WeakCanonical/Transfer.lean` | 1 | Transfer theorem |
| `Metalogic/WeakCanonical/OrderedSum.lean` | 1 | Ordered sum construction |
| `Metalogic/WeakCanonical/Expressiveness/CaseAnalysis.lean` | 1 | Case analysis |
| `Metalogic/Bundle/UntilSinceCoherence.lean` | unknown | Until/Since coherence |

**Impact**: The sorry-free modules (Syntax, Semantics, ProofSystem, Theorems, Soundness, Decidability, FMP, Separation, Conservative Extension, most of Algebraic) form a substantial sorry-free core. However, many of the most interesting metalogic results (completeness chain, truth lemma, EF games) have sorry dependencies. cslib likely won't accept files containing sorry — these would need to be either excluded or completed first.

**sorryAx traces**: The `Completeness.lean` file documents that `sorryAx` traces through `succ_embed_surjective → limitDomSubtype_isSuccArchimedean → succ_cofinal → chronicle_gap_contradiction`. This is a known unresolved chain.

## Version Compatibility Risks

**CRITICAL: Major toolchain version gap**
- **BimodalLogic**: `leanprover/lean4:v4.27.0-rc1`
- **cslib**: `leanprover/lean4:v4.31.0-rc1`

This is a 4-version gap spanning significant Lean 4 changes. Key concerns:

1. **`module` keyword**: cslib uses the new `module` declaration (Lean 4.31 feature). BimodalLogic does not. All files would need `module` added.

2. **`public import` vs `import`**: cslib uses `public import` throughout. BimodalLogic uses bare `import`. Every import statement needs conversion.

3. **`@[expose] public section`**: cslib uses this pattern extensively. BimodalLogic does not use it at all. This affects namespace visibility.

4. **Mathlib version**: BimodalLogic pins `mathlib @ v4.27.0-rc1`. cslib pins mathlib by commit hash (`eb15debe...`). These are different Mathlib versions with potentially breaking API changes across 4 versions.

5. **`plausible` dependency**: BimodalLogic depends on the `plausible` library (used only in tests). cslib does not have this dependency and shouldn't need it — tests wouldn't be ported.

6. **lakefile format**: cslib uses `lakefile.toml`, BimodalLogic uses `lakefile.lean`. The library target configuration is incompatible.

## Style/Convention Mismatches

### Namespace Conventions
- **cslib**: `Cslib.Logic.Modal` (fully qualified, prefixed with `Cslib`)
- **BimodalLogic**: `Bimodal.Syntax`, `Bimodal.Semantics` (no library prefix)

All namespaces would need renaming: `Bimodal.Syntax.Formula` → `Cslib.Logics.Bimodal.Syntax.Formula` or similar.

### Copyright Headers
- **cslib**: Standard Mathlib-style copyright headers with named authors and Apache 2.0 license
- **BimodalLogic**: No copyright headers on source files

Every file needs a copyright header added.

### Module Documentation
- **cslib**: Uses `/-! # Title ... -/` module docstrings consistently
- **BimodalLogic**: Uses `/-! ... -/` docstrings but in a different style — more detailed, with implementation notes, naming conventions, etc.

### Linting
- **cslib**: Has `weak.linter.mathlibStandardSet = true` and `weak.linter.flexible = true` — enforces Mathlib style linting
- **BimodalLogic**: No linter configuration. Code may not pass Mathlib linters.

### Type Naming
- **cslib**: `Proposition`, `Model` (generic modal logic types)
- **BimodalLogic**: `Formula`, `TaskFrame`, `TaskModel` (domain-specific types)

No direct conflicts (different namespaces), but the overlapping concepts (both define modal formulas) could confuse users. The relationship between `Cslib.Logic.Modal.Proposition` and the BimodalLogic `Formula` type should be clearly documented or bridged.

### Proof Style
- **cslib**: Uses `autoImplicit` (default), standard Mathlib tactics
- **BimodalLogic**: Explicitly sets `autoImplicit := false`, uses custom tactics (`modal_search`, `apply_axiom`, `modal_t`), custom proof search automation

## Content That May Not Belong in cslib

### Definite Excludes
1. **`Boneyard/`** — 27,310 lines of archived dead code with 29 sorries. Explicitly excluded from default build already.
2. **`Tests/`** — 10,914 lines. Uses `plausible` dependency. Test code for a standalone project, not library tests.
3. **`Automation/` executables** — Dataset generators, benchmark tools, proof extractors, REPL bridges. These are project-specific tools (ML training data generation, benchmark anchors). ~18,909 lines total. The automation *tactics* (`ProofSearch/`, `Tactics/`) might belong, but the executable infrastructure does not.
4. **`docs/`**, **`latex/`**, **`typst/`** — Documentation and paper artifacts. Not code.
5. **`Boneyard/DeadConvergenceProof/`** at repo root — Additional dead code.

### Questionable
1. **`Examples/`** — `BimodalProofs.lean`, `TemporalStructures.lean`. Sorry-free but demo-oriented. Could become test files or examples.
2. **`Metalogic/WeakCanonical/EFGames/`** — Ehrenfeucht-Fraïssé game formalization. Interesting but `StaviCompleteness.lean` has 3 sorries.
3. **`Metalogic/Relational/`** — Need to check scope.
4. **Automation tactics** — `AesopRules.lean`, `EFGameTactics.lean`, custom proof search. These are useful but highly domain-specific and may not generalize.

### Approximate Integration Scope
- **Core sorry-free theory**: ~70 files, ~50,000 lines (Syntax, Semantics, ProofSystem, Theorems, FrameConditions, Soundness, Core Metalogic, ConservativeExtension, Algebraic, Decidability, FMP, Separation)
- **Sorry-containing metalogic**: ~11 files, ~15,000 lines
- **Automation (tactics only)**: ~5 files, ~3,000 lines
- **Total estimated for integration**: ~85 files, ~65,000-70,000 lines

This is an enormous amount of code for a single PR. It would need to be broken into multiple focused PRs.

## Questions That Need Answering

1. **Does cslib accept sorry?** If not, all 11 files with active sorries must either be completed or excluded. This significantly affects the completeness story.

2. **What's the PR strategy?** A single PR with ~70,000 lines will not be reviewed. Need a clear decomposition into independently reviewable, self-contained PRs. Suggested order:
   - PR 1: Syntax (Formula, Atom, Context, Subformulas, BigConj)
   - PR 2: Semantics (TaskFrame, TaskModel, Truth, Validity, WorldHistory)
   - PR 3: ProofSystem (Axioms, Derivation, Derivable, Substitution)
   - PR 4: Theorems (Propositional, ModalS4, ModalS5, Perpetuity, etc.)
   - PR 5+: Metalogic modules (each major subsystem as a separate PR)

3. **Who is the copyright holder?** BimodalLogic has no copyright headers. The user needs to determine authorship for the Apache 2.0 headers required by cslib.

4. **How does BimodalLogic's `Formula` relate to cslib's `Proposition`?** Should there be a conversion/embedding? Or are they independent formulations?

5. **Should BimodalLogic's custom automation be ported?** The `modal_search` tactic and proof search infrastructure are useful but add maintenance burden.

6. **Is the `Metalogic/Algebraic/InteriorOperators.lean` sorry (`temp_k_dist derivable from BX`) fixable?** It's in an otherwise sorry-free module.

7. **Naming: `Bimodal` or `TenseModal` or `BimodalTM`?** The cslib namespace needs to be decided. `Cslib.Logics.Bimodal` seems natural, but `Cslib.Logics.TenseModal` might be more descriptive for the community.

8. **Will the Lean 4.27 → 4.31 port introduce breakage?** Four versions of Lean changes plus corresponding Mathlib changes is a significant migration. API renames, tactic changes, and syntax differences should be expected. This could be a substantial amount of work unto itself.

## Confidence Level

**High** — The findings are based on direct source code analysis of both repositories. The toolchain version gap and sorry counts are factual. The style mismatches are observable. The main uncertainty is around how much breakage the v4.27→v4.31 port will actually cause (could be minor or extensive depending on which Mathlib APIs are used).
