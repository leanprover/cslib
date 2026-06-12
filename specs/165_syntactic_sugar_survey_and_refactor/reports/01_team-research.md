# Research Report: Task #165

**Task**: Syntactic sugar survey and refactor (Foundations/, Propositional/, Modal/, Tense/)
**Date**: 2026-06-12
**Mode**: Team Research (4 teammates)
**Session**: sess_1749745000_a3b2c1

## Summary

PR #633 reviewer feedback (comment r3403944952 on `Propositional/Metalogic/Completeness.lean:45`)
established the convention: **use scoped notation (`→ ∧ ∨ ¬ ⊥ □ ◇ U S …`) instead of raw
constructors (`.imp`, `.bot`, `.neg`, …) at all usage sites**. The survey found roughly
**2,600 replaceable expression-position occurrences** in the directly-scoped directories
(Propositional ~320, Modal ~435, Temporal ~1,845), plus ~10,400 in Bimodal if that
directory is included in scope. The Foundations/Logic layer (~730-840 occurrences of
`HasImp.imp`/`HasBot.bot`) should **NOT** be refactored — it is a deliberately explicit
polymorphic typeclass layer with no notation.

**Scope note**: The task description names "Tense/" — no such directory exists. The
temporal-logic code lives in `Cslib/Logics/Temporal/` (and `Cslib/Logics/Bimodal/` for
the bimodal temporal system). This report treats Temporal/ as the intended "Tense/" scope
and includes Bimodal findings for completeness.

## Key Findings

### Primary Approach (from Teammate A — Propositional + Foundations)

- **Propositional/**: ~320 replaceable occurrences across 16 files. Densest:
  `Metalogic/Completeness.lean` (~60), `NaturalDeduction/HilbertDerivedRules.lean` (~40),
  `Metalogic/IntLindenbaum.lean` (~40), `Metalogic/MinLindenbaum.lean` (~35).
  All files open `Cslib.Logic.PL`, so notation is always in scope. Full line-by-line
  catalog in `01_teammate-a-findings.md`.
- **Replacement patterns** (PL): `φ.imp ψ` → `φ → ψ` (~200), `Proposition.bot`/`.bot` → `⊥`
  (~50), `Proposition.neg φ` → `¬φ` (~30), `.and`/`.or` → `∧`/`∨` (~25),
  `Proposition.bot.imp φ` → `⊥ → φ` (EFQ pattern, ~20).
- **Foundations/Logic/**: ~660-840 usages of `HasImp.imp`/`HasBot.bot`/`HasBox.box` are
  typeclass method calls on an abstract `F : Type*` — no notation exists.

### Alternative Approaches (from Teammate B — Modal)

- **Modal/**: ~435 replaceable lines across 56 files. The **15 ProofSystem/Instances
  files** are the densest, highest-value targets: every axiom schema is spelled out as
  e.g. `KAxiom (Proposition.imp (Proposition.box (Proposition.imp φ ψ)) (Proposition.imp
  (Proposition.box φ) (Proposition.box ψ)))` which becomes `KAxiom (□(φ → ψ) → □φ → □ψ)`.
- The D axiom currently encoded as `□φ → ((□(φ → ⊥)) → ⊥)` becomes the readable `□φ → ¬□¬φ`.
- **Metalogic/** (Completeness, MCS, DeductionTheorem, DerivationTree): ~250 lines in
  signatures and proof bodies.
- **One scoping exception**: `FromPropositional.lean` lives in `namespace Cslib.Logic`
  where PL and Modal notation could conflict — leave fully qualified.
- `change` tactic targets CAN use notation (definitional transparency); `unfold X` and
  `simp only [X]` arguments CANNOT (they name definitions, not notation).

### Gaps and Shortcomings (from Critic — Teammate C)

- **Temporal/**: ~1,845 expression-position occurrences across 31 files; the single file
  `Chronicle/PointInsertion.lean` accounts for 664. Heavy hitters also include
  `Chronicle/CounterexampleElimination.lean` (173), `Chronicle/RRelation.lean` (139),
  `Metalogic/MCS.lean` (123).
- **Unsafe categories confirmed** (must NOT replace):
  1. Pattern-match arms (~525 lines across all Logics/) — Lean syntax requirement
  2. `congrArg₂ Formula.imp` — needs the function name (~9+ sites)
  3. `simp only [Formula.neg, …]` / `unfold Proposition.diamond` — definition names in
     tactic arguments (7 unfold sites, ~30 simp-only sites)
  4. Typeclass field assignments (`instance : … where imp := .imp`)
  5. The `abbrev` definition sites of the derived connectives themselves
  6. **Three files that explicitly do not open their namespace** to avoid single-letter
     notation conflicts (`F G P H S U`): `Temporal/ProofSystem/Instances.lean`,
     `Bimodal/ProofSystem/Instances.lean`, `Bimodal/Theorems/Perpetuity/Helpers.lean`
- **Deep structural matches** in Temporal's `complexity`/`encodeNat` (e.g.
  `| .imp (.untl (.imp φ .bot) (.imp .bot .bot)) .bot =>`) match definitional expansions
  and must stay raw.
- **Safety guarantees**: all derived connectives are `abbrev`s, so notation elaborates to
  identical terms — replacements are definitionally invisible to the kernel. `→`
  ambiguity with the function arrow is resolved by type inference (low risk).
- Recursive function bodies (right of `=>` in match arms) are safe to replace but
  visual alignment with the raw-constructor pattern may be preferred — style judgment.

### Strategic Horizons (from Teammate D)

- **Missing notation found**:
  1. **PL lacks `↔`**: `Proposition.iff` exists (Defs.lean:77) but has no scoped infix.
     Modal and Temporal both have it. Fix: add
     `@[inherit_doc] scoped infix:30 " ↔ " => Proposition.iff` to PL Defs.lean.
  2. **Bimodal may lack `Bot`/`Top` instances** — verify and add if missing.
  3. Precedence inconsistency: `△`/`▽` is 80 in Temporal but 40 in Bimodal (minor; no action required).
- **Foundations/Logic should NOT get notation** (consensus with Critic): the explicit
  typeclass calls are the point of that layer; generic `→` would clash with the function
  arrow; `[Bot F]` constraints would propagate everywhere.
- **PR coordination**: three open PRs affect scope —
  - **PR #633** (Foundations/Logic + Propositional, the PR with the reviewer comment):
    apply PL sugar fixes there first.
  - **PR #635** (Proposition Lukasiewicz refactor) and **PR #637** (Modal primitives
    refactor): actively rewriting Modal primitives — Modal sugar work must wait for or
    coordinate with these.
- **Upstream style**: upstream cslib main uses notation inside derived-connective
  definitions; the implicit convention from the reviewer is "use notation wherever
  available and unambiguous." No formal style guide exists.

## Synthesis

### Conflicts Resolved

1. **Foundations/Logic notation** — Teammate A floated adding new notation (e.g. `⟶`,
   `⊥ₗ`) for the ~660+ `HasImp.imp` usages as a "Phase 2 design decision"; Teammates C
   and D both argued the polymorphic layer should stay explicit. **Resolution: keep
   Foundations/Logic as-is** (C+D position) — it is out of scope for this refactor. If
   readability of `Combinators.lean`/`S5.lean` becomes a real pain point, propose
   notation upstream as a separate RFC-style PR.
2. **Scope of "Tense/"** — interpreted as `Temporal/`. Bimodal/ (~10,400 occurrences) is
   surveyed but flagged as a scope decision for the user: it is by far the largest and
   riskiest directory and was not literally named in the task.
3. **Recursive function bodies** — B flagged them replaceable, C flagged the style
   tension. **Resolution: replace only when it improves readability; keep raw
   constructors where the body mirrors the match pattern** (case-by-case during
   implementation).

### Gaps Identified

- Exact per-line catalogs exist for Propositional and Modal; Temporal counts are
  file-level estimates (line-level cataloging deferred to implementation).
- The interaction of notation with goals displayed after `unfold` needs per-site testing
  (7 sites).
- PR #635/#637 churn means Modal line numbers in the catalog will shift; re-verify at
  implementation time.

### Recommendations

1. **Phase the work into separate PRs by logic level** (dependency/risk order):
   1. **PL** (~320 replacements + add `↔` notation) — directly answers the PR #633
      review comment; apply to that PR's branch.
   2. **Temporal** (~1,845) — independent of Modal churn; can proceed in parallel.
   3. **Modal** (~435) — after PRs #635/#637 land.
   4. **Bimodal** (~10,400 + `Bot`/`Top` instances) — only if user confirms scope;
      consider splitting by subdirectory.
2. **Within each PR**: add missing notation/instances first, then refactor Defs/Basic →
   ProofSystem → Metalogic → Semantics → NaturalDeduction.
3. **Mechanical safety net**: after each file, `lake build <Module>`; full CI
   (`lake build`, `lake lint`, `lake exe lint-style`, `lake test`, `lake shake`) per PR.
   All replacements are definitionally invisible, so failures should be rare and local
   (mostly precedence/parenthesization issues).
4. **Never touch**: pattern-match arms, tactic arguments naming definitions
   (`unfold`/`simp only`/`congrArg₂`), typeclass field assignments, abbrev definition
   sites, the three namespace-conflict files, and all of Foundations/Logic.

## Teammate Contributions

| Teammate | Angle | Status | Confidence |
|----------|-------|--------|------------|
| A | Propositional + Foundations survey | completed | high |
| B | Modal survey | completed | high |
| C | Critic: Temporal survey + risk analysis | completed | high |
| D | Horizons: missing notation, strategy, Bimodal | completed | high/medium |

## References

- PR #633 review comment r3403944952 (the triggering feedback)
- `Cslib/Logics/Propositional/Defs.lean` (PL notation, lines 83-86)
- `Cslib/Logics/Modal/Basic.lean` (Modal notation, lines 81-87)
- `Cslib/Logics/Temporal/Syntax/Formula.lean` (Temporal notation, lines 97-107, 446-449)
- `Cslib/Logics/Bimodal/Syntax/Formula.lean` (Bimodal notation, lines 81-103)
- `Cslib/Foundations/Logic/Connectives.lean` (typeclass hierarchy)
- Teammate findings: `01_teammate-{a,b,c,d}-findings.md` (same directory)
- Open PRs: #633 (PL/Foundations), #635 (Lukasiewicz refactor), #637 (Modal primitives)
