# PR: refactor: Proposition type to Lukasiewicz convention

**Title**: `refactor: Proposition type to Lukasiewicz convention`

**Base branch**: `leanprover/cslib:main`
**Head branch**: `benbrastmckie/cslib:refactor/proposition-lukasiewicz`

## Summary

Refactors the `Proposition` inductive type to follow the Lukasiewicz convention: `bot` (falsum) and `imp` (implication) are the primitive constructors, while conjunction (`and`), disjunction (`or`), negation (`neg`), and verum (`top`) are derived connectives. This replaces the previous `and`/`or`/`impl` primitives.

Key changes:
- Introduces `Connectives.lean` with typeclasses (`HasNeg`, `HasConj`, `HasDisj`, `HasTop`, `HasBiimpl`) providing a general interface for derived connectives
- Simplifies `NaturalDeduction/Basic.lean` from 10 inference rules to 5, as the derived connective rules are no longer primitive
- Adds the `ChagrovZakharyaschev1997` reference (Chagrov & Zakharyaschev, *Modal Logic*, Oxford Logic Guides vol. 35, 1997)

## Context

This is Sub-PR 1.1.1 extracted from the larger PR #633. It isolates the foundational `Proposition` type refactoring as a self-contained, independently reviewable change.

**Zulip topic**: [https://leanprover.zulipchat.com/#narrow/channel/513188-CSLib/topic/Propositional.20Logic/with/602336739]

**Literature reference**: Chagrov, A. & Zakharyaschev, M. (1997). *Modal Logic*. Oxford Logic Guides, vol. 35. Oxford University Press. Chapter 1 follows the classical convention, originating with Church (1956) and the Tarski-Bernays-Wajsberg system, of taking falsum and implication as primitive connectives with other connectives derived.

## File-by-file change summary

```
 Cslib.lean                                         |  1 +
 Cslib/Foundations/Logic/Connectives.lean           | 98 ++++++++++++++++++++++
 Cslib/Foundations/Logic/InferenceSystem.lean       |  4 +-
 Cslib/Logics/Propositional/Defs.lean               | 80 ++++++++++--------
 .../Propositional/NaturalDeduction/Basic.lean      | 98 +++++++---------------
 references.bib                                     | 11 +++
 6 files changed, 188 insertions(+), 104 deletions(-)
```

### Cslib.lean (+1)
- Adds `public import Cslib.Foundations.Logic.Connectives` in alphabetical position

### Cslib/Foundations/Logic/Connectives.lean (+98, NEW)
- New file defining typeclasses for derived logical connectives
- `HasNeg`: negation typeclass (neg := imp a bot)
- `HasConj`: conjunction typeclass
- `HasDisj`: disjunction typeclass
- `HasTop`: verum typeclass (top := neg bot)
- `HasBiimpl`: biconditional typeclass
- Provides `Notation` instances for standard logical symbols

### Cslib/Foundations/Logic/InferenceSystem.lean (+2, -2)
- Changes `public import Cslib.Init` to `import Cslib.Init` (visibility adjustment)
- Adds docstring `/-! # Inference System Typeclass -/` replacing empty `/-! -/`

### Cslib/Logics/Propositional/Defs.lean (+44, -36)
- Replaces `and`/`or`/`impl` constructors with `bot`/`imp` primitives
- Adds `public import Cslib.Foundations.Logic.Connectives`
- Derives connectives (`neg`, `and`, `or`, `top`, `biimpl`) via Connectives typeclasses
- Updates `Proposition.complexity` and `Proposition.atoms` for new structure
- Updates `Proposition.subst` for the new constructors
- Adds `instance : HasBot`, `HasImp`, `HasNeg`, `HasConj`, `HasDisj`, `HasTop`, `HasBiimpl`

### Cslib/Logics/Propositional/NaturalDeduction/Basic.lean (-55, +43)
- Simplifies inference rules from 10 to 5 (modus ponens, explosion, deduction theorem, conjunction intro/elim, necessitation)
- Removes primitive rules for disjunction and adds them as derivable
- Updates proof structure to use `bot`/`imp` representation

### references.bib (+11)
- Adds `ChagrovZakharyaschev1997` BibTeX entry

## AI Disclosure

This PR was prepared with the assistance of Claude Code (Anthropic). The AI tool was used for:
- Extracting files from a development branch to create a clean PR branch
- Running CI verification commands
- Drafting this PR description

All Lean code was written by the authors (Thomas Waring, Benjamin Brast-McKie) and verified to compile cleanly on the PR branch.
