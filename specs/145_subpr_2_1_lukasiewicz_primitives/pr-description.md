# PR: refactor(Modal): Lukasiewicz primitive convention for modal propositions

**Title**: `refactor(Modal): Lukasiewicz primitive convention for modal propositions`

**Base branch**: `leanprover/cslib:main`
**Head branch**: `benbrastmckie/cslib:refactor/modal-lukasiewicz`

## Summary

Refactors the modal `Proposition` inductive type to follow the Lukasiewicz convention: `bot` (falsum), `imp` (implication), and `box` (necessity) are the primitive constructors alongside `atom`, while negation (`neg`), conjunction (`and`), disjunction (`or`), verum (`top`), possibility (`diamond`), and biconditional (`iff`) are derived connectives defined as `abbrev`s. This replaces the previous `not`/`and`/`diamond` primitives.

Key changes:
- `Proposition` constructors changed from `{atom, not, and, diamond}` to `{atom, bot, imp, box}`
- Derived connectives defined as `abbrev`s (not `def`s), enabling definitional unfolding
- All `grind`-based validity proofs replaced with explicit term-mode proofs
- `Denotation.lean` updated for the new primitives with explicit proofs
- `LogicalEquivalence.lean` rewritten with `Context` constructors matching the new primitives (`hole`, `impL`, `impR`, `box`)

## Context

This is Sub-PR 2.1 extracted from the larger PR #633. It isolates the modal `Proposition` type refactoring as a self-contained, independently reviewable change that establishes the Lukasiewicz convention for all subsequent modal logic PRs.

**Zulip topic**: [https://leanprover.zulipchat.com/#narrow/channel/513188-CSLib/topic/Modal.20Logic/with/602381445]

**Literature reference**: Blackburn, P., de Rijke, M., & Venema, Y. (2001). *Modal Logic*. Cambridge Tracts in Theoretical Computer Science, vol. 53. Cambridge University Press. The convention of taking falsum, implication, and box as primitive modal connectives — with negation, conjunction, disjunction, and diamond derived — is standard in algebraic and frame-theoretic treatments of modal logic. See also Chagrov, A. & Zakharyaschev, M. (1997). *Modal Logic*. Oxford Logic Guides, vol. 35. Oxford University Press.

## File-by-file change summary

```
 Cslib/Logics/Modal/Basic.lean              | 315 ++++++++++++++++++++---------
 Cslib/Logics/Modal/Denotation.lean         |  52 ++++-
 Cslib/Logics/Modal/LogicalEquivalence.lean | 176 ++++++----------
 CslibTests/GrindLint.lean                  |   3 +
 4 files changed, 329 insertions(+), 217 deletions(-)
```

### Cslib/Logics/Modal/Basic.lean (+219, -96)

- Replaces `not`/`and`/`diamond` constructors with `bot`/`imp`/`box` primitives
- Adds derived connectives as `abbrev`s: `neg`, `top`, `or`, `and`, `diamond`, `iff`
- Adds `deriving DecidableEq, BEq` to `Proposition`
- Rewrites `Satisfies` to match on `{atom, bot, imp, box}` directly
- Adds explicit satisfaction theorems for derived connectives (`neg_iff`, `diamond_iff`, `and_iff`, `or_iff`)
- Replaces all 20+ `grind`-based axiom validity proofs (K, dual, T, B, 4, 5, D and their reflexive/symmetric/transitive/euclidean/serial converses) with explicit term-mode proofs
- Replaces 3 theory-level `grind` proofs (`TheoryEq.ext_iff`, `satisfies_theory`, `not_theoryEq_satisfies`) with explicit proofs using `Set.ext_iff`, direct hypothesis application, and `rw`/`push_neg`/`rcases`
- Updates `Proposition.complexity`, `Proposition.atoms`, `Proposition.subst` for new constructors

### Cslib/Logics/Modal/Denotation.lean (+43, -9)

- Updates `denotation` function to match on `{atom, bot, imp, box}` instead of `{atom, not, and, diamond}`
- Replaces 3 `grind`-based proofs with explicit case-by-case proofs:
  - `satisfies_mem_denotation`: explicit `simp only`/`constructor`/`rcases` by case
  - `neg_denotation` (renamed from `not_denotation`): explicit `simp only`/`push_neg`/case split
  - `theoryEq_denotation_eq`: explicit constructor with `satisfies_mem_denotation`

### Cslib/Logics/Modal/LogicalEquivalence.lean (+64, -112)

- Complete rewrite from 132 lines to 84 lines
- `Proposition.Context` constructors changed from `{hole, not, andL, andR, diamond}` to `{hole, impL, impR, box}` matching new primitives
- Defines `LogicallyEquivalent` directly (not via typeclass instantiation)
- Proves `congruence` theorem for the new context structure
- Removes dependency on `Cslib.Foundations.Logic.LogicalEquivalence` typeclass
- All proofs explicit (no `grind`)

### CslibTests/GrindLint.lean (+3)

- Adds `#grind_lint skip` entries for 3 Modal theorems with high grind instantiation chains:
  - `Cslib.Logic.Modal.neg_denotation` (24 instantiations)
  - `Cslib.Logic.Modal.Satisfies.and_iff_and` (30 instantiations)
  - `Cslib.Logic.Modal.Satisfies.or_iff_or` (24 instantiations)

## AI Disclosure

This PR was prepared with the assistance of Claude Code (Anthropic). The AI tool was used for:
- Drafting and extracting files from a development branch to create a clean PR branch
- Running CI verification commands
- Drafting this PR description

All Lean code was written by the authors (Thomas Waring, Benjamin Brast-McKie) and verified to compile cleanly on the PR branch.
