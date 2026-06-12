## Summary

Introduces the temporal logic formula type `Temporal.Formula` with primitives
`{atom, bot, imp, untl, snce}`, taking falsum (`⊥`) and implication (`→`) as the
primitive propositional connectives and until (`U`) and since (`S`) as the primitive
temporal modalities. Negation (`neg`), verum (`top`), disjunction (`or`), conjunction
(`and`), biconditional (`iff`), eventually (`someFuture`/`𝐅`), globally (`allFuture`/`𝐆`),
past-eventually (`somePast`/`𝐏`), and historically (`allPast`/`𝐇`) are derived connectives
defined as `abbrev`s, enabling definitional unfolding. This is the gateway PR for all
temporal logic in CSLib.

## Why `{bot, imp, untl, snce}` as the primitives

- **Propositional completeness.** `{imp, bot}` is functionally complete for classical logic
  (same basis as #635), so `neg`/`top`/`or`/`and`/`iff` are all definable as `abbrev`s.
- **Temporal completeness.** Kamp's theorem (1968) shows that `{untl, snce}` are expressively
  complete for first-order definable temporal properties over linear orders. Every other temporal
  operator (`𝐅`, `𝐆`, `𝐏`, `𝐇`, next, prev, release, trigger, weak until/since, strong
  release/trigger, always, sometimes) is derived from these two.
- **A minimal inductive.** Five constructors means fewer cases in every recursion and induction
  — the encoding, complexity, temporal depth, BEq, and atom-collection functions all benefit.
- **Temporal duality for free.** The `swapTemporal` involution simply exchanges `untl ↔ snce`,
  giving the temporal duality rule ("if ⊢ φ then ⊢ swapTemporal φ") with a clean structural
  recursion and a short involution proof.

## Argument convention: Burgess order

The derived operators use the Burgess convention: in `untl event guard` and `snce event guard`,
the first argument is the **event** (holds at the witness point) and the second is the **guard**
(holds at all intermediate points). So `someFuture φ = untl φ top` (event φ, trivial guard),
not the standard LTL notation `⊤ U φ`. This convention matches the abstract typeclass expansion
in `Axioms.lean` and the downstream proof-system files (`ProofSystem.lean`, `Instances.lean`)
that pattern-match on these `abbrev`s.

## Dependency: stacked on #635

This PR is **stacked on #635** ("refactor: Proposition type to bot/imp primitives"), which
introduces `Cslib/Foundations/Logic/Connectives.lean` and the typeclass hierarchy
(`HasBot`, `HasImp`, `HasUntil`, `HasSince`, `TemporalConnectives`, …). This PR registers
`Temporal.Formula` as a `TemporalConnectives` instance, deferring to #635 for the connective
design.

Please review/merge #635 first. Until #635 lands, this PR's branch carries #635's commits, so
the diff below shows those foundation files as well; once #635 is merged the diff reduces to
the two files listed under "File-by-file".

## What the file provides

### Core formula type (lines 1–119)
- `Formula` inductive with `{atom, bot, imp, untl, snce}`, deriving `DecidableEq` and `BEq`.
- Derived propositional connectives: `neg`, `top`, `or`, `and`, `iff` (Łukasiewicz encoding).
- Derived temporal operators: `someFuture`, `allFuture`, `somePast`, `allPast`.
- Scoped notation: `¬ ∧ ∨ → ↔ U S 𝐅 𝐆 𝐏 𝐇`.
- `TemporalConnectives`, `Bot`, `Top` instances.

### Countability (lines 138–234)
- `encodeNat`: Cantor-pairing encoding of formulas into `ℕ`.
- `encodeNat_injective`: the encoding is injective (explicit induction, no `decide` oracle).
- `Countable`, `Infinite`, `Denumerable` instances.

### BEq laws (lines 236–310)
- `ReflBEq` and `LawfulBEq` instances for `Formula`.

### Structural measures (lines 312–383)
- `complexity`: pattern-aware structural complexity that recognises derived operators
  (F, G, P, H, next, prev, release, trigger) and assigns them overhead 1.
- `temporalDepth`: maximum nesting depth of `untl`/`snce`.
- `countImplications`: implication count for proof-search heuristics.

### Additional derived operators (lines 385–449)
- `next`/`prev` (X/Y), `weakFuture`/`weakPast` (G'/H'), `always`/`sometimes` (△/▽),
  `release`/`trigger` (R/T), `weakUntil`/`weakSince` (W/WS),
  `strongRelease`/`strongTrigger` (M/ST).

### Swap temporal duality (lines 451–525)
- `swapTemporal`: exchanges `untl ↔ snce` recursively.
- `swapTemporal_involution`: applying twice gives identity.
- Exchange theorems for all derived operators (someFuture↔somePast, allFuture↔allPast,
  next↔prev, strongRelease↔strongTrigger).
- `swapTemporal_neg`: distributes over negation.

### Predicates and atom collection (lines 527–582)
- `needsPositiveHypotheses`: classifies formulas for proof-system propagation.
- `atoms`: collects propositional atoms as a `Finset`.
- `atoms_swapTemporal`: swapping preserves the atom set.

## File-by-file change summary

### Cslib.lean
- Adds `public import Cslib.Logics.Temporal.Syntax.Formula` (alphabetical position).

### Cslib/Logics/Temporal/Syntax/Formula.lean (new, 582 lines)
- Full temporal formula type with primitives, derived connectives, countability/BEq instances,
  structural measures, derived operators, swap-temporal duality, and atom collection.
  See "What the file provides" above for section breakdown.

## AI Disclosure

This PR was prepared with the assistance of Claude Code (Anthropic), used for extracting
files from a development branch, running CI verification commands, and drafting this description.
All Lean code was written by the author (Benjamin Brast-McKie) and verified to compile on the
PR branch.
