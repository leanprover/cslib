# feat(Logics/Temporal): temporal logic formula type with primitives and derived operators

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

## File-by-file change summary

### Cslib.lean
- Adds `public import Cslib.Logics.Temporal.Syntax.Formula` (alphabetical position).

### Cslib/Logics/Temporal/Syntax/Formula.lean (new, 582 lines)

**Inductive and derived connectives.** The `Formula` inductive has five constructors (`atom`,
`bot`, `imp`, `untl`, `snce`), deriving `DecidableEq` and `BEq`. All other connectives are
`abbrev`s that unfold by `rfl`:

| Connective | Definition | Notation |
|------------|------------|----------|
| `neg φ` | `imp φ bot` | `¬` |
| `top` | `imp bot bot` | (via `Top` instance) |
| `or φ ψ` | `imp (neg φ) ψ` | `∨` |
| `and φ ψ` | `neg (imp φ (neg ψ))` | `∧` |
| `iff φ ψ` | `(imp φ ψ).and (imp ψ φ)` | `↔` |
| `someFuture φ` | `untl φ top` | `𝐅` |
| `allFuture φ` | `neg (someFuture (neg φ))` | `𝐆` |
| `somePast φ` | `snce φ top` | `𝐏` |
| `allPast φ` | `neg (somePast (neg φ))` | `𝐇` |

Registers `TemporalConnectives`, `Bot`, and `Top` instances.

**Countability.** `Countable`, `Infinite`, and `Denumerable` instances for `Formula Atom`,
established via a Cantor-pairing encoding (`encodeNat`) with an explicit injectivity proof
(`encodeNat_injective`).

**BEq laws.** `ReflBEq` and `LawfulBEq` instances, proved by structural induction on the
five constructors.

**Structural measures.** Three recursive functions for proof-search and complexity analysis:
- `complexity`: connective count, pattern-aware for derived operators (e.g. `𝐅 φ` counts as
  1 rather than 4).
- `temporalDepth`: maximum nesting of `untl`/`snce`.
- `countImplications`: heuristic for proof search.

**Extended derived operators.** The full temporal operator vocabulary beyond the four core
derived operators: `next`/`prev` (X/Y), `release`/`trigger` (R/T, duals of until/since),
`weakUntil`/`weakSince` (W/WS), `strongRelease`/`strongTrigger` (M/ST),
`weakFuture`/`weakPast` (G'/H'), `always`/`sometimes` (△/▽).

**Swap temporal duality.** `swapTemporal` exchanges `untl ↔ snce` recursively, giving the
temporal duality rule. Key results:
- `swapTemporal_involution`: applying twice gives identity.
- Exchange theorems: `someFuture ↔ somePast`, `allFuture ↔ allPast`, `next ↔ prev`,
  `strongRelease ↔ strongTrigger`.
- `atoms_swapTemporal`: swapping preserves the atom set.

**Proof-system support.** `needsPositiveHypotheses` classifies formulas for propagation rules,
and `atoms` collects propositional atoms as a `Finset`.

## AI Disclosure

This PR was prepared with the assistance of Claude Code (Anthropic), used for extracting
files from a development branch, running CI verification commands, and drafting this description.
All Lean code was written by the author (Benjamin Brast-McKie) and verified to compile on the
PR branch.
