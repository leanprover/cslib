# Teammate C Findings (Round 2): Critical Analysis — All Three Levels

**Task**: 112 — Establish soundness and completeness for propositional Hilbert proof systems
**Role**: Teammate C (Critic) — gaps, risks, blind spots, challenged assumptions
**Round**: 2 (building on round-1 findings; previous reports: 01_teammate-a/b/c/d-findings.md)
**Date**: 2026-06-11

---

## Overview

The round-1 reports correctly identified the scope (three levels: classical, intuitionistic,
minimal) and proposed strategies for each. This round-2 critic report challenges the assumptions
and identifies where the proposed strategies may fail or underestimate complexity. I examine
seven specific risks in detail, grounded in the actual code and literature.

---

## Risk 1: CZ Chapter 1's Proof Strategy Is NOT the Henkin/MCS Strategy

**Claimed in round-1**: CZ Chapter 1 uses Henkin/MCS-style canonical construction that matches
the existing codebase's `KCompleteness.lean` pattern.

**What CZ actually says** (Theorem 1.16, pp. 14–15): CZ proves classical completeness via the
**semantic tableau / Hintikka systems method**, NOT via Henkin/MCS. The proof:

1. Starts from the tableau `(∅, {φ})` (the "false tableau" for φ)
2. Extends it step-by-step by placing each subformula on left (T) or right (F) side, testing
   consistency at each step
3. Constructs a finite saturated disjoint tableau `tn`
4. By Proposition 1.7, a realizable countermodel exists from the saturated tableau

This is a **finite subformula closure procedure**, not Lindenbaum-Zorn. The "model" extracted is
defined directly from the saturated tableau: `M = Tn ∩ Var(φ)`.

The Henkin/MCS approach appears in CZ's **Chapter 5** (canonical model method for modal logics),
not Chapter 1. CZ's Chapter 5 canonical model is the infinite Kripke model of all MCS worlds,
which is what the existing `Completeness.lean` implements.

**The critical divergence**: The codebase's existing propositional MCS infrastructure (`MCS.lean`)
implements the Henkin-style approach — but this is NOT what CZ Chapter 1 presents. CZ Chapter 1
proves completeness for the specific formula at hand via finite tableaux. The Henkin/MCS approach
for propositional logic is an adaptation from the modal chapter, not CZ Chapter 1 directly.

**Impact on implementation**: This is actually **not a blocker** — the Henkin/MCS approach IS
a valid proof of propositional completeness, and the codebase's MCS infrastructure supports it.
The teammates recommending CZ Chapter 1 as "the direct template" are technically wrong about
which CZ chapter uses which method, but the recommended proof strategy (Henkin/MCS via
`canonicalValuation`) is still correct and supported by the codebase. The correct citation
for the Henkin/MCS propositional approach is CZ Chapter 5 (canonical models), not Chapter 1.

**Verdict**: The proposed implementation is sound, but should not be described as "following
CZ Chapter 1" — it follows the Henkin/MCS approach from CZ Chapter 5 / BdRV Chapter 4,
simplified by dropping the modal operators.

---

## Risk 2: CZ's Intuitionistic Completeness Uses Hintikka Systems — Not MCS

**Claimed in round-1**: Intuitionistic completeness uses "canonical model with prime/saturated
sets" that can be adapted from the propositional/modal MCS infrastructure.

**What CZ actually says** (Theorem 2.43, pp. 45–46): CZ proves intuitionistic completeness via
**Hintikka systems**, which are:

- A set `T` of **disjoint saturated tableaux** (pairs `(Γ, A)` of formula sets)
- A partial order `S` on `T` (the accessibility relation)
- Satisfying conditions (HS1): for `(Γ, A) ∈ T` and `φ ∧ ψ ∈ Γ`, etc.
- And (HS2): for `φ → ψ ∈ A`, there exists a successor `(Γ', A') ∈ T` with `φ ∈ Γ'` and `ψ ∈ A'`

The proof builds a Hintikka system for the tableau `(∅, {φ})` by:
1. Taking `T` = all disjoint saturated consistent tableaux over `Sub(φ)`
2. Ordering by `(Γ, A) ≤ (Γ', A')` iff `Γ ⊆ Γ'`
3. Showing this forms a Hintikka system (only condition HS2 requires work)
4. By Proposition 2.31, any Hintikka system induces a countermodel

**This is fundamentally different from the MCS/Henkin approach.** A Hintikka system
is not a maximally consistent set — it is a partial Kripke frame built from finite tableau pairs.
The CZ approach works over the FINITE subformula closure `Sub(φ)`, which gives a **decidability
proof** as a byproduct.

**What the existing MCS infrastructure provides**: `SetMaximalConsistent`, `negation_complete`
(φ ∈ S ∨ ¬φ ∈ S). The `negation_complete` property is a **classical** fact — it relies on
the deduction theorem and the maximality condition. For intuitionistic logic:
- `negation_complete` does NOT hold — an MCS in intuitionistic logic need not contain
  either φ or ¬φ. (Intuitionistic logic is not negation-complete; `φ ∨ ¬φ` is not derivable.)
- The `SetMaximalConsistent.negation_complete` theorem in `Consistency.lean` (line 257) uses
  `by_contra` and `push_Not` — it is a classical proof in the meta-theory that works for any
  derivation system, BUT its conclusion `φ ∈ S ∨ HasImp.imp φ HasBot.bot ∈ S` only holds
  because it uses the deduction theorem plus maximality.

**The actual problem**: For intuitionistic completeness via MCS (prime filter approach), we need
**prime filters**, not maximal consistent sets. A prime filter T satisfies:
- `φ → ψ ∈ T` iff `∀ w ≥ T, φ ∈ w → ψ ∈ w` (requires a Kripke-style argument)
- Lindenbaum for prime filters requires a different saturation condition

The existing `SetMaximalConsistent` framework uses `¬SetConsistent D (insert φ S)` as the
maximality condition. For intuitionistic logic, this gives a classically-maximal set, but this
does NOT correspond to a point in the canonical intuitionistic Kripke model. The canonical
model for intuitionistic logic has **prime theories** as worlds, not maximally consistent sets.

**Verdict: HIGH RISK.** The MCS infrastructure cannot be directly applied to intuitionistic
completeness. A separate Kripke-based semantic infrastructure and a different canonical model
construction are required. This is approximately 3-5x more work than the classical case.

---

## Risk 3: The Propositional DerivationTree Is NOT Parameterized Over Axioms

**Claimed in round-1**: The modal `DerivationTree (Axioms : Proposition Atom → Prop)` is
parameterized, enabling different logics via axiom predicates. The propositional analogue
would parameterize similarly for K/S/EFQ/Peirce subsets.

**What the code actually shows**: The propositional `DerivationTree` in `Derivation.lean`
(lines 59–73) is:

```lean
inductive DerivationTree : List (PL.Proposition Atom) → PL.Proposition Atom → Type _
```

It uses `ax : PropositionalAxiom φ → DerivationTree Γ φ`, where `PropositionalAxiom` is
a **hardcoded** inductive type with all four constructors (implyK, implyS, efq, peirce).
There is **no axiom parameter** — the system hardcodes the classical axioms.

**To prove completeness for `HilbertInt` (no peirce) or `HilbertMin` (no efq, no peirce)**,
one would need either:
1. A separate derivation tree type `DerivationTreeInt` with only implyK/implyS/efq axioms,
2. Or a parameterized version analogous to the modal `DerivationTree (Axioms : ...)`,
3. Or use `Subtype`/filter approach restricting `PropositionalAxiom` to a subset.

None of these exist. The `Instances.lean` file only registers `ClassicalHilbert` for
`HilbertCl`, leaving `HilbertMin` and `HilbertInt` as opaque tag types with NO instances
registered — they are declared in `ProofSystem.lean` (lines 367, 370) but have zero instances.

**Concrete impact**: To prove `MinimalHilbert` soundness/completeness, we need a derivation
tree for minimal logic (no EFQ, no Peirce). But no such tree exists. Two options:
1. Create `MinimalPropositionalAxiom` and `MinimalDerivationTree`, then `MinimalMCS`,
   then minimal soundness/completeness — this requires creating 3+ new files for each level.
2. Use the parameterized modal `DerivationTree` as a template and refactor the propositional
   system to also use an axiom parameter — this is a larger refactor of existing code.

Either way, the scope is significantly larger than round-1 reports assumed.

**Verdict: HIGH RISK.** The task description says "scope includes ALL THREE levels," but only
the classical level has existing derivation infrastructure. The minimal and intuitionistic levels
require new derivation tree types or significant refactoring.

---

## Risk 4: The `negation_complete` MCS Property Requires Classical Reasoning in the Meta-Theory

**This is subtle and important.** The `negation_complete` theorem in `Consistency.lean` (line 257):

```lean
theorem SetMaximalConsistent.negation_complete
    (D : DerivationSystem F) (hdt : HasDeductionTheorem D)
    {S : Set F} (h_mcs : SetMaximalConsistent D S)
    (φ : F) : φ ∈ S ∨ HasImp.imp φ HasBot.bot ∈ S
```

This proof uses `by_contra` (classical negation elimination in the meta-theory). This is fine
when proving **classical** propositional completeness: the meta-theory can be classical even
if the object logic is not.

However, this creates a conceptual issue for the intuitionistic/minimal cases: the completeness
proof for intuitionistic logic (if attempted via canonical MCS) would use `negation_complete`
to establish that the canonical model has the right truth-value for every formula. But
`negation_complete` for an intuitionistic MCS says `φ ∈ S ∨ ¬φ ∈ S` — this is exactly what
intuitionistic logic does NOT validate at the object level. We would be proving completeness
of intuitionistic logic using a fact about the canonical world structure that only holds because
the **meta-theory** is classical.

**This is actually standard practice** (the meta-theory being classical does not invalidate
the completeness proof), but it means we cannot prove intuitionistic completeness by a direct
analogy with the classical completeness proof — the canonical model for IPC is the Heyting
algebra / prime filter model, not the Boolean / MCS model.

**Verdict: MEDIUM RISK.** Not a blocker for the classical case, but confirms that the MCS
approach cannot be straightforwardly extended to the intuitionistic case.

---

## Risk 5: Minimal Logic Semantics Is NOT Just "Intuitionistic Without EFQ"

**Claimed in round-1 scope description**: "Minimal: Like intuitionistic but without the
bottom condition."

**What the literature actually says**: Minimal logic (Johansson, 1937) differs from
intuitionistic logic in how `⊥` (bottom/falsum) is interpreted. There are two formulations:

**Formulation A** (standard): Minimal logic has the same Kripke semantics as intuitionistic
logic, but `⊥` is treated as a **propositional atom** that can be forced at some worlds.
In other words, the forcing clause is:
- `(M, w) ⊩ ⊥` iff `w ∈ V(⊥)` (for some upward-closed set V(⊥))

This is radically different from intuitionistic semantics where `(M, w) ⊩ ⊥` is always false
(⊥ is universally unforced at every world in every model).

**Formulation B** (equivalent): Minimal logic is characterized by Kripke frames with an
arbitrary "falsity predicate" on worlds — a distinguished subset of worlds where `⊥` holds —
satisfying upward-closure. This is sometimes called "Kripke semantics for minimal logic" or
"N-frames" (Colacito, de Jongh, Vardas).

**The critical implication for the codebase**: The propositional `Proposition Atom` type
(in `Defs.lean`) treats `⊥` as a **constant constructor** `.bot` that is ALWAYS false:
```lean
| bot
```
And the `Defs.lean` defines the satisfaction relation for classical logic where `.bot` is False.
For intuitionistic Kripke semantics, `.bot` is also always false (never forced).

But for **minimal** logic, `.bot` must be treated differently: it is potentially forceable at
some worlds. This means the formula type itself needs a different semantic interpretation for
minimal logic — one where `.bot` behaves like an atom with an upward-closed valuation.

**Can this be done in the existing `PL.Proposition` type?** Possibly, by defining:
```lean
-- Kripke semantics for minimal logic
def ForcesMin (m : KripkeModel W Atom) (w : W) : PL.Proposition Atom → Prop
  | .atom p => p ∈ m.V w
  | .bot    => w ∈ m.V_bot  -- special field for ⊥
  | .imp φ ψ => ∀ w' ≥ w, ForcesMin m w' φ → ForcesMin m w' ψ
```

This requires a **different model type** than the one used for intuitionistic logic — one with
an extra field `V_bot : UpwardClosedSubset W` for where ⊥ is forced.

**The codebase's existing modal Kripke infrastructure** (`Modal.Model`, `Modal.Satisfies`) is
for classical modal logic. It does NOT support ordered worlds or intuitionistic/minimal forcing
semantics. There is NO existing Kripke frame structure for intuitionistic or minimal propositional
semantics in the codebase.

**Verdict: HIGH RISK.** Minimal logic requires a completely new semantic infrastructure not
related to the existing modal Kripke infrastructure. The claim that minimal logic is
"similar to intuitionistic" is correct at the proof-system level but FALSE at the semantic
level — the models are structurally different.

---

## Risk 6: The Scope Is Not Three Parallel Tasks — It Is One Task Plus Two Much Harder Tasks

**The round-1 reports treat the three levels as roughly equal in effort.** This is incorrect.

**Classical completeness (HilbertCl)**: Straightforward. All infrastructure exists. Estimated
work: 3 new files (~200-300 lines total). The Henkin/MCS approach works directly.

**Intuitionistic completeness (HilbertInt)**:
1. New derivation tree type for intuitionistic logic (no Peirce axiom)
2. New deduction theorem for the intuitionistic system
3. New MCS-like theory for prime filters (or Hintikka systems)
4. New Kripke semantic infrastructure (partially ordered worlds, upward-closed valuations)
5. New forcing relation
6. New canonical model (with prime filter worlds and accessibility = subset ordering)
7. New truth lemma
8. New completeness theorem
Estimated work: 8-15 new files, 800-2000 lines. Complexity is comparable to the entire modal
K/T/S4/S5 stack.

**Minimal completeness (HilbertMin)**:
1-8. Everything for intuitionistic (since minimal is a sub-system)
9. Different bottom-handling in semantics (V_bot field or ⊥ as atom)
10. New soundness proof for EFQ-free derivation trees
11. Different canonical model (worlds where ⊥ may be forced)
Estimated work: comparable to intuitionistic, plus additional complexity for ⊥ semantics.

**The practical implication**: If the task intends all three levels, this is NOT a single
implementation task — it is at minimum 3 separate phased tasks, with the intuitionistic and
minimal cases each requiring approximately 10x more work than the classical case.

**Recommendation**: Phase the work. Phase 1 (classical completeness) is well-scoped and can
be completed cleanly. Phases 2-3 (intuitionistic/minimal) should be separate tasks with
their own research and planning rounds.

**Verdict: SCOPE RISK — HIGH.** Attempting all three levels in one implementation pass without
separate planning for intuitionistic/minimal will almost certainly result in sorry-deferral
patterns or incomplete work on the non-classical cases.

---

## Risk 7: Typeclass Instances for HilbertMin and HilbertInt Do Not Exist

**What was found in the code**: `ProofSystem.lean` declares:
```lean
opaque Propositional.HilbertMin : Type := Empty
opaque Propositional.HilbertInt : Type := Empty
```

`Instances.lean` registers `ClassicalHilbert Propositional.HilbertCl` only. There are
**zero instances** for `HilbertMin` or `HilbertInt` in the entire codebase.

**To register `MinimalHilbert Propositional.HilbertMin` instances**, we need:
1. An `InferenceSystem` instance: this requires a derivation tree for minimal logic
2. `ModusPonens`, `HasAxiomImplyK`, `HasAxiomImplyS` instances
3. The `MinimalHilbert` bundled instance

But step 1 requires a **minimal derivation tree** (without EFQ and Peirce axiom cases).
The existing `PropositionalAxiom` type includes all four axioms (implyK, implyS, efq, peirce).
We cannot register a `MinimalHilbert` instance using the existing `propDerivationSystem`
because it derives ALL four axioms, making it a classical system, not a minimal one.

Similarly for `IntuitionisticHilbert HilbertInt`: we need a derivation system without Peirce.

**The design question this raises**: Should the propositional derivation system be refactored
to match the modal pattern — i.e., `DerivationTree (Axioms : PL.Proposition Atom → Prop)` with
a parameterized axiom set — so that different systems (`MinimalAxiom`, `IntAxiom`, `ClassicalAxiom`)
can all use the same tree structure? This would be the cleaner architecture.

**The cost of not refactoring**: Three separate inductive types (`MinimalDerivationTree`,
`IntDerivationTree`, `ClassicalDerivationTree`), three separate deduction theorem proofs,
three separate MCS instantiations — substantial code duplication.

**Verdict: ARCHITECTURE RISK.** The task requires a design decision before implementation:
refactor propositional DerivationTree to be parameterized (like modal), or build three
separate non-parameterized systems. The former requires touching existing code.

---

## Summary Table

| # | Risk | Severity | Impact |
|---|------|----------|--------|
| R1 | CZ Ch.1 uses tableaux, not MCS — strategy attribution is wrong | Low | No implementation impact, just citation |
| R2 | Intuitionistic completeness needs Hintikka/prime-filter, not MCS | **High** | MCS infrastructure unusable for Int/Min cases |
| R3 | PropositionalDerivationTree hardcodes classical axioms; Min/Int have no derivation trees | **High** | Requires new infrastructure for each level |
| R4 | negation_complete requires classical meta-theory; confirms MCS ≠ Int canonical model | Medium | Confirms R2 |
| R5 | Minimal logic semantics requires different ⊥ treatment (potentially forceable) | **High** | New model type required |
| R6 | Scope: classical ~200 lines; each of Int/Min ~1000-2000 lines | **High** | Three-level scope is 10x underestimated |
| R7 | HilbertMin/HilbertInt have zero typeclass instances; cannot be used until built | Medium | Requires architectural decision |

---

## What Was Correctly Assessed in Round 1

The round-1 reports correctly identified:
- All MCS infrastructure for classical completeness is present and correct
- Classical soundness/completeness is feasible and straightforward
- The modal `k_completeness` / `truth_lemma` pattern IS the right template for classical PL
- No Mathlib lemmas reduce burden
- `[DecidableEq Atom]` is harmless

These assessments stand. The round-1 reports are reliable for classical completeness.

---

## What Was Underestimated or Missed in Round 1

1. **CZ Theorem 2.43 proof strategy**: Uses Hintikka systems, not canonical models — the
   codebase has no Hintikka system infrastructure.

2. **Intuitionistic canonical model ≠ classical canonical model**: Prime filters vs. MCS.
   The `negation_complete` property of MCS is classically valid but does not generalize to
   intuitionistic completeness.

3. **Minimal logic semantics**: ⊥ is potentially forceable; requires a new model type with a
   separate valuation for ⊥. No existing infrastructure for this.

4. **Scope was underestimated by 10x**: The round-1 reports say "3 new files" for the
   whole task. For classical only, that is correct. For all three levels, it is 15-25 new files.

5. **DerivationTree architecture**: The existing propositional DerivationTree cannot serve
   as the base for minimal/intuitionistic instances without either refactoring or duplication.

---

## Recommended Phase Structure

**Phase 1 (Do Now)**: Classical HilbertCl soundness and completeness
- 3 new files: `Semantics/Basic.lean`, `Metalogic/Soundness.lean`, `Metalogic/Completeness.lean`
- All infrastructure exists; no blockers; ~200-300 lines; no sorry risk
- Register `ClassicalHilbert HilbertCl` instances in `Instances.lean` (already done)

**Phase 2 (Separate Task)**: Refactor or extend DerivationTree for parameterization
- Either adapt propositional DerivationTree to be parameterized over axioms (like modal)
- Or create `MinimalPropositionalAxiom` / `IntuitionisticPropositionalAxiom` sub-types
- Decision required before phases 3-4 can proceed

**Phase 3 (Separate Task)**: Intuitionistic HilbertInt soundness and completeness
- Requires: partially ordered Kripke frames, upward-closed valuations, forcing relation
- New canonical model (prime filter worlds with subset accessibility)
- New Hintikka system or prime filter infrastructure
- New instances: `IntuitionisticHilbert HilbertInt`

**Phase 4 (Separate Task)**: Minimal HilbertMin soundness and completeness
- Requires: same as Phase 3, plus different ⊥ semantics
- New model type with `V_bot` (forceable bottom)
- New instances: `MinimalHilbert HilbertMin`

---

## Conclusion

The previous research rounds identified the right approach for **classical completeness** and the
implementation plan for that level is sound. However, the assumption that intuitionistic and
minimal completeness are "similar" or can be done in the same pass is incorrect. The semantic
infrastructure for Int and Min does not exist in the codebase, the MCS approach used for
classical logic does not extend to these cases, and the proof strategies in CZ require Hintikka
systems rather than canonical models for the Int case.

Attempting all three levels in a single implementation task without separate planning will
violate the zero-sorry policy — the intuitionistic/minimal cases will block mid-implementation
because required infrastructure (parameterized derivation trees, Kripke frame types, prime
filter theory) does not exist and its scope is substantial.

**Strong recommendation**: Mark task 112 as "classical completeness only" for the current
implementation. Create successor tasks for intuitionistic and minimal completeness with their
own research and planning rounds.
