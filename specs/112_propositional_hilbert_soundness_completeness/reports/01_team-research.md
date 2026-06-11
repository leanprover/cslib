# Research Report: Task #112

**Task**: Establish soundness and completeness for propositional Hilbert proof systems
**Date**: 2026-06-10
**Mode**: Team Research (4 teammates)
**Session**: sess_1781155000_a3b4c5

---

## Summary

All four teammates converge on an exceptionally clear picture with strong agreement and no
significant conflicts. The propositional Hilbert proof system in cslib already has a complete
syntactic and MCS infrastructure — every lemma needed for a Henkin/MCS completeness proof is
present and verified. The only missing components are the semantic layer (valuations, evaluation,
tautology) and the soundness/completeness theorems themselves. These can be implemented as three
new files totaling approximately 250-290 lines, following the existing modal completeness
infrastructure as a near-verbatim template.

The strategic insight from Teammate D reinforces this assessment: the codebase has a uniform
three-layer metalogic architecture (generic foundation, logic-specific MCS, soundness/completeness)
that is complete for modal and temporal logics but has only layers A and B for propositional
logic. Task 112 fills in layer C for propositional logic. Teammate A establishes that the correct
reference is Chagrov and Zakharyaschev Chapter 1, which uses the same Henkin/MCS approach
(not Kalmar's truth-table induction) and thus directly motivates the proof structure already
used in the codebase.

The one open question requiring user input before planning is scope: the task description says
"propositional Hilbert proof systems" (plural), which could include intuitionistic and minimal
Hilbert systems. Intuitionistic completeness requires Kripke semantics — a completely different
and substantially more complex proof. Teammate C identified this as a high-severity scope risk.
The team's collective recommendation is to scope task 112 to classical propositional logic
(`HilbertCl`) only, and open a separate task for intuitionistic/minimal cases if needed.

---

## Key Findings

### Recommended Reference Source

**Primary reference: Chagrov and Zakharyaschev, *Modal Logic* (1997), Chapter 1.**

Teammate A establishes this as the optimal reference for the following reasons:

1. CZ Chapter 1 presents classical propositional logic (`Cl`) using implication and falsum as
   primitives — an exact match with cslib's `atom/bot/imp` formula language.
2. CZ uses the Henkin/MCS canonical construction for completeness, NOT Kalmar's inductive
   truth-table method. This is the technique already used for modal completeness in the codebase,
   making CZ Chapter 1 a structural match, not merely a content match.
3. CZ Chapter 1 is explicitly designed as a propositional warm-up that directly motivates and
   parallels the modal completeness proof in later chapters — the same relationship that holds
   between propositional and modal metalogic in cslib.
4. The four CZ axiom schemata (`K: φ → (ψ → φ)`, `S: (φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))`,
   `⊥-elim: ⊥ → φ`, `Peirce: ((φ → ψ) → φ) → φ`) exactly match `implyK`, `implyS`, `efq`,
   and `peirce` in `PropositionalAxiom`.

Alternatives considered and rejected:
- Mendelson uses Kalmar's method (truth-table induction), which does not generalize to modal
  logic and does not match the codebase's approach.
- van Dalen uses natural deduction as the primary proof system — structural mismatch.
- Enderton's propositional completeness is also Kalmar-style; Henkin completeness appears only
  for first-order logic.
- Blackburn, de Rijke, Venema does not independently prove propositional completeness; it
  assumes propositional soundness/completeness as background and cannot serve as the reference
  for the propositional base case.

**Secondary reference: Blackburn, de Rijke, Venema, *Modal Logic* (2001), Chapters 4+** — for
the modal counterparts (already in use in the codebase).

### Existing Infrastructure Assessment

The propositional subsystem is complete at the proof-system and MCS levels (Layers A and B).
Every lemma needed for the Henkin/MCS completeness proof is already proven.

**Present and verified:**
- `Cslib/Logics/Propositional/Defs.lean`: `Proposition Atom` with `atom | bot | imp` primitives,
  derived connectives (`neg`, `top`, `or`, `and`, `iff`)
- `Cslib/Logics/Propositional/ProofSystem/Axioms.lean`: `PropositionalAxiom` with `implyK`,
  `implyS`, `efq`, `peirce`
- `Cslib/Logics/Propositional/ProofSystem/Derivation.lean`: `DerivationTree`, `Deriv`,
  `Derivable`, `propDerivationSystem`
- `Cslib/Logics/Propositional/ProofSystem/Instances.lean`: `ClassicalHilbert` instance
- `Cslib/Logics/Propositional/Metalogic/DeductionTheorem.lean`: Full deduction theorem
- `Cslib/Logics/Propositional/Metalogic/MCS.lean`: `PropSetConsistent`,
  `PropSetMaximalConsistent`, `prop_lindenbaum`, `prop_closed_under_derivation`,
  `prop_implication_property`, `prop_negation_complete`, `prop_mcs_bot_not_mem`,
  `prop_mcs_neg_of_not_mem`, `prop_mcs_not_mem_of_neg`, `prop_mcs_mem_iff_neg_not_mem`
- `Cslib/Foundations/Logic/Metalogic/Consistency.lean`: Generic `DerivationSystem`,
  `SetConsistent`, `SetMaximalConsistent`, Zorn/Lindenbaum, `closed_under_derivation`,
  `implication_property`, `negation_complete`

**Missing (Layer C — all semantic infrastructure):**
- No `Semantics.lean` or equivalent defining propositional valuations, evaluation function,
  and validity/tautology predicate
- No `Soundness.lean` proving `Derivable φ → Tautology φ`
- No `Completeness.lean` proving `Tautology φ → Derivable φ` via canonical valuation from MCS

Neither Mathlib nor any external formalization (Isabelle/AFP, Coq/MathComp, other Lean 4
projects) provides drop-in lemmas for this specific `atom/bot/imp` Hilbert system. The
in-codebase modal completeness infrastructure is the correct and direct template.

### Architectural Alignment Strategy

The codebase has a uniform three-layer metalogic architecture:

| Layer | Generic foundation | Modal instance | Propositional instance |
|-------|--------------------|----------------|------------------------|
| A | `Foundations/Logic/Metalogic/Consistency.lean` | (used) | (used) |
| B | Logic-specific MCS | `Modal/Metalogic/MCS.lean` | `Propositional/Metalogic/MCS.lean` (exists) |
| C | Soundness + Completeness | `Modal/Metalogic/Soundness.lean` + `Completeness.lean` | **MISSING** |

Teammate D establishes that the propositional Layer C should be structurally identical to the
modal Layer C, with these simplifications:
- No `CanonicalWorld` subtype needed — use `Set (PL.Proposition Atom)` or `PropMCS` directly
- No accessibility relation
- No `box` case in the Truth Lemma
- Canonical "model" is a single valuation `v p = (atom p ∈ M)`, not a Kripke structure
- `Evaluate v φ` has three cases (`atom`, `bot`, `imp`) vs. four (`atom`, `bot`, `imp`, `box`)

The proposed naming convention mirrors the modal pattern:
- `prop_axiom_sound` (analogous to `k_axiom_sound`, `axiom_sound`)
- `prop_soundness` (analogous to `soundness`, `k_soundness`)
- `CanonicalValuation` / `PropCanonicalValuation` (analogous to `CanonicalModel`)
- `prop_truth_lemma` (analogous to `truth_lemma`, `k_truth_lemma`)
- `prop_completeness` (analogous to `k_completeness`, `completeness`)

The `PL.Proposition.toModal` embedding already exists in `FromPropositional.lean`, enabling a
future coherence theorem (semantics-preservation under embedding) as a natural next step after
task 112, but not required for task 112 itself.

### Gaps and Risks

**Scope ambiguity (High severity):** The task says "propositional Hilbert proof systems"
(plural). The codebase defines `HilbertMin`, `HilbertInt`, and `HilbertCl` as a hierarchy.
Intuitionistic (`HilbertInt`) and minimal (`HilbertMin`) completeness require Kripke semantics
over ordered frames — a completely different and substantially more complex proof structure. The
bivalent semantics (`Eval v φ`) does NOT work for intuitionistic logic (it validates `¬¬p → p`,
which is not intuitionistically valid). If the task intends to cover more than `HilbertCl`, the
scope more than doubles and requires entirely new semantic infrastructure.

**Technical risks (Low-to-medium severity):**
- The Truth Lemma `imp` case requires inline derivation tree constructions following the modal
  pattern in `Completeness.lean` lines 178–222. This is the only non-trivial proof step.
- The `propDerivationSystem` uses `List`-based contexts while the MCS framework is `Set`-based;
  this bridge already exists and works correctly via `closed_under_derivation`.
- The `[DecidableEq Atom]` constraint is inherited throughout but is harmless.
- `noncomputable` will be required throughout (uses `Classical.propDecidable`).
- Soundness proof must not copy-paste the modal proof verbatim — the modal `DerivationTree` has
  a `.necessitation` constructor that the propositional one lacks.
- The `Prop` vs. `Bool` choice for `Valuation` output: the Prop-valued approach (`Atom → Prop`)
  is recommended for consistency with the rest of the codebase.

---

## Synthesis

### Points of Agreement

All four teammates converge on the following without exception:

1. **All MCS infrastructure is complete.** Every lemma needed for the Henkin/MCS completeness
   proof (`prop_lindenbaum`, `prop_closed_under_derivation`, `prop_implication_property`,
   `prop_negation_complete`, `prop_mcs_bot_not_mem`, and the negation membership lemmas) is
   already proven. No new MCS work is required for task 112.

2. **The implementation has three phases.** The task decomposes into: (a) propositional
   semantics file defining `Valuation`, `Evaluate`/`Eval`, and `Tautology`/`Valid`; (b)
   soundness theorem by induction on `DerivationTree`; (c) completeness theorem via canonical
   valuation from MCS and Truth Lemma. All three phases are well-understood and have clear
   precedents in the existing codebase.

3. **The modal completeness code is the direct template.** The propositional case is the modal
   case with the `box` constructor and necessitation rule removed. The `k_truth_lemma` in
   `KCompleteness.lean` (lines 168–261) is the direct model for `prop_truth_lemma`. The
   `k_completeness` theorem (lines 269–323) transfers with minimal changes.

4. **Henkin/MCS approach (not Kalmar).** CZ Chapter 1 is the correct reference precisely
   because it uses the same canonical model strategy as the codebase, not a truth-table
   induction. This ensures structural alignment between propositional and modal completeness.

5. **Scope should start with classical.** The team unanimously recommends scoping task 112 to
   `ClassicalHilbert` (`HilbertCl`) only. Intuitionistic/minimal cases are categorically
   different in their semantic machinery and should be separate tasks if desired.

6. **No Mathlib or external lemmas reduce the burden.** Confirmed by Teammate B across
   `lean_leansearch`, `lean_loogle`, and `lean_leanfinder`. The in-codebase modal infrastructure
   is the correct and only relevant template.

7. **Estimated implementation size is small.** All teammates estimate 250-290 lines across three
   files, achievable in a single implementation wave.

### Conflicts Resolved

No genuine conflicts were identified across the four reports. The only minor variations are
design choices rather than disagreements:

**File layout variation**: Teammate A proposes `Semantics.lean` (single file), Teammate B
proposes `Semantics/Basic.lean`, Teammate C proposes `Semantics/Eval.lean`, and Teammate D
proposes `Semantics/Valuation.lean` with an optional `Semantics/Validity.lean`. These
are equivalent; the choice between a single file and a subdirectory is a minor organizational
preference. **Resolution**: Use `Cslib/Logics/Propositional/Semantics/Basic.lean` (Teammate B's
proposal), matching the modal pattern where `Modal/Basic.lean` contains the semantics.

**Parameterized vs. concrete soundness**: Teammate C recommends a concrete (non-parameterized)
soundness proof over `PropositionalAxiom` rather than a parameterized theorem with a validity
callback. Teammates A, B, and D implicitly recommend following the modal parameterized pattern.
**Resolution**: Include both a parameterized `prop_soundness` and a concrete `prop_soundness_derivable`
wrapper, mirroring the modal pattern. The parameterized form is useful if future sub-logics
(intuitionistic, minimal) are added.

### Open Questions

**Q1 (Scope — RESOLVED by user):** User confirmed: ALL three levels — `MinimalHilbert`,
`IntuitionisticHilbert`, AND `ClassicalHilbert`. This means:
- Classical: bivalent truth-value semantics (straightforward, ~250 lines)
- Intuitionistic: Kripke semantics with persistent valuations (moderate, shares infrastructure with modal logic)
- Minimal: Kripke semantics without explosion condition (similar to intuitionistic)
The intuitionistic/minimal cases significantly expand scope but align well with the existing
modal Kripke infrastructure. The propositional Kripke semantics will share definitions with
the modal Kripke semantics (frames, accessibility, persistence).

**Q2 (Valuation type — design choice):** Should `Valuation` use `Atom → Prop` (Prop-valued) or
`Atom → Bool` (Bool-valued)? The team recommends `Atom → Prop` for consistency with the modal
`Model` valuation. This is answerable without user input but worth noting.

**Q3 (Canonical valuation subtype):** Should the canonical valuation in completeness use a
`{ S // PropSetMaximalConsistent S }` subtype (mirroring modal `CanonicalWorld`) or plain
`S : Set (Proposition Atom)`? Both work; the subtype is cleaner and mirrors the existing modal
infrastructure. Recommended: use subtype.

**Q4 (Both soundness forms):** Should the soundness theorem be stated at the `DerivationTree`
level (strong form) and at the `Derivable` (existential) level? Recommended: include both,
as the modal code has both `soundness` and `soundness_derivable`.

---

## Recommended Task Decomposition

Based on the combined findings, task 112 decomposes naturally into three implementation phases:

**Phase 1: Propositional Semantics** (~50-80 lines)
- New file: `Cslib/Logics/Propositional/Semantics/Basic.lean`
- Defines `Valuation Atom := Atom → Prop`
- Defines `Evaluate : Valuation Atom → Proposition Atom → Prop` by structural recursion on
  `atom`, `bot`, `imp` cases
- Defines `Tautology φ := ∀ v, Evaluate v φ`
- Defines `Satisfiable φ := ∃ v, Evaluate v φ`
- No proofs in this file — definitions only
- Dependency: `Propositional/Defs.lean` only

**Phase 2: Soundness** (~60-80 lines)
- New file: `Cslib/Logics/Propositional/Metalogic/Soundness.lean`
- Proves `prop_axiom_sound : PropositionalAxiom φ → Tautology φ` (four cases, all trivial by
  unfolding `Evaluate`)
- Proves parameterized `prop_soundness : DerivationTree Γ φ → (∀ ψ ∈ Γ, Evaluate v ψ) →
  Evaluate v φ` (induction on tree; no `.necessitation` constructor)
- Proves `prop_soundness_derivable : Derivable φ → Tautology φ` (wrapper for empty context)
- Dependency: `Semantics/Basic.lean`, `ProofSystem/Derivation.lean`, `ProofSystem/Axioms.lean`
- Pattern: `Modal/Metalogic/Soundness.lean` with `.necessitation` case removed

**Phase 3: Completeness** (~100-130 lines)
- New file: `Cslib/Logics/Propositional/Metalogic/Completeness.lean`
- Defines `canonicalValuation (M : PropMCS) : Valuation Atom := fun p => atom p ∈ M.val`
- Proves `prop_truth_lemma (M : PropMCS) : ∀ φ, Evaluate (canonicalValuation M) φ ↔ φ ∈ M.val`
  - `atom p` case: trivial by definition
  - `bot` case: uses `prop_mcs_bot_not_mem`
  - `imp φ ψ` case: uses `prop_implication_property`, `prop_negation_complete`,
    `prop_mcs_neg_of_not_mem`; follow `KCompleteness.lean` lines 178-222 exactly
- Proves `prop_completeness : Tautology φ → Derivable φ` (by contradiction: assume not
  derivable, `{¬φ}` consistent by soundness, extend to MCS by `prop_lindenbaum`, apply
  `prop_truth_lemma` to get contradiction)
- Optionally proves `prop_iff_tautology : Tautology φ ↔ Derivable φ` (soundness + completeness)
- Dependency: `Semantics/Basic.lean`, `Metalogic/Soundness.lean`, `Metalogic/MCS.lean`
- Pattern: `KCompleteness.lean` with box-witness construction entirely removed

**Module registration**: Update `Cslib.lean` top-level to import the three new modules.

**Scope confirmed — all three levels**: User confirmed that intuitionistic and minimal cases
ARE in scope. The task should be expanded into sub-tasks:
- Sub-task A: Classical soundness/completeness (truth-value semantics, Phases 1-3 above)
- Sub-task B: Propositional Kripke semantics (frames, persistent valuations, forcing)
- Sub-task C: Intuitionistic soundness/completeness (Kripke semantics, no Peirce axiom)
- Sub-task D: Minimal soundness/completeness (Kripke semantics, no EFQ axiom)
- Sub-task E: Module integration and Cslib.lean registration

The Kripke semantics for intuitionistic/minimal logic will share infrastructure with the
existing modal Kripke semantics. The canonical model construction for intuitionistic logic
uses prime theories (deductively closed, disjunction property) rather than MCS — this is a
different but well-understood construction.

---

## Teammate Contributions

| Teammate | Angle | Status | Confidence |
|----------|-------|--------|------------|
| A | Primary sources (best reference) | completed | high |
| B | Existing formalizations (proof patterns) | completed | high |
| C | Critic (gaps, risks, blind spots) | completed | high |
| D | Horizons (strategic alignment) | completed | high |

---

## References

### Primary Literature
- Chagrov, A. and Zakharyaschev, M. (1997). *Modal Logic*. Oxford Logic Guides, Vol. 35.
  Oxford University Press. [Chapter 1 — propositional soundness/completeness via Henkin/MCS]
  https://global.oup.com/academic/product/modal-logic-9780198537793
- Blackburn, P., de Rijke, M., and Venema, Y. (2001). *Modal Logic*. Cambridge Tracts in
  Theoretical Computer Science, Vol. 53. Cambridge University Press. [Chapters 4+, already in
  use for modal completeness in the codebase]
  https://www.cambridge.org/core/books/modal-logic/F7CDB0A265026BF05EAD1091A47FCF5B

### Alternative References (Considered and Rejected)
- Mendelson, E. *Introduction to Mathematical Logic*, 6th ed. Routledge. [Uses Kalmar method —
  does not match codebase's Henkin approach]
- van Dalen, D. *Logic and Structure*. [Uses natural deduction — structural mismatch]
- Enderton, H.B. *A Mathematical Introduction to Logic*. [Propositional completeness is
  Kalmar-style; Henkin only for first-order]

### External Formalizations (Confirmed Non-Applicable)
- FormalizedFormalLogic/Foundation — Lean 4 formalization, S5 modal completeness via MCS/Henkin
  https://formalizedformallogic.github.io/Book/
- Bentzen, B. "A Henkin-style completeness proof for the modal logic S5." arXiv:1910.01697
  https://arxiv.org/abs/1910.01697
- Isabelle/AFP "A Sequent Calculus for Classical Logic" (Berghofer) — sequent calculus, not Hilbert
- Mathlib `Classical.prop_complete`, `Mathlib.Tactic.Tauto`, `Sat.Valuation` — not applicable

### Critical Codebase Files
- `Cslib/Logics/Propositional/Metalogic/MCS.lean` — all MCS infrastructure (complete)
- `Cslib/Logics/Propositional/Metalogic/DeductionTheorem.lean` — deduction theorem (complete)
- `Cslib/Logics/Modal/Metalogic/KCompleteness.lean` — direct template for Phase 3 (lines 168-323)
- `Cslib/Logics/Modal/Metalogic/Soundness.lean` — direct template for Phase 2
- `Cslib/Foundations/Logic/Metalogic/Consistency.lean` — generic MCS framework (Layer A)
- `Cslib/Logics/Modal/FromPropositional.lean` — PL→Modal embedding (future coherence theorem)
