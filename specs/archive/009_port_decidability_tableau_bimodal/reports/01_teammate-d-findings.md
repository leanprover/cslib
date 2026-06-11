# Teammate D — Horizons: Strategic Direction for Tableau & Decidability

**Task**: 9 — Port Decidability and Tableau to Bimodal module
**Date**: 2026-06-09
**Angle**: Long-term alignment and strategic direction

## Key Findings

1. **The bimodal tableau is inherently non-compositional.** The 28 expansion rules operate on `Bimodal.Formula` (all 6 constructors: atom, bot, imp, box, untl, snce) with rules for both modal and temporal operators interleaving. This makes the existing BimodalLogic tableau impossible to factor into separate modal and temporal tableau components. The interaction axiom MF and the interplay of box with until/since mean the bimodal decidability result is a fundamentally combined result — not a composition of simpler ones.

2. **Propositional and modal tableau ARE independently valuable — and absent.** While the bimodal tableau cannot be decomposed, cslib currently has NO decidability results for propositional logic, modal logic, or temporal logic individually. These are independently well-studied, simpler, and would serve different user communities. A propositional tableau (~200 lines) and a modal K/S5 tableau (~1,000 lines) would be significant library contributions in their own right.

3. **The roadmap reveals a "vertical depth" strategy, not "horizontal breadth."** The ROADMAP explicitly follows a modular factoring principle: "every component lives at the most general level it can compile at." The four-phase plan (Propositional → Modal+Temporal → Metalogic → Bimodal) proceeds bottom-up. Decidability is at the top of the hierarchy (Wave 5, depends on 4+7). This means the project is committed to depth-first on this particular logic family, not breadth-first across many logics.

4. **Task 41 (shared completeness infrastructure) is the key strategic opportunity.** Task 41 explicitly aims to abstract shared patterns between temporal and bimodal completeness — "to be done after concrete implementations exist." The same principle should apply to decidability: build the concrete bimodal tableau first, then extract a reusable pattern. Premature abstraction is explicitly warned against in the roadmap (Key Design Decision #5: "No generic metalogic typeclass").

5. **The `DerivationSystem` pattern from `Consistency.lean` is the right abstraction template.** The generic MCS framework (Task 29) demonstrates the project's approach to shared infrastructure: define a structure (`DerivationSystem`) with minimal axioms, prove generic results, then instantiate per-logic. A future `TableauSystem` structure could follow the same pattern — but only after concrete implementations exist for multiple logics.

6. **The porting order is already optimal for strategic value.** The dependency graph puts decidability at Wave 5, after completeness infrastructure. This is correct because: (a) the tableau proof extraction requires `DerivationTree` (from Task 4, done), (b) the correctness proof connects tableau closure to derivability via MCS theory (Task 7, done), and (c) FMP results need the completeness framework.

7. **Decidability enables executable decision procedures — a potential "killer feature."** Unlike completeness (which is a meta-theorem about the proof system), decidability gives you a computable `decide` function. In Lean 4, this could theoretically be extracted to executable code via `native_decide`, enabling:
   - A tactic that automatically proves/disproves bimodal formulas
   - Countermodel generation as a debugging tool
   - Integration with Lean's `Decidable` typeclass for use in `if/then/else`
   
   This would make cslib's bimodal logic uniquely useful compared to pen-and-paper formalizations.

8. **Future logic extensions should NOT drive the current architecture.** While cslib could eventually support epistemic (S5-like), deontic, CTL, CTL*, μ-calculus, or PDL, these logics require fundamentally different tableau strategies:
   - CTL/CTL*: tree-model property, different branching
   - μ-calculus: parity games, not standard tableau
   - PDL: Fischer-Ladner closure, different termination argument
   - Description logics: blocking strategies for cycles
   
   Designing for all of these now would be premature. The bimodal tableau (signed formulas + expansion rules + saturation + closure) is already general enough to be instructive for future work.

9. **The FMP sub-task is strategically separable.** Task 9 notes the possible split into (9a) core tableau/decision procedure (~5k lines) and (9b) FMP (~4k lines). This is strategically sound: the decision procedure is the primary deliverable, while FMP is a strengthening result (finite countermodels). Splitting allows the decidability `instance` to land in cslib faster while FMP can follow as a refinement.

10. **Cross-logic composition theory exists but is research-grade, not library-grade.** The theoretical literature on "fusion" of modal logics (Gabbay et al., Wolter & Zakharyaschev) shows that decidability can sometimes transfer through fusion. However, formalizing transfer theorems is itself a significant research project. The BimodalLogic approach — proving decidability directly for the combined logic — is the pragmatic choice for a library.

## Recommended Approach

**Strategy: Port bimodal decidability first as-is (Task 9), then build downward.**

The recommended execution order is:

1. **Now: Port the bimodal tableau (Task 9)** — This is the hardest case and drives the architecture. The BimodalLogic source is mature (~10k lines, proven). Port it faithfully, maintaining the existing structure (SignedFormula → Tableau → Closure → Saturation → ProofExtraction → Correctness → DecisionProcedure).

2. **After Task 9: Build propositional decidability (~200 lines, new)** — A simple truth-table or 2-valued semantic argument yields `Decidable` for propositional logic. This is trivial but fills a gap and proves the pattern at the simplest level.

3. **After Task 9: Build modal K/S5 decidability (~1,000 lines, new)** — The modal tableau is well-studied and significantly simpler than bimodal (no temporal operators, standard branching). It would serve the model theory community independently.

4. **After concrete implementations: Extract shared infrastructure (aligned with Task 41)** — Once propositional, modal, and bimodal decidability exist concretely, identify what can be abstracted. Candidates: `SignedFormula` could be generic over any formula type, `TableauExpansionRule` could be a typeclass, and the correctness theorem structure (closed = derivable, open + saturated = satisfiable) is shared.

5. **Long-term: Consider temporal decidability separately.** Linear temporal logic over the naturals is decidable (Büchi automata), but the tableau approach differs significantly from the bimodal one. This would be new development, not a port.

**Key principle**: The roadmap's "no premature abstraction" philosophy (Key Design Decision #5) applies equally to decidability. Build concrete, then abstract. The bimodal case is the richest and should come first — it will reveal which patterns are truly shareable.

## Evidence/Examples

### Roadmap Alignment

The roadmap states: "The modular factoring analysis identifies ~6,800 lines of content that are reusable above the bimodal level." For decidability, the reusability analysis is:

| Component | Reusable? | Rationale |
|-----------|-----------|-----------|
| `SignedFormula` type | Partially | Concept is generic (T/F annotations), but constructors are formula-specific |
| Tableau expansion rules | No | 28 rules are specific to 6 bimodal constructors + interaction axiom |
| Closure/saturation | Partially | The concepts generalize, but the conditions are logic-specific |
| ProofExtraction | No | Extracts bimodal `DerivationTree` from closed branches |
| Correctness structure | Yes | "Closed = derivable, open+saturated = satisfiable" pattern is universal |
| DecisionProcedure | No | Concrete `Decidable` instance for bimodal formulas |
| FMP | No | Finite model bound depends on bimodal subformula closure |

Approximately 20-30% of decidability infrastructure could eventually be shared — much less than the ~40% for MCS theory. This confirms that the decidability port should proceed concretely first.

### Community Patterns

Other Lean 4 formalization projects for comparison:
- **Mathlib**: No modal logic decidability (only propositional logic semantics)
- **LeanSAT**: Propositional satisfiability via DRAT certificates — entirely different approach (SAT solving, not tableau)
- **lean4-logic** (Iehara): Has some tableau-based completeness for propositional and modal logic, but no decidability instance

This means cslib's bimodal decidability result would be **unique in the Lean ecosystem** — a strong differentiator.

### Import Hierarchy for Decidability

```
Foundations/Logic/Metalogic/Consistency.lean    (generic MCS, Task 29 ✓)
                    ↓
Bimodal/Metalogic/Core/DerivationTree.lean      (Deriv wrapper, Task 7 ✓)
Bimodal/Metalogic/Core/DeductionTheorem.lean    (deduction theorem, Task 7 ✓)
Bimodal/Metalogic/Core/MaximalConsistent.lean   (bimodal MCS, Task 7 ✓)
                    ↓
Bimodal/Metalogic/Decidability/SignedFormula.lean    ← Task 9 starts here
Bimodal/Metalogic/Decidability/Tableau.lean
Bimodal/Metalogic/Decidability/Closure.lean
Bimodal/Metalogic/Decidability/Saturation.lean
Bimodal/Metalogic/Decidability/ProofExtraction.lean
Bimodal/Metalogic/Decidability/Correctness.lean
Bimodal/Metalogic/Decidability/DecisionProcedure.lean
Bimodal/Metalogic/Decidability/CountermodelExtraction.lean
Bimodal/Metalogic/Decidability/FMP/...               ← optional split (9b)
```

All dependencies (Tasks 4, 7) are already complete. Task 9 is unblocked.

### Executable Decision Procedure Opportunity

The `DecisionProcedure.lean` in BimodalLogic provides:
```lean
instance : Decidable (ThDerivable φ) := ...
```

In Lean 4, this enables:
```lean
#eval decide (ThDerivable (.box (.imp p q)))  -- true/false at compile time
```

This is a concrete, usable feature that no other formalized bimodal logic provides. It should be preserved and highlighted in the port.

## Confidence Level

**Medium-High**

**Justification**: High confidence on the strategic ordering (bimodal first, then simpler logics) and the non-compositionality of the bimodal tableau — these follow directly from the project's architecture and the mathematical structure. Medium confidence on the future abstraction potential (Task 41 analog for decidability) — this depends on what patterns actually emerge from the concrete implementations, which don't exist yet for propositional/modal in cslib. The executable decision procedure opportunity is high-confidence (it's already working in BimodalLogic), but the tactic integration would require new development beyond Task 9's scope.
