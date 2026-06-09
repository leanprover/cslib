# Teammate B Findings: Alternative Approaches and Prior Art

**Task**: 9 — Port Decidability and Tableau to Bimodal module
**Date**: 2026-06-09
**Angle**: Alternative patterns, prior art, and composition strategies

## Key Findings

1. **Prior art in Lean 4 is limited but growing**: The most relevant project is `m4lvin/lean4-pdl` (Tableaux for Propositional Dynamic Logic in Lean 4, WIP), which includes a ported basic modal logic tableau from Lean 3. The `FormalizedFormalLogic/Foundation` project formalizes Kripke completeness for modal logics but uses Henkin-style canonical model constructions rather than tableau methods. No existing Lean 4 library formalizes a tableau-based decision procedure for temporal or bimodal logics.

2. **Coq and Isabelle have mature formalizations**: In Coq, Doczkal & Smolka (ITP 2019) formalized verified decision procedures for K, KT, and S4 using histories-based tableaux with soundness and completeness. In Isabelle/HOL, Goré & Postniece formalized ALC description logic tableaux. The Coq work is the closest analogue — it returns either a Kripke model (satisfiable) or a proof tree (unsatisfiable), achieving a certified decision function.

3. **The existing embedding infrastructure strongly supports a top-down composition strategy**: The embeddings (`ModalEmbedding.lean`, `TemporalEmbedding.lean`, `PropositionalEmbedding.lean`) are structural injections that commute (the diamond commutes). This means decidability for Bimodal can theoretically be transferred to Modal and Temporal via these embeddings — if the fragment is decidable in Bimodal, it's decidable in the sub-logics.

4. **A generic typeclass-based tableau framework is architecturally possible but premature**: The `Connectives.lean` hierarchy (`PropositionalConnectives → ModalConnectives → TemporalConnectives → BimodalConnectives`) provides the right foundation, but the tableau rules are deeply logic-specific (28 rules for Bimodal involving interaction between □ and U/S). Abstracting these into a generic framework would require a `TableauRule` typeclass with termination measures, which is significant engineering with unclear payoff before at least 2 concrete instances exist.

5. **Well-founded termination is feasible via subformula complexity**: Lean 4's `termination_by` with a `Nat`-valued measure (subformula count + modal/temporal depth) is the standard approach. The existing `Formula.complexity` and `Formula.temporalDepth` functions in `Temporal/Syntax/Formula.lean` provide the template. For tableau expansion, a combined measure of (number of unexpanded formulas, subformula complexity) provides well-founded recursion. Fuel-based approaches (`Option` return) are simpler to implement but lose totality — the verified decision procedure should be total.

6. **Sequent calculus cut-elimination is a viable alternative for Propositional, but not for the temporal fragment**: Cut-elimination gives decidability for propositional and basic modal logics but does not straightforwardly handle temporal operators (Until/Since require specialized fixpoint arguments). Tableau methods are the standard approach for temporal logics in the literature (Burgess, Reynolds) and align with what the BimodalLogic source repository uses.

7. **The coalgebraic approach (generic decidability via functors) is theoretically elegant but impractical here**: The coalgebraic μ-calculus framework provides EXPTIME decidability for a wide class of modal fixpoint logics, but formalizing the functor/coalgebra infrastructure in Lean 4 is a multi-year project. It does not match the concrete BimodalLogic source being ported.

## Recommended Approach

**Hybrid bottom-up strategy with embedding-based transfer for sub-logics**.

Build concrete tableau + decidability for each logic in order of complexity, then use embeddings to derive results where possible:

### Phase 1: Propositional Decidability (standalone, ~200 lines)
- Truth-table evaluation → `Decidable (Satisfies v φ)` for propositional logic
- No tableau needed — `DecidableEq` + structural recursion suffices
- This is a warm-up that establishes the `instance : Decidable` pattern

### Phase 2: Bimodal Tableau (port from BimodalLogic, ~10k lines)
- Port the full tableau infrastructure as described in the task
- This is the core deliverable and matches the source repository
- SignedFormula → Tableau (28 rules) → Closure → Saturation → Correctness → DecisionProcedure → CountermodelExtraction → FMP

### Phase 3: Modal Decidability via Embedding (~300 lines, new)
- Given: `Decidable (Bimodal.Satisfies ...)` from Phase 2
- The embedding `Modal.Proposition.toBimodal` is injective and preserves satisfaction
- Transfer theorem: if `toBimodal φ` is decidable in Bimodal, then `φ` is decidable in Modal
- This avoids duplicating the entire tableau for the modal fragment

### Phase 4: Temporal Decidability via Embedding (~300 lines, new)
- Same pattern as Phase 3 using `Temporal.Formula.toBimodal`
- Temporal formulas embed into the temporal fragment of Bimodal

### Phase 5 (Optional): Abstract Generic Tableau
- Only after Phases 2-4 are complete
- Extract shared patterns into `Foundations/Logic/Metalogic/Tableau.lean`
- Candidate abstractions: `SignedFormula` type, `TableauBranch`, `Closure` conditions

### Why not top-down only?

The Bimodal tableau has 28 expansion rules that cover all connectives. The modal and temporal fragments each use only a subset. A standalone modal tableau would need only ~8 rules and be simpler to prove termination for. However, since the source code already has the full Bimodal tableau, porting it first and then transferring to sub-logics is more efficient than building 3 separate tableaux.

### Why not generic framework first?

The `DerivationSystem` + `HasDeductionTheorem` pattern in `Foundations/Logic/Metalogic/Consistency.lean` is the right model: build generic infrastructure after seeing 2+ concrete instances. The existing generic MCS framework was built after Modal and Temporal MCS proofs existed. Tableau abstraction should follow the same pattern.

## Evidence/Examples

### Embedding Transfer Pattern (Modal case)

```lean
-- Sketch: transfer decidability via embedding
theorem modal_decidable_of_bimodal_decidable
    [inst : DecidablePred (Bimodal.Satisfies m w)]
    (φ : Modal.Proposition Atom) :
    Decidable (Modal.Satisfies m' w' φ) := by
  -- Use the embedding preservation theorem
  -- Modal.Satisfies m w φ ↔ Bimodal.Satisfies (liftModel m) w (φ.toBimodal)
  -- Apply inst to the right-hand side
  sorry -- actual proof requires model lifting
```

### Comparison: Alternative Architectures

| Approach | Effort | Composability | Proof Complexity | Matches Source? |
|----------|--------|---------------|------------------|-----------------|
| **Port Bimodal + Transfer** | Medium-High | High (embeddings) | Medium (transfer thms) | Yes |
| **3 Separate Tableaux** | Very High | Low (no sharing) | High (3× termination) | No |
| **Generic Framework First** | Very High | Very High | Very High (abstract proofs) | No |
| **Coalgebraic** | Extreme | Extreme | Extreme | No |
| **Sequent Calculus** | Medium | Low | Medium (but no temporal) | No |

### Prior Art Reference Summary

| Project | Prover | Logics | Approach | Status |
|---------|--------|--------|----------|--------|
| Doczkal & Smolka (ITP 2019) | Coq/SSReflect | K, KT, S4 | Histories-based tableau | Complete |
| lean4-pdl (Gattinger) | Lean 4 | PDL + BML | Tableau | WIP |
| FormalizedFormalLogic | Lean 4 | Modal, FO | Henkin/canonical model | Active |
| Goré & Postniece | Isabelle/HOL | ALC (DL) | Semantic tableau | Complete |
| cslib (this project) | Lean 4 | S5, Temporal, Bimodal | Canonical model (MCS) | Active (completeness done) |

### Termination Measure Pattern

```lean
-- From existing Temporal.Formula.complexity (lines 308-334)
-- Bimodal version would be analogous with additional box case
def Bimodal.Formula.tableauWeight : Formula Atom → Nat
  | .atom _ => 1
  | .bot => 1
  | .imp φ ψ => 1 + tableauWeight φ + tableauWeight ψ
  | .box φ => 2 + tableauWeight φ   -- box needs extra weight for modal expansion
  | .untl φ ψ => 3 + tableauWeight φ + tableauWeight ψ  -- temporal needs more
  | .snce φ ψ => 3 + tableauWeight φ + tableauWeight ψ

-- Tableau expansion terminates because each rule strictly decreases
-- the multiset of unsigned formula weights on the branch
```

### Codebase Pattern: Generic → Concrete Instantiation

The project already follows the "generic framework, concrete instantiation" pattern:

```
Foundations/Logic/Metalogic/Consistency.lean   -- Generic DerivationSystem, Lindenbaum
  ├── Modal/Metalogic/MCS.lean                -- modalDerivationSystem instance
  ├── Temporal/Metalogic/MCS.lean             -- temporalDerivationSystem instance
  └── Bimodal/Metalogic/Core/MCSProperties.lean -- bimodal fc-parameterized instance
```

The same pattern should apply to tableau infrastructure once built:

```
Foundations/Logic/Metalogic/Tableau.lean (Phase 5, optional)
  ├── Bimodal/Metalogic/Decidability/Tableau.lean (Phase 2)
  └── [Modal/Temporal derived via embeddings, Phases 3-4]
```

## Confidence Level

**Medium-High**

- **High confidence** on the embedding-based transfer strategy: the embeddings are already well-structured with commutativity proofs, and the pattern is standard in formal logic.
- **High confidence** on prior art assessment: the landscape is well-surveyed and no existing Lean 4 project provides a reusable tableau framework.
- **Medium confidence** on the generic framework timing: Task 41 (Abstract shared completeness infrastructure) already plans to do this for completeness. Doing it simultaneously for tableau may be premature. Wait until Phase 2 is complete.
- **Lower confidence** on the effort estimates for transfer theorems (Phases 3-4): the model lifting required to connect `Modal.Satisfies` to `Bimodal.Satisfies` via the embedding may be non-trivial, depending on how the canonical models relate. This needs further investigation during planning.
