# Research Report: Task #9

**Task**: Port Decidability and Tableau to Bimodal module
**Date**: 2026-06-09
**Mode**: Team Research (4 teammates)

## Summary

Four research teammates investigated tableau and decidability infrastructure across Propositional, Modal, Temporal, and Bimodal logics in cslib. Strong consensus emerged: **port the existing bimodal tableau as-is first** (~10k lines from BimodalLogic), then build simpler decidability results (propositional, modal, temporal) as separate tasks afterward. Compositionality across the 4 logics is structurally limited — the 28 bimodal expansion rules are inherently combined and cannot factor into separate modal/temporal components. The project's own "build concrete, then abstract" pattern (demonstrated by the generic MCS framework in Foundations) should guide decidability infrastructure: no premature generic `TableauSystem` typeclass.

## Key Findings

### Primary Approach (from Teammate A)

1. **The four formula types are independent inductives linked by embedding maps** — no shared datatype exists. `PL.Proposition` (3 constructors), `Modal.Proposition` (4), `Temporal.Formula` (5), `Bimodal.Formula` (6). A generic tableau framework would need to abstract over the formula type via typeclasses.

2. **The existing `DerivationSystem`/MCS pattern in Foundations already shows the right abstraction level**: a thin typeclass layer with generic results (Lindenbaum's lemma, SetConsistent, SetMaximalConsistent), instantiated per-logic. Tableau should follow the same pattern.

3. **Each logic's tableau termination argument is fundamentally different**:
   - Propositional: subformula property (trivial)
   - Modal: Fischer-Ladner closure (finite subformula set)
   - Temporal: Fischer-Ladner closure + eventuality fulfillment
   - Bimodal: 28 rules with cross-modal interaction

4. **Recommended directory structure** (consistent across all logics):
   ```
   {Logic}/Metalogic/Decidability/
   ├── SignedFormula.lean
   ├── Tableau.lean
   ├── Closure.lean
   ├── Saturation.lean
   ├── ProofExtraction.lean
   ├── CountermodelExtraction.lean
   ├── Correctness.lean
   └── DecisionProcedure.lean
   ```

5. **Existing DerivationTree pattern is remarkably uniform** across logics (5 constructors for Modal, 7 for Bimodal), so ProofExtraction will follow a consistent pattern.

### Alternative Approaches (from Teammate B)

1. **Prior art in Lean 4 is limited**: The most relevant project is `m4lvin/lean4-pdl` (WIP tableau for PDL). In Coq, Doczkal & Smolka (ITP 2019) formalized verified decision procedures for K/KT/S4 using histories-based tableaux. No existing Lean 4 library formalizes tableau-based decidability for temporal or bimodal logics.

2. **Embedding-based transfer is theoretically viable**: The existing embeddings (`ModalEmbedding.lean`, `TemporalEmbedding.lean`) are structural injections with commutativity proofs. In principle, decidability for Bimodal can transfer to Modal and Temporal via these embeddings — avoiding the need to build 3 separate tableaux.

3. **Well-founded termination via subformula complexity is feasible**: `Formula.complexity` and `Formula.temporalDepth` functions already exist in `Temporal/Syntax/Formula.lean` as templates. For tableau expansion, a combined measure of (unexpanded formulas count, subformula complexity) provides well-founded recursion.

4. **Sequent calculus cut-elimination works for propositional/modal but not temporal**: Temporal operators require specialized fixpoint arguments, so tableau is the right approach for the temporal fragment.

5. **Comparison of architectures**:

   | Approach | Effort | Composability | Proof Complexity | Matches Source? |
   |----------|--------|---------------|------------------|-----------------|
   | Port Bimodal + Transfer | Medium-High | High | Medium | Yes |
   | 3 Separate Tableaux | Very High | Low | High (3× termination) | No |
   | Generic Framework First | Very High | Very High | Very High | No |
   | Coalgebraic | Extreme | Extreme | Extreme | No |

### Gaps and Shortcomings (from Critic)

1. **Task 9 is ONLY about bimodal — the 4-logic scope is ungrounded.** The task description exclusively concerns porting BimodalLogic decidability code. Building new decidability for Propositional, Modal, and Temporal from scratch is separate work (3 additional Medium-to-Large tasks).

2. **No source repository accessible in the working tree.** The BimodalLogic source (`Theories/Bimodal/Metalogic/Decidability/`) is not present. All porting estimates are based on the task description, not verified source. Prior tasks suggest estimates may be inflated (Task 7: ~2,500 lines estimated, ~1,112 actually ported).

3. **Temporal completeness has a blocking `sorry`** at `Temporal/Metalogic/Completeness.lean:416` (ℤ-indexed MCS chain construction). If decidability depends on completeness, this is a hidden dependency.

4. **Bimodal `Completeness.lean` is "MCS Completeness Properties" — helper lemmas, not the full completeness theorem.** The actual bimodal completeness theorem doesn't exist yet in cslib. Whether decidability depends on completeness is a critical open question.

5. **Compositionality assumptions are largely unsupported by code structure.** Connective typeclasses provide notation sharing, not proof sharing. Embeddings are structural injections, not proof-lifting mechanisms. Each logic needs its own termination proof.

6. **Propositional decidability is trivially different** — truth-table evaluation or simple induction suffices (~200 lines). A tableau approach is overkill for 3-constructor formulas.

7. **Modal decidability needs FMP, which doesn't exist yet.** The S5 completeness uses an infinite canonical model. Decidability requires showing a finite model suffices (filtration/selective filtration).

8. **Heartbeat pressure is a real risk.** `maxHeartbeats` is already at 3,200,000 for Temporal Completeness (418 lines). The 1,800-line Tableau.lean with 28 rules could require enormous heartbeats or `partial` workarounds.

9. **Cost multiplier for 4-logic coverage is ~2x in lines but ~5-8x in effort.** The bimodal port is "just" porting; Propositional/Modal/Temporal would be new development (no source to port from).

10. **The "port vs redesign" question is unresolved.** The BimodalLogic source was monolithic. Porting as-is creates bimodal-only decidability. Factored decidability would mean redesigning, not porting.

### Strategic Horizons (from Horizons)

1. **The bimodal tableau is inherently non-compositional.** The 28 rules operate on all 6 formula constructors with modal-temporal interaction. This makes factoring into separate components impossible — it's a fundamentally combined result.

2. **The roadmap reveals a "vertical depth" strategy.** The project proceeds bottom-up (Prop → Modal+Temporal → Metalogic → Bimodal) and decidability is at Wave 5. The project is committed to depth-first on this logic family.

3. **Task 41 (shared completeness infrastructure) is the key analog.** It aims to abstract shared patterns after concrete implementations exist. The same principle should govern any future generic tableau framework.

4. **Decidability enables executable decision procedures — a potential "killer feature."** Unlike completeness, decidability gives a computable `decide` function. In Lean 4: `#eval decide (ThDerivable (.box (.imp p q)))`. This would be **unique in the Lean ecosystem** — no other project has formalized bimodal decidability.

5. **The FMP split (9a/9b) is strategically sound.** Core tableau/decision procedure (~5k lines) delivers the `Decidable` instance faster; FMP (~4k lines) strengthens to finite countermodels and can follow as a separate task.

6. **Future logic extensions should NOT drive current architecture.** CTL/CTL*, μ-calculus, PDL, description logics all require fundamentally different tableau strategies. Designing for all of these now would be premature.

7. **Import hierarchy is clean — Task 9 is unblocked:**
   ```
   Foundations/Metalogic/Consistency.lean  (Task 29 ✓)
       ↓
   Bimodal/Metalogic/Core/              (Task 7 ✓)
       ↓
   Bimodal/Metalogic/Decidability/      ← Task 9 starts here
   ```

## Synthesis

### Conflicts Resolved

1. **Build order (Bottom-up vs Bimodal-first)**: Teammates A recommended Prop→Modal→Temporal→Bimodal; Teammates B, C, D recommended bimodal first. **Resolution: Bimodal first.** The source code exists for bimodal (~10k lines to port); no source exists for the simpler logics. Port what's available, then build the rest. Bottom-up is pedagogically nice but practically wrong for this project — you'd write new code for simple logics before porting available code for the complex one.

2. **Scope: Task 9 vs multi-logic decidability**: Critic strongly argues Task 9 is bimodal-only; others want multi-logic strategy. **Resolution: Task 9 focuses on bimodal port. This research informs the multi-logic strategy, but Propositional/Modal/Temporal decidability should be separate tasks.** The research focus prompt broadens the investigation appropriately, but the implementation scope stays bimodal.

3. **Embedding-based transfer feasibility**: Teammate B advocates strongly; Critic is skeptical. **Resolution: Transfer via embeddings is theoretically sound but uncertain in practice.** The embeddings preserve satisfiability, but lifting decidability requires model-lifting theorems that don't exist yet. Worth investigating during planning as a Phase 3 strategy, not a dependency for Task 9.

4. **Propositional decidability approach**: Teammate A suggests tableau (~800 lines); Teammates B, C, D say truth-table (~200 lines). **Resolution: Use truth-table/semantic evaluation for propositional decidability.** A propositional tableau is unnecessarily complex for 3-constructor formulas. This is a separate, small task.

### Gaps Identified

1. **BimodalLogic source not accessible in repo** — porting estimates are unverifiable without it. The actual source needs to be made available before implementation planning.

2. **Bimodal completeness theorem is incomplete** — only MCS helper lemmas exist. Whether decidability depends on the full completeness theorem needs explicit determination.

3. **Temporal completeness has a sorry** — blocks temporal-specific decidability (not bimodal directly, but relevant for the multi-logic goal).

4. **Modal FMP infrastructure doesn't exist** — needed for standalone modal decidability (not blocking Task 9).

5. **Heartbeat/performance risk** — 28-rule tableau with termination proofs may stress Lean 4's elaborator. `maxHeartbeats` already at 3.2M for simpler files.

### Recommendations

**For Task 9 (immediate)**:
1. Port the bimodal tableau as-is from BimodalLogic, maintaining the existing file structure
2. Split into 9a (core tableau + decision procedure, ~5k lines) and 9b (FMP, ~4k lines)
3. Determine explicitly whether decidability depends on the full completeness theorem
4. Introduce a thin generic `SignedFormula` type in Foundations (~200 lines) that bimodal instantiates
5. Expect heartbeat pressure on Tableau.lean — plan for `maxHeartbeats` overrides and possible file splitting

**For multi-logic decidability (future tasks)**:
6. Create separate tasks for: Propositional decidability (truth-table, ~200 lines), Modal decidability (K/S5, ~1-3k lines new), Temporal decidability (needs sorry resolution first)
7. Investigate embedding-based transfer (Bimodal → Modal, Bimodal → Temporal) during modal/temporal planning
8. Defer generic `TableauSystem` framework until 2+ concrete implementations exist (aligned with Task 41 pattern)
9. Do NOT design current infrastructure to accommodate future logics (CTL*, μ-calculus, etc.)

**Reusability estimate**: ~20-30% of decidability infrastructure can eventually be shared across logics (SignedFormula, correctness theorem structure, closure/saturation concepts). Much less than the ~40% sharing achieved for MCS theory, because tableau rules and termination arguments are more logic-specific.

## Teammate Contributions

| Teammate | Angle | Status | Confidence |
|----------|-------|--------|------------|
| A | Primary approach, architecture, file organization | completed | medium-high |
| B | Alternative approaches, prior art, embedding transfer | completed | medium-high |
| C | Critic: scope, feasibility, dependencies, blind spots | completed | high |
| D | Strategic horizons, roadmap alignment, future direction | completed | medium-high |

## References

- Doczkal & Smolka (ITP 2019): Verified decision procedures for K, KT, S4 in Coq
- `m4lvin/lean4-pdl`: WIP tableau for PDL in Lean 4
- `FormalizedFormalLogic/Foundation`: Lean 4 Kripke completeness (Henkin-style, not tableau)
- cslib `Foundations/Logic/Metalogic/Consistency.lean`: Generic MCS framework (pattern template)
- cslib `Bimodal/Embedding/*.lean`: Structural embeddings (composition opportunity)
- cslib Roadmap Key Design Decision #5: "No generic metalogic typeclass" (premature abstraction warning)
