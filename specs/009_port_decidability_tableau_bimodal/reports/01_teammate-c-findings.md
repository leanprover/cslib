# Teammate C: Critic Findings — Tableau & Decidability Infrastructure

**Task**: 9 (Port Decidability and Tableau to Bimodal module)
**Date**: 2026-06-09
**Angle**: Gaps, blind spots, and unvalidated assumptions

---

## Key Findings

### 1. Task 9 Is ONLY About Bimodal — The "4 Logics" Scope Is Ungrounded

The focus prompt asks about "Propositional/, Modal/, Temporal/, and Bimodal/" but Task 9's description exclusively concerns porting the *existing* BimodalLogic decidability code to `Cslib/Logics/Bimodal/Metalogic/Decidability/`. There is **no source code** for Propositional, Modal, or Temporal tableau procedures in the BimodalLogic repository or in cslib. Building new decidability procedures for these 3 logics from scratch is an entirely different scope category — likely 3 additional tasks of Medium-to-Large size each.

**Risk**: Conflating "study how to compose tableau across 4 logics" with "port existing bimodal code" will produce analysis that doesn't match the actual work to be done.

### 2. No Source Repository Accessible — Porting Difficulty Unknown

The BimodalLogic repository (`Theories/Bimodal/Metalogic/Decidability/`) is referenced in the task description but does NOT exist in the cslib working tree. There are no `Tableau.lean`, `SignedFormula.lean`, `Closure.lean`, `DecisionProcedure.lean`, `CountermodelExtraction.lean`, `ProofExtraction.lean`, or `FMP/` files anywhere in the project. The 10,000-line estimate is from the task description, unverifiable without the source.

**Implication**: All porting difficulty estimates are speculative. Prior tasks (Task 7: ~2,500 lines estimated, 1,112 lines actually ported) suggest the estimates may be inflated, but equally, the tableau code may be more tightly coupled than MCS theory and resist reduction.

### 3. Temporal Completeness Has a `sorry` — Decidability May Depend On It

`Cslib/Logics/Temporal/Metalogic/Completeness.lean:416` contains an unresolved `sorry` in the main completeness theorem. The sorry blocks the ℤ-indexed MCS chain construction (the truth lemma for Until/Since on linear orders).

**Critical question**: Does the Bimodal decidability procedure depend on completeness? Inspection of the Bimodal `Completeness.lean` (478 lines) reveals it is actually "MCS Completeness Properties" — helper lemmas for MCS (conjunction/disjunction/diamond-box duality), NOT a full completeness theorem. The actual completeness theorem for Bimodal doesn't exist yet in cslib. If decidability depends on completeness (e.g., via FMP ↔ completeness interaction), this is a blocking dependency NOT listed in the task.

### 4. Compositionality Assumptions Are Largely Unsupported by Code Structure

The existing codebase provides **zero** shared tableau infrastructure:

- **Formula types are completely independent**: `PL.Proposition` (3 constructors), `Modal.Proposition` (4), `Temporal.Formula` (5), `Bimodal.Formula` (6). These are separate inductive types, not instances of a parametric type.
- **Connective typeclasses** (`Connectives.lean`) provide notation sharing, not proof sharing. You can't write a generic tableau expansion rule over `HasImp F`.
- **MCS infrastructure** is partly generic (`Foundations/Logic/Metalogic/Consistency.lean`) but each logic has its own DeductionTheorem (per roadmap design decision #1). This pattern would repeat for decidability — each logic needs its own termination proof.
- **Embeddings exist** (`ModalEmbedding.lean`, `TemporalEmbedding.lean`) but these are structural injections, not proof-lifting mechanisms. You can embed a Modal formula into Bimodal, but you cannot automatically lift a "Modal tableau is terminating" proof to "Bimodal tableau is terminating."

**Realistic composition opportunities**:
- `SignedFormula` type could potentially be generic over any formula type with `HasBot`/`HasImp` (signed = formula paired with polarity)
- `Subformula` infrastructure: `Temporal.Formula.subformulas` exists (Subformulas.lean:46); analogous definitions needed per logic
- Closure/saturation *definitions* could share a signature via a typeclass, but the proofs won't compose

### 5. Propositional Decidability Is Trivially Different — Not a Tableau Problem

Propositional logic (`PL.Proposition`) has only 3 constructors (`atom`, `bot`, `imp`). Its decidability is a trivial induction on formula structure, or truth-table evaluation, or DPLL. A tableau approach is overkill and misleading. The propositional logic in cslib has a natural deduction system (`NaturalDeduction/Basic.lean`), not a Hilbert system, so it doesn't even have the same metalogic infrastructure pattern.

### 6. Modal Decidability Needs Its Own Completeness First

`Modal/Metalogic/Completeness.lean` (547 lines, zero sorry) proves completeness for S5. But decidability for modal logic typically goes through:
- Finite model property (FMP) for the modal logic in question
- Filtration or selective filtration technique
- Bounded model size argument

None of this exists yet. The S5 completeness provides the starting canonical model, but FMP is an additional major theorem. The modal completeness proof uses an infinite canonical model (MCS-indexed worlds) — decidability requires showing a finite model suffices.

### 7. Bimodal Tableau Has 28 Rules — Termination Is the Hard Part

The task description mentions 28 expansion rules for the bimodal tableau. Proving well-founded termination of a tableau with 28 rules in Lean 4 is extremely labor-intensive:
- Each rule must decrease some well-founded measure
- The measure must handle all 28 cases simultaneously
- Lean 4's well-founded recursion elaborator is notoriously slow for large mutual/nested recursions
- `maxHeartbeats` is already at 3,200,000 for Temporal Completeness (418 lines) — a 1,800-line Tableau.lean could require astronomical heartbeats or `partial` workarounds

### 8. The "Port" vs "Build Fresh" Question Is Unresolved

The roadmap says "every component lives at the most general level it can compile at." But the BimodalLogic source was a monolithic bimodal development — there was no propositional-level or modal-level factoring of the tableau procedure. Porting it as-is creates bimodal-only decidability. The focus prompt's emphasis on composition suggests the user wants factored decidability — but that would mean **redesigning** the BimodalLogic tableau, not porting it.

### 9. Dependencies: Task 4 Status Is Unclear

Task 4 (ProofSystem) is listed as a dependency but doesn't appear in `state.json`'s active projects (it was likely archived). The Bimodal ProofSystem files exist (1,507 lines total across 6 files), so this dependency appears satisfied. However, task 7's completion summary notes "RestrictedMCS deferred to completeness task" — this deferred work may be needed for decidability (restricted MCS is used in frame-specific completeness, which connects to FMP).

### 10. Cost Multiplier for 4-Logic Coverage Is ~5-8x, Not 4x

Assuming the bimodal port is the baseline (~10k lines), adding Propositional, Modal, and Temporal decidability requires:
- **Propositional**: ~500 lines (trivial, truth-table or simple tableau)
- **Modal (K or S5)**: ~3,000-4,000 lines (FMP, filtration, bounded model)
- **Temporal (BX)**: ~4,000-6,000 lines (FMP for linear temporal logic is technically demanding — Fischer-Ladner closure, quotienting, Ramsey-like arguments)
- **Shared infrastructure**: ~500-1,000 lines (SignedFormula generic, subformula closure)

Total: ~18,000-21,500 lines. That's roughly **2x** the bimodal port alone. However, the bimodal port is "just" porting, while Propositional/Modal/Temporal would be **new development** (no source to port from), making the actual effort **5-8x** in time.

---

## Recommended Approach

1. **Decouple Task 9 from the 4-logic composition question**. Task 9 should remain: "port the existing BimodalLogic decidability code to cslib." The multi-logic decidability study should be a separate research task.

2. **Resolve the Temporal Completeness sorry first** (or determine whether decidability depends on it). If the bimodal completeness theorem isn't needed for decidability, document this explicitly.

3. **Identify the minimal generic infrastructure** before porting:
   - Generic `SignedFormula` type (over any `F` with `DecidableEq`)
   - Generic `Closure` definition (subformula closure with logic-specific extensions)
   - These are ~200-400 lines and could live in `Foundations/`

4. **Port the bimodal tableau as-is first**, then factor generic components OUT of it later. This follows the project's successful pattern (MCS was first per-logic, then 60% factored to Foundations).

5. **Create separate tasks** for Modal FMP, Temporal FMP, and Propositional decidability if desired. Each has distinct techniques and should be tracked independently.

---

## Evidence/Examples

| Finding | Evidence |
|---------|----------|
| No source files | `find . -name "Tableau*" -o -name "SignedFormula*"` returns zero results in `Cslib/Logics/` |
| Formula independence | `Cslib/Logics/*/Syntax/Formula.lean` — each is an independent `inductive` |
| MCS per-logic pattern | Roadmap design decision #1 and #5: "DeductionTheorem stays per-logic", "No generic metalogic typeclass" |
| Temporal sorry | `Cslib/Logics/Temporal/Metalogic/Completeness.lean:416` |
| Bimodal Completeness is partial | File header: "MCS Completeness Properties" — helper lemmas, not the main theorem |
| heartbeat pressure | `set_option maxHeartbeats 3200000` in `Temporal/Metalogic/Completeness.lean:49` |
| Existing subformula infra | `Temporal/Syntax/Subformulas.lean` defines `subformulas` and `subformulaCount` |
| Embedding ≠ proof lifting | `Bimodal/Embedding/ModalEmbedding.lean` — structural map only, no derivation transfer |
| Task 7 deferred work | Completion summary: "RestrictedMCS deferred to completeness task" |

---

## Confidence Level

**High** — These findings are based on direct codebase inspection (file existence, line counts, sorry counts, formula types, import graphs) rather than speculation. The scope feasibility concerns (#1, #2, #10) are arithmetic. The dependency concerns (#3, #6, #9) are verifiable from state.json and grep. The compositionality analysis (#4, #8) is grounded in the actual type definitions and the project's own roadmap design decisions.

The one medium-confidence finding is #7 (heartbeat/termination difficulty) — this is based on general Lean 4 experience rather than having seen the actual BimodalLogic tableau code, which is not available in this repo.
