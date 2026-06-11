# Teammate D Findings: Strategic Horizons

**Task**: 99 — Complete modal cube Hilbert proof systems
**Angle**: Long-term alignment, strategic direction, task decomposition
**Date**: 2026-06-11

## Key Findings

### 1. Project Context and Strategic Alignment

CSLib is a Lean 4 library formalizing Computer Science broadly. The ROADMAP shows this project is porting BimodalLogic content into CSLib's modular architecture. The modal cube work directly enables:

- **Bimodal completeness variants** (Remaining items: discrete/continuous completeness rely on the modal infrastructure being complete)
- **Embedding verifications** — `ModalEmbedding.lean` embeds modal into bimodal; completeness of individual modal systems validates these embeddings
- **Conservative extension results** — already proven for the bimodal BX system; each modal subsystem's completeness contributes a sub-result

The modal cube completion is NOT peripheral — it is the canonical reference library that the more complex temporal and bimodal results build upon.

### 2. What Tasks 92-98 Accomplished (Prior Art)

The previous wave (tasks 92-98) established:
- **Task 92**: Parameterized `DerivationTree` over axiom predicates; added bundled typeclasses (`ModalTHilbert`, `ModalDHilbert`, `ModalS4Hilbert`) and tag types
- **Task 93**: Created `Instances.lean` with 5 axiom predicates (KAxiom, TAxiom, DAxiom, S4Axiom, ModalAxiom=S5) and full instance registrations
- **Task 94**: Integrated orphaned HilbertDerivedRules into module graph
- **Tasks 95-97**: Established soundness + completeness for K, T, D, S4 (each ~90-450 lines)
- **Task 98**: Final integration

**Key architectural decisions already made:**
- Separate inductive axiom predicates per system (NOT a parameterized selector)
- Shared `DerivationTree`, `DeductionTheorem`, `MCS` parameterized over `Axioms`
- Soundness uses `h_ax_sound` callback pattern (composable)
- Per-system soundness/completeness in dedicated files

### 3. What the Remaining 10 Logics Require

The infrastructure is fully in place. Each new system needs:
1. An axiom predicate (inductive type in `Instances.lean` or separate file)
2. Tag type + typeclass instances  
3. Soundness theorem (via `h_ax_sound` callback)
4. Completeness theorem (canonical model with frame properties)

**Critical insight**: The existing `HasAxiom5` typeclass and `Axioms.Axiom5` schema are ALREADY defined in `ProofSystem.lean` and `Axioms.lean` respectively. All semantic validity lemmas (`Satisfies.five`, `Satisfies.b`, `Satisfies.d`, `Satisfies.four`, `Satisfies.t`) already exist. The work is primarily connecting these existing pieces.

### 4. Recommended Task Decomposition (Wave Structure)

**Wave 0 — Infrastructure Extension** (1 task):
- Add new bundled typeclasses for intermediate systems: `ModalBHilbert` (K+B), `ModalK4Hilbert` (K+4), `ModalK5Hilbert` (K+5), and compound systems
- Add corresponding tag types
- This is a SMALL task but unblocks everything else

**Wave 1 — Single-axiom systems** (3 tasks, parallelizable):
- **KB (= "B" in Cube.lean)**: K + axiom B. Frame: symmetric. Completeness: canonical symmetry.
- **K4 (= "Four" in Cube.lean)**: K + axiom 4. Frame: transitive. Completeness: canonical transitivity (already proven for S4, just drop T).
- **K5 (= "Five" in Cube.lean)**: K + axiom 5. Frame: Euclidean. Completeness: canonical Euclidean property.

**Wave 2 — Two-axiom compounds** (4 tasks, parallelizable):
- **KB5**: K + B + 5. Frame: symmetric + Euclidean (= equivalence relation minus reflexivity).
- **K45**: K + 4 + 5. Frame: transitive + Euclidean.
- **D4**: K + D + 4. Frame: serial + transitive. Reuses D seriality proof + S4 transitivity proof.
- **D5**: K + D + 5. Frame: serial + Euclidean.

**Wave 3 — Three-axiom compounds** (2 tasks, parallelizable):
- **TB (= "KTB" = standard B logic)**: K + T + B. Frame: reflexive + symmetric (= equivalence minus transitivity).
- **D45**: K + D + 4 + 5. Frame: serial + transitive + Euclidean.
- **DB**: K + D + B. Frame: serial + symmetric.

**Why this ordering?**:
- Wave 1 logics introduce single new frame properties whose canonical proofs are independent
- Wave 2 logics COMPOSE proofs from Wave 1 (e.g., K45 = K4 transitivity proof + K5 Euclidean proof)
- Wave 3 logics compose even further
- Within each wave, tasks are fully parallel

### 5. Mathematical Dependencies (Frame Property Proof Reuse)

The key reusable lemmas needed:
- `canonical_refl` (from T completeness) — for T-containing systems
- `canonical_trans` (from S4 completeness) — for 4-containing systems
- `canonical_serial` (from D completeness) — for D-containing systems
- `canonical_symm` (NEW for B) — for B-containing systems
- `canonical_eucl` (from S5 completeness) — for 5-containing systems

Once Wave 1 establishes `canonical_symm` (B) and independently confirms `canonical_trans` works standalone (K4) and `canonical_eucl` works standalone (K5), ALL compound systems are pure compositions.

### 6. Typeclass Hierarchy Considerations

The current hierarchy is:
```
ModalHilbert (K)
  ├── ModalTHilbert (K+T)
  │     └── ModalS4Hilbert (K+T+4)
  │           └── ModalS5Hilbert (K+T+4+B)
  └── ModalDHilbert (K+D)
```

For 15 systems, we should NOT create a deep diamond hierarchy. Instead, use flat individual axiom typeclasses:
```
[ModalHilbert S] + [HasAxiomB S] — for KB
[ModalHilbert S] + [HasAxiom4 S] — for K4
[ModalHilbert S] + [HasAxiom5 S] — for K5
[ModalDHilbert S] + [HasAxiom4 S] — for D4
```

This uses the EXISTING `HasAxiom*` typeclasses compositionally without needing 10 new bundled classes. The bundled classes (ModalTHilbert, etc.) already exist for the 5 core systems. For compound systems, CONSTRAINT INSTANCES suffice.

Alternatively, add minimal bundled classes only where the Cube.lean definitions warrant them (e.g., `ModalK45Hilbert`, `ModalTBHilbert`). But this adds boilerplate without clear benefit.

**Recommendation**: Use constraint-based instances for compound systems (no new bundled classes). The Instances.lean file registers the appropriate HasAxiom* instances for each tag type, and soundness/completeness theorems state their conditions directly.

### 7. Naming and Organization

Current pattern: `{Logic}Soundness.lean`, `{Logic}Completeness.lean` directly in `Metalogic/`.

With 10 new systems (20 new files), this gets crowded. Consider:
- `Metalogic/Soundness/` subdirectory with `K.lean`, `T.lean`, `B.lean`, `K4.lean`, `K45.lean`, etc.
- `Metalogic/Completeness/` subdirectory similarly

**However**: The existing files use flat naming (`KSoundness.lean`, `TSoundness.lean`). Refactoring the existing 10 files is churn that could introduce import issues. 

**Recommendation**: Continue flat naming for consistency with existing work. The file count (24 metalogic files) is manageable. If it becomes unwieldy later, a restructuring task can group them.

Naming for new files:
- `BSoundness.lean`, `BCompleteness.lean` (for logic "B" = KB)
- `K4Soundness.lean`, `K4Completeness.lean` (for logic "Four" = K4)
- `K5Soundness.lean`, `K5Completeness.lean` (for logic "Five" = K5)
- `K45Soundness.lean`, `K45Completeness.lean`
- `D4Soundness.lean`, `D4Completeness.lean`
- `D5Soundness.lean`, `D5Completeness.lean`
- `D45Soundness.lean`, `D45Completeness.lean`
- `DBSoundness.lean`, `DBCompleteness.lean`
- `TBSoundness.lean`, `TBCompleteness.lean`
- `KB5Soundness.lean`, `KB5Completeness.lean`

### 8. What Comes After the Modal Cube

Once all 15 logics have soundness and completeness:

1. **Cube Bridge Theorems** (immediate follow-up): `K_eq_derivable`, `T_eq_derivable`, etc. connecting Cube.lean's semantic definitions to the syntactic proof systems. This is the capstone.

2. **Decidability/Finite Model Property**: The bimodal module already has FMP proofs. Modal FMP is simpler — all 15 cube logics have FMP. This is a natural next extension.

3. **Derived Relationships** (proof that logics include each other syntactically):
   - `K ⊆ T` (every K-derivable formula is T-derivable) — via axiom predicate embedding
   - These mirror the `k_subset_t` semantic proofs in Cube.lean but at the syntactic level

4. **Generic Theorem Libraries**: 
   - `Theorems/Modal/T.lean` (T-level theorems using `[ModalTHilbert S]`)
   - `Theorems/Modal/S4.lean` (S4-level theorems)
   - Currently only `Basic.lean` (K-level) and `S5.lean` exist

5. **Tableau/Sequent Calculi**: Alternative proof systems with cut-elimination, connecting to the Hilbert systems via equivalence proofs.

### 9. Risk Assessment for This Task

**Low risk** (most of the work):
- Soundness proofs: purely mechanical (each axiom case already has a validity lemma)
- Instance registration: boilerplate following established patterns
- K4, D4, D5, D45: compose existing canonical proofs

**Medium risk**:
- KB completeness: Need to prove canonical symmetry (`R S T → R T S`). Uses axiom B: `φ → □◇φ`. The argument: if `R S T` (i.e., `{ψ | □ψ ∈ S} ⊆ T`), and `φ ∈ T`, then by B: `□◇φ ∈ T`. We need `□◇φ ∈ T → ◇φ ∈ S`... this requires care. The standard proof uses the contrapositive.
- K5 completeness: Need canonical Euclidean property. Standard proof uses axiom 5 (`◇φ → □◇φ`).
- KB5 completeness: Combines B and 5; need to verify the canonical model has the joint property.

**Very low risk**: Infrastructure extension, since all pieces already exist.

## Recommended Approach

1. **Single infrastructure task** (Wave 0): Extend `Instances.lean` with 10 new axiom predicates and tag types+instances. ~400-500 lines.

2. **Three Wave 1 tasks** (parallel): KB, K4, K5 — each self-contained with soundness + completeness. ~200-350 lines each.

3. **Four Wave 2 tasks** (parallel): K45, D4, D5, KB5 — each composes Wave 1 canonical proofs. ~150-250 lines each.

4. **Three Wave 3 tasks** (parallel): TB, D45, DB — three-axiom compositions. ~150-250 lines each.

5. **Integration task** (Wave 4): Update `Metalogic.lean` aggregator, update Cube.lean with bridge theorems connecting semantic and syntactic characterizations.

**Total: 12 tasks across 5 waves.**

Alternative: Fewer, larger tasks. E.g., group Wave 1 into a single task (since all three are needed before Wave 2). This gives **5 tasks** (infrastructure, single-axiom batch, two-axiom batch, three-axiom batch, integration). The tradeoff: larger tasks are harder to parallelize but reduce orchestration overhead.

## Evidence/Examples

- Tasks 95-97 took K/T/D/S4 from nothing to completion in ~3 parallel tasks. The same parallelization applies here.
- The parameterized `soundness` theorem (Soundness.lean:85) makes new soundness proofs ~40-90 lines each (just the `h_ax_sound` callback).
- The per-system completeness files range from 133 lines (T) to 452 lines (D), with the variation driven by the complexity of the frame property proofs.
- All `HasAxiom*` typeclasses and `Axioms.*` schema abbreviations for B, 4, 5, D, T, K already exist.

## Confidence Level

**High** — The infrastructure is proven, the patterns are established, and all mathematical content (validity lemmas, axiom schemas) is already formalized. The remaining work is systematic composition, not novel research. The main unknowns are the exact canonical model proofs for B and 5 in isolation, but these follow standard textbook arguments (Blackburn Ch. 4).
