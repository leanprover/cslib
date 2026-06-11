# Research Report: Task #99

**Task**: Complete modal cube Hilbert proof systems
**Date**: 2026-06-11
**Mode**: Team Research (4 teammates)
**Session**: sess_1781152895_0648ac

## Summary

The infrastructure for completing the remaining 10 modal cube logics (B, Four, Five, K45, D4, D5, D45, DB, TB, KB5) is overwhelmingly in place. All 6 individual axiom typeclasses (`HasAxiomK`, `HasAxiomT`, `HasAxiom4`, `HasAxiomB`, `HasAxiom5`, `HasAxiomD`) exist, as do semantic validity lemmas for every axiom. The parameterized `soundness` theorem, three truth lemma variants, and the canonical model construction are all reusable. **Only two genuinely new mathematical proofs are needed**: `canonical_symm` (symmetry from axiom B) and `canonical_eucl_from_5` (Euclideanness from axiom 5). Everything else is systematic composition following established patterns.

## Key Findings

### 1. Existing Infrastructure (Complete and Reusable)

| Layer | What Exists | Status |
|-------|-------------|--------|
| Typeclasses | `HasAxiomK/T/4/B/5/D` (all 6) | Complete |
| Bundled classes | `ModalHilbert`, `ModalTHilbert`, `ModalDHilbert`, `ModalS4Hilbert`, `ModalS5Hilbert` | 5 of 15 |
| Tag types | `HilbertK/T/D/S4/S5` | 5 of 15 |
| Axiom predicates | `KAxiom`, `TAxiom`, `DAxiom`, `S4Axiom`, `ModalAxiom` | 5 of 15 |
| Soundness | Parameterized `soundness` + 5 per-system proofs | Fully reusable |
| Completeness | Parameterized canonical model + 5 per-system proofs | Fully reusable |
| Canonical frame properties | `canonical_refl`, `canonical_trans`, `canonical_eucl`, `canonical_serial` | 4 of 6 needed |
| Truth lemma variants | `truth_lemma` (T), `truth_lemma_d` (D), `k_truth_lemma` (K) | All 3 needed variants exist |
| Semantic validity | `Satisfies.k/t/b/four/five/d` | All 6 exist |

### 2. What's Missing (Two Critical Lemmas)

**A. `canonical_symm`** — The canonical relation is symmetric when axiom B is present.

Required by: B, DB, TB, KB5 (4 systems)

Proof strategy (Blackburn Thm 4.28 clause 2):
1. Assume `R(w,v)` (canonical). Take any `□φ ∈ v`. Need `φ ∈ w`.
2. Suppose for contradiction `φ ∉ w`. Then `¬φ ∈ w` (MCS).
3. By axiom B at w: `¬φ → □◇(¬φ)`, so `□◇(¬φ) ∈ w`.
4. Since `R(w,v)`: `◇(¬φ) ∈ v`.
5. In encoding: `◇(¬φ) = (□((φ→⊥)→⊥))→⊥ = (□¬¬φ)→⊥`.
6. From `□φ ∈ v`, derive `□¬¬φ ∈ v` via K + DNE introduction (derivation tree manipulation).
7. Then `(□¬¬φ)→⊥ ∈ v` and `□¬¬φ ∈ v` gives `⊥ ∈ v` — contradiction with MCS.

Risk: MEDIUM-HIGH. Requires derivation tree gymnastics for DNE step, following the existing pattern in `canonical_eucl` (Completeness.lean:127-141).

**B. `canonical_eucl_from_5`** — The canonical relation is Euclidean when axiom 5 is present.

Required by: Five, K45, D5, D45, KB5 (5 systems)

Proof strategy (from Teammate C's detailed analysis):
1. Assume `R(w,v)` and `R(w,u)`. Take `□φ ∈ v`. Need `φ ∈ u`.
2. Suppose for contradiction `□φ ∉ w`. Then `¬□φ ∈ w`, i.e., `◇¬φ ∈ w`.
3. By axiom 5 at w: `◇¬φ → □◇¬φ`, so `□◇¬φ ∈ w`.
4. Since `R(w,v)`: `◇¬φ ∈ v`.
5. But `□φ ∈ v` implies `¬◇¬φ ∈ v` (since `◇¬φ` = `¬□φ` in classical logic, derivable via DNE steps).
6. Contradiction. So `□φ ∈ w`. Since `R(w,u)`: `φ ∈ u`. ✓

Risk: HIGH. This is the hardest new proof — does NOT exist in the codebase. The `canonical_eucl` proof (S5) derives Euclideanness from T+4+B combined, which is mathematically distinct. The diamond/negation encoding (`◇ψ = (□(ψ→⊥))→⊥`) adds syntactic complexity.

### 3. Truth Lemma Classification (No New Variants Needed)

| Logic | Has T? | Has D? | Truth Lemma | Box Witness Used |
|-------|--------|--------|-------------|-----------------|
| B | No | No | `k_truth_lemma` | `k_mcs_box_witness` |
| Four | No | No | `k_truth_lemma` | `k_mcs_box_witness` |
| Five | No | No | `k_truth_lemma` | `k_mcs_box_witness` |
| K45 | No | No | `k_truth_lemma` | `k_mcs_box_witness` |
| KB5 | No | No | `k_truth_lemma` | `k_mcs_box_witness` |
| D4 | No | Yes | `truth_lemma_d` | `mcs_box_witness_d` |
| D5 | No | Yes | `truth_lemma_d` | `mcs_box_witness_d` |
| D45 | No | Yes | `truth_lemma_d` | `mcs_box_witness_d` |
| DB | No | Yes | `truth_lemma_d` | `mcs_box_witness_d` |
| TB | Yes | Yes* | `truth_lemma` | `mcs_box_witness` |

*TB has T, which implies D (proven in Cube.lean).

### 4. Per-System Design

Each new system follows the uniform pattern:

| System | Axioms (beyond propositional + K) | Frame Conditions | File Names |
|--------|-----------------------------------|------------------|------------|
| B (KB) | B | Symmetric | `BSoundness.lean`, `BCompleteness.lean` |
| Four (K4) | 4 | Transitive | `K4Soundness.lean`, `K4Completeness.lean` |
| Five (K5) | 5 | Euclidean | `K5Soundness.lean`, `K5Completeness.lean` |
| K45 | 4, 5 | Trans + Eucl | `K45Soundness.lean`, `K45Completeness.lean` |
| D4 | D, 4 | Serial + Trans | `D4Soundness.lean`, `D4Completeness.lean` |
| D5 | D, 5 | Serial + Eucl | `D5Soundness.lean`, `D5Completeness.lean` |
| D45 | D, 4, 5 | Ser + Trans + Eucl | `D45Soundness.lean`, `D45Completeness.lean` |
| DB | D, B | Serial + Symm | `DBSoundness.lean`, `DBCompleteness.lean` |
| TB (KTB) | T, B | Refl + Symm | `TBSoundness.lean`, `TBCompleteness.lean` |
| KB5 | B, 5 | Symm + Eucl | `KB5Soundness.lean`, `KB5Completeness.lean` |

### 5. Architectural Decision: Standalone Predicates + Typeclass Composition

**Resolved conflict**: Teammate D suggested constraint-only instances (no new bundled classes), while A/B suggested creating bundled classes for each logic.

**Resolution**: Create minimal bundled classes only where they enable future API use (e.g., `ModalBHilbert`, `ModalK4Hilbert`), following the existing pattern established for K/T/D/S4/S5. This is consistent with the codebase style and enables typeclass-driven reasoning. The cost is low (~3 lines per class). Systems with >2 axioms beyond K can use constraint-only instances if needed.

### 6. Soundness Pattern (Uniform, Mechanical)

Every soundness proof follows the identical structure:
1. Define axiom predicate with constructors for each axiom
2. Prove `x_axiom_sound` by cases — dispatch to existing `Satisfies.*` lemmas
3. Wrap with `x_soundness` and `x_soundness_derivable` via parameterized `soundness`

The propositional cases (implyK, implyS, efq, peirce) and modalK are literally copy-paste across all systems. Estimated ~40-90 lines per soundness file.

### 7. Completeness Pattern (Compositional)

Every completeness proof follows:
1. `by_contra` (φ not derivable → {¬φ} consistent)
2. Lindenbaum extension to MCS
3. Apply appropriate truth lemma
4. Apply canonical frame property lemmas (compose from existing)
5. Instantiate universal validity hypothesis → contradiction

Estimated ~80-200 lines per completeness file (depending on number of frame properties).

## Synthesis

### Conflicts Resolved

1. **Bundled classes vs. constraints**: Use bundled classes (consistent with existing K/T/D/S4/S5 pattern). Low cost, enables future typeclass reasoning.

2. **Wave ordering**: Synthesized from all teammates into optimal 4-wave structure (see below). Key insight from Critic: infrastructure (Wave 0) must be a hard prerequisite, especially `canonical_eucl_from_5` which blocks 5 systems.

3. **Naming convention**: Use flat file naming matching existing pattern (e.g., `K4Soundness.lean` not `FourSoundness.lean`) since "K4" is the standard logic name for what Cube.lean calls "Four". Exception: `BSoundness.lean` (the Cube.lean name) since "KB" could be confused with a file about K and B separately.

4. **Contrapositive factoring**: The Critic recommended factoring out the shared contrapositive setup (~30 lines duplicated in each completeness proof). Resolution: **Optional optimization** — not blocking, and refactoring existing working proofs carries risk. Can be done in a follow-up task.

### Gaps Identified

1. **Encoding challenge**: The diamond encoding `◇ψ = (□(ψ→⊥))→⊥` makes the B and 5 canonical proofs syntactically heavier than textbook presentations. The existing `canonical_eucl` already handles this (lines 127-141 of Completeness.lean), providing a template.

2. **MCS helper needed**: `mcs_five_eucl` — from `◇φ ∈ S` derive `□◇φ ∈ S` using axiom 5. This is trivial (MCS modus ponens with the axiom 5 instance) but needs to exist.

3. **No verification of `canonical_symm` + `canonical_eucl_from_5` interaction**: For KB5, we need both properties simultaneously. Mathematically they compose independently, but this should be verified in the KB5 completeness proof.

### Recommendations

#### Task Structure (Recommended: 12 Tasks, 5 Waves)

**Wave 0 — Shared Infrastructure** (1 task, prerequisite for all):
- Prove `canonical_symm` (from axiom B alone)
- Prove `canonical_eucl_from_5` (from axiom 5 alone)
- Add helper `mcs_five_eucl`
- Extend `ProofSystem.lean` with 10 new tag types
- Extend `ProofSystem.lean` with new bundled classes
- Add all 10 axiom predicates to `Instances.lean`
- Register all typeclass instances for the 10 new systems

**Wave 1 — Single-Axiom Extensions** (3 tasks, fully parallel):
- Task: B (KB) soundness + completeness
- Task: K4 (Four) soundness + completeness
- Task: K5 (Five) soundness + completeness

**Wave 2 — Two-Axiom Compounds** (4 tasks, fully parallel):
- Task: K45 soundness + completeness
- Task: TB (KTB) soundness + completeness
- Task: KB5 soundness + completeness
- Task: D4 soundness + completeness

**Wave 3 — D-Series Extensions** (3 tasks, fully parallel):
- Task: D5 soundness + completeness
- Task: D45 soundness + completeness
- Task: DB soundness + completeness

**Wave 4 — Integration** (1 task):
- Update `Metalogic.lean` module aggregator with all new imports
- Verify `lake build` passes for full module
- Optional: Cube bridge theorems connecting semantic and syntactic characterizations

#### Risk Mitigation

| Risk | Strategy |
|------|----------|
| `canonical_eucl_from_5` is hard | Attack in Wave 0 with full focus; Critic provided the exact proof strategy |
| Diamond encoding complexity | Follow existing `canonical_eucl` derivation tree pattern |
| Code volume (20 new files) | Templates from existing proofs; soundness is copy-paste |
| Interaction between B and 5 | Verify independently in KB5 completeness |

## Teammate Contributions

| Teammate | Angle | Status | Confidence | Key Contribution |
|----------|-------|--------|------------|-----------------|
| A | Primary Approach | completed | High | Infrastructure map, per-system design table, truth lemma classification |
| B | Alternatives | completed | High | Pattern evaluation (A/B/C/D), Blackburn canonicity framework, Euclidean proof sketch |
| C | Critic | completed | High | Identified canonical_eucl gap as CRITICAL, detailed proof strategy for both new lemmas |
| D | Horizons | completed | High | Wave structure, post-cube roadmap, alignment with bimodal work |

## References

- Blackburn, de Rijke, Venema — *Modal Logic* (2002), Chapter 4, Theorems 4.27–4.30
- `/home/benjamin/Projects/cslib/specs/literature/blackburn_4.md` — Chapter 4 completeness
- [Systematic Verification of the Modal Logic Cube in Isabelle/HOL](https://arxiv.org/abs/1507.08717) — Benzmüller et al.
- [FormalizedFormalLogic/Foundation (Lean 4)](https://github.com/iehality/lean4-logic) — Prior art
- Existing codebase: `Cslib/Logics/Modal/Metalogic/` (5 completed systems as templates)
