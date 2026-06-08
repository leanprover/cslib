# Teammate D (Horizons): Strategic Analysis

**Task**: Integrate BimodalLogic results into cslib
**Date**: 2026-06-08
**Angle**: Strategic alignment, long-term direction, integration approach

## Key Findings

1. **cslib explicitly welcomes modal and temporal logics** — the CONTRIBUTING.md lists "Temporal logic" and "Modal logics" as example contributions under Pillar 1 > Logics, and already has a `Cslib.Logics.Modal` module (K, T, B, 4, 5, D and the full Modal Cube with soundness/completeness direction results).

2. **BimodalLogic is a massive, largely self-contained formalization** — 246 Lean files, ~85k lines. The sorry-free portions (Syntax, Semantics, ProofSystem, Core metalogic, SoundnessLemmas, FrameConditions, Decidability, ConservativeExtension, Automation) total ~40k+ lines. The sorry-heavy parts (Bundle ~19 sorries, BXCanonical ~43, WeakCanonical ~107, Theorems ~19) total ~83k lines.

3. **Major toolchain gap**: cslib is on Lean v4.31.0-rc1 with Mathlib at a recent commit, while BimodalLogic targets Lean v4.27.0-rc1. This is a 4-version gap that will require significant porting.

4. **Architectural style differences**: cslib uses `module`, `@[expose] public section`, `Cslib.Init` imports, `InferenceSystem` typeclass, Mathlib's `grind` tactic heavily, and follows Mathlib style conventions. BimodalLogic uses independent patterns (its own `Formula` inductive, custom axiom constructors, hand-rolled MCS theory).

5. **The sorry-free core (Syntax + Semantics + ProofSystem + Core + Soundness + Decidability + Automation) constitutes a strong, complete submission candidate** — approximately 38k lines of verified code including a full decision procedure with proof extraction and soundness for base, dense, and discrete systems.

## cslib's Current Scope and Direction

cslib positions itself as "The Lean library for Computer Science" — a broad, reusable infrastructure project analogous to Mathlib but for CS. Its current content spans:

- **Computability**: Automata (DFA, NFA, epsilon-NFA), Turing machines, URM, distributed algorithms (FLP), Myhill-Nerode theorem
- **Languages**: Lambda calculus (named + locally-nameless), CCS process algebra, Boole verification language, combinatory logic
- **Logics**: Propositional (natural deduction), Modal (K through S5 cube), HML, Linear logic (CLL + cut elimination)
- **Foundations**: LTS/FLTS semantics, inference systems, bisimulation, syntax foundations
- **Other**: Cryptography (secret sharing), Machine Learning (PAC learning, VC dimension), Probability, Algorithms (merge sort)

The existing Modal logic development in cslib is relatively small (~270 lines across 3 files) and focused on Kripke semantics for the modal cube — basic definitions, satisfaction, and frame condition soundness/completeness for individual axioms (K, T, B, 4, 5, D). There is no temporal logic, no proof system, no decidability procedure, and no completeness theorem.

Recent development priorities (from git log) show active work on automata theory (Myhill-Nerode), distributed algorithms (FLP), machine learning (PAC/VC dimension), lambda calculus, and cryptography. The project is actively growing and welcoming substantial contributions.

## How BimodalLogic Fits Strategically

**BimodalLogic fills a significant gap.** Temporal logic is explicitly listed in CONTRIBUTING.md as a wanted contribution. The bimodal logic TM combines S5 modal operators with Since/Until temporal operators — this directly extends the existing Modal cube work and adds an entirely new dimension (temporal reasoning) to cslib.

**Strategic value hierarchy** (what matters most for cslib):
1. **Temporal logic foundations** — cslib has none; this would be the first
2. **Complete metalogic** — soundness + completeness for a non-trivial multi-modal logic is a flagship result
3. **Decision procedure** — verified decidability with proof extraction is highly practical
4. **Task semantics** — a novel semantic framework (world-histories over task frames) that goes beyond standard Kripke semantics
5. **Automation** — proof search tactics and training data generation

**Risk**: The full BimodalLogic codebase is enormous (85k lines) and has 209 sorries. Attempting to integrate it all at once would be infeasible and would not meet cslib's quality bar. A phased approach is essential.

## Integration Approach Recommendation (adapt vs as-is)

**Recommendation: Significant adaptation required, phased integration.**

The code cannot go in as-is for several reasons:

1. **Namespace conventions**: BimodalLogic uses `Bimodal.*` namespace; cslib requires `Cslib.Logics.Bimodal.*` (or possibly `Cslib.Logics.Temporal.*` and `Cslib.Logics.Modal.Bimodal.*`)
2. **Import structure**: Must use `Cslib.Init` as base import, adopt `module` declarations and `@[expose] public section` pattern
3. **Typeclass integration**: BimodalLogic's `Formula` type should consider integration with or at least awareness of `Cslib.Logic.Modal.Proposition` and the `InferenceSystem` framework
4. **No sorries**: cslib will not accept files with `sorry` — only sorry-free modules should be integrated
5. **Mathlib version**: Must be updated to work with cslib's Mathlib dependency (v4.31.0-rc1 toolchain)
6. **Documentation**: cslib requires Mathlib-style docstrings on all public definitions/theorems
7. **Linting**: Must pass `lake lint`, `lake exe lint-style`, and `lake shake`

**Recommended phased approach**:

| Phase | Content | Lines (est.) | Sorry-free? | Standalone? |
|-------|---------|-------------|-------------|-------------|
| 1 | Syntax (Formula, Atom, Subformulas) | ~3.3k | Yes | Yes |
| 2 | Semantics (TaskFrame, WorldHistory, TaskModel, Truth, Validity) | ~1.8k | Yes | Depends on Syntax |
| 3 | ProofSystem (Axioms, Derivation, Derivable) | ~1.6k | Yes | Depends on Syntax |
| 4 | Soundness (Core lemmas + base soundness) | ~5.2k | Mostly (4 sorries in top-level Soundness.lean) | Depends on 1-3 |
| 5 | Core Metalogic (MCS, Deduction theorem) | ~2.8k | Yes | Depends on 1-3 |
| 6 | Decidability (Tableau, FMP, proof extraction) | ~8.1k | Yes | Depends on 1-5 |
| 7 | FrameConditions | ~0.8k | Yes | Depends on 1-3 |
| 8 | Automation (tactics, proof search) | ~18.9k | Yes | Depends on 1-3 |

Each phase should be a separate PR for reviewability.

## Opportunities for Cross-Connection

1. **Extend existing Modal module**: BimodalLogic's S5 fragment directly relates to cslib's `Cslib.Logics.Modal.Cube.S5`. Could provide instances showing the modal fragment of TM specializes to S5.

2. **InferenceSystem integration**: BimodalLogic's proof system (axioms + derivation rules) should instantiate cslib's `HasInferenceSystem` typeclass, connecting bimodal derivability to the library-wide inference framework.

3. **LTS connection**: cslib's `Cslib.Foundations.Semantics.LTS` formalization of labelled transition systems could connect to BimodalLogic's task frames — task relations are a generalization of LTS transitions indexed by duration.

4. **OmegaSequence/Temporal**: cslib has `Cslib.Foundations.Data.OmegaSequence.Temporal` which deals with temporal properties of infinite sequences — potential connection to BimodalLogic's temporal operators.

5. **Propositional logic foundation**: BimodalLogic's propositional fragment (embedded within the bimodal formula type) could share definitions or at least theorems with `Cslib.Logics.Propositional`.

6. **Future temporal logics**: Once the bimodal infrastructure is in cslib, it opens the door for LTL, CTL, CTL*, and other temporal logics that share the Since/Until operator core — significant reuse potential.

7. **Process algebra connection**: CCS (`Cslib.Languages.CCS`) has temporal behavior; bimodal logic could provide a logical characterization of temporal properties of processes.

## Confidence Level

**High** — The strategic fit is clear: temporal logic is explicitly wanted, the existing modal logic foundation is small enough that integration won't create conflicts, and the BimodalLogic codebase has substantial sorry-free content. The main risk is the porting effort (toolchain upgrade, style adaptation, documentation), not the strategic direction.
