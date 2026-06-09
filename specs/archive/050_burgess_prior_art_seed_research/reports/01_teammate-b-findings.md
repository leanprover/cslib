# Teammate B Findings: Bimodal BXCanonical Infrastructure Audit

**Task**: 50 — Burgess Prior Art and Seed Research for Tasks 46-49
**Angle**: Alternative Approaches — Bimodal infrastructure transferability analysis
**Date**: 2026-06-09

## Key Findings

1. **The Chronicle construction is almost entirely temporal-only.** Despite living under `Bimodal/`, the Chronicle subdirectory (12,096 lines) operates on temporal connectives (U, S, G, H, F, P) with zero references to `Formula.box` or `Formula.diamond`. The only bimodal element is the `FrameClass` parameter and the import path namespacing.

2. **The `box` modality appears ONLY in Frame.lean (BXPoint), TruthLemma.lean, CanonicalModel.lean, and ChronicleToCountermodel files.** These are the "last mile" integration points where the chronicle is embedded into a bimodal model. The core construction machinery (RRelation, ChronicleTypes, PointInsertion, CounterexampleElimination, ChronicleConstruction) is purely temporal.

3. **The Temporal/ metalogic already has phases 1-5 complete** (DeductionTheorem, MCS, Soundness + helper lemmas in Completeness.lean). It has its own `CanonicalWorld`, `canonical_acc`, G/H truth lemma, and a `completeness` theorem with a single `sorry` on the canonical model construction. The Chronicle infrastructure slots directly into this sorry.

4. **Formula type difference is the structural barrier.** Temporal uses 5 constructors (atom, bot, imp, untl, snce) while Bimodal has 6 (adds `box`). This means ALL imports must be rewritten — you cannot import Bimodal.Formula into Temporal code. The proofs themselves are nearly identical but operate on different types.

5. **Strong abstraction opportunity exists for the future** but is NOT blocking. The `g_content`/`h_content` machinery, `SetDeductivelyClosed`, `rRelation`, `rMaximal`, deductive closure, and Zorn's-lemma-based extension theorems are all formula-type-agnostic in logic — they only need: (a) a formula type with imp/bot/untl/snce/all_future/all_past, (b) a derivation system with necessitation and k-distribution, (c) specific axioms (BX3-BX11). These could be parameterized over a typeclass.

## Per-File Analysis

### Chronicle/RRelation.lean (1695 lines) → Task 46

**What transfers directly**: ~95% of the file. The entire r-relation definition, `rRelation_guard_continues'`, deductive closure infrastructure, `rMaximal_extension_exists`, `rMaximalSince_extension_exists`, `r3Maximal_extension_exists`, and all Burgess R3 machinery.

**Bimodal-specific elements**: NONE in the proof content. Only the namespace (`Cslib.Logic.Bimodal...`), import paths, and the `FrameClass` type (which is bimodal's `Base/Dense/Discrete` enum). The temporal version doesn't need `FrameClass` at all — it has a single derivation system.

**What changes**:
- Import paths: `Cslib.Logics.Bimodal.X` → `Cslib.Logics.Temporal.X`
- `FrameClass` parameter removed (temporal has a single proof system)
- `SetMaximalConsistent fc M` → `Temporal.SetMaximalConsistent M`
- Theorem references (e.g., `Cslib.Logic.Bimodal.Theorems.past_necessitation` → temporal equivalent)
- `liftBase` helper unnecessary (no frame class lattice)
- `DerivationTree fc L φ` → `temporalDerivationSystem.Deriv L φ` (wrapped in `Nonempty`)

**Abstraction candidate**: HIGH. The `rRelation`, `rMaximal`, `SetDeductivelyClosed`, and deductive closure definitions are logic-agnostic. A shared `Chronicle.Core` module parameterized over `FormulaType` and `DerivSystem` could serve both.

### Chronicle/ChronicleTypes.lean (386 lines) → Task 47

**What transfers directly**: ~85%. The `Chronicle` structure (dom : Finset Rat, f : Rat → Set Formula, g : Rat → Rat → Set Formula), DCS definitions, `ClosedUnderDerivation`, `mcs_is_dcs`, `cud_modus_ponens`, and condition C0.

**Bimodal-specific elements**: `liftBase`, `mcs_to_base` (converting between `fc` and `FrameClass.Base`), and the `FrameClass` parameter. Also imports `ModalSaturation` (not needed for temporal).

**What changes**:
- Same import path rewrite as RRelation
- Remove `FrameClass` parameter and `liftBase`/`mcs_to_base` helpers
- Remove `ModalSaturation` import (bimodal-specific)
- The chronicle conditions (C0-C5) are defined in terms of temporal content (g_content/h_content subset, until/since witnesses) — these transfer directly once the helper definitions exist

**Abstraction candidate**: MEDIUM. The `Chronicle` structure itself and conditions C0-C5 are logic-agnostic, but they reference `Formula Atom` directly.

### Chronicle/PointInsertion.lean (3556 lines) → Task 47

**What transfers directly**: ~90%. All of Burgess Lemmas 2.4-2.7, the `BurgessR3` and `BurgessR3Maximal` definitions, seed consistency proofs, and the point insertion construction.

**Bimodal-specific elements**: NONE in proof content. References `Cslib.Logic.Bimodal.Theorems.TemporalDerived` and `Cslib.Logic.Bimodal.Theorems.Propositional.Core` but these are derived theorems about temporal connectives that happen to be proved in the Bimodal module. The temporal module would need its own versions.

**What changes**:
- Import path rewrite
- Remove `FrameClass` parameter
- Need temporal-side versions of: `temp_k_dist_derived`, `past_necessitation`, `past_k_dist`, `double_negation`, various propositional combinators
- The existing `Completeness.lean` in Temporal/ already has `derive_dne`, `derive_h_nec`, and many of these patterns

**Abstraction candidate**: LOW for individual lemmas (too tightly coupled to proof steps), HIGH for the overall structure (point insertion as a parameterized operation).

### Chronicle/CounterexampleElimination.lean (3529 lines) → Task 48

**What transfers directly**: ~95%. The `C5Counterexample`/`C5'Counterexample` structures, `eliminate_C5_counterexample`/`eliminate_C5'_counterexample`, `PotentialCounterexample`, and the uniform elimination interface are all purely temporal.

**Bimodal-specific elements**: NONE. Only imports and namespace.

**What changes**: Same mechanical rewrite as other files.

**Abstraction candidate**: HIGH. The counterexample structures and elimination procedures are formula-agnostic once the chronicle types are parameterized.

### Chronicle/ChronicleConstruction.lean (1531 lines) → Task 48

**What transfers directly**: ~95%. `singleton_chronicle`, `omega_chain`, `limit_chronicle`, `limit_satisfies_c0`, `limit_satisfies_c5` — all purely temporal.

**Bimodal-specific elements**: The `[Denumerable (Formula Atom)]` instance requirement (needed for omega-chain enumeration) — this exists for both formula types.

**What changes**: Import path rewrite; remove `FrameClass` parameter.

**Abstraction candidate**: HIGH. The omega-chain construction is completely logic-agnostic.

### BXCanonical/Frame.lean (464 lines) → Task 46

**What transfers directly**: ~60%. The `g_content_closed_derivation`, `h_content_closed_derivation`, `g_content_set_consistent`, `h_content_set_consistent`, `bx_le_trans`, `bx_forward_witness`, `bx_backward_witness`, G/H forward/backward — all temporal content.

**Bimodal-specific elements**:
- `BXPoint` structure: wraps `Set (Formula Atom)` + `SetMaximalConsistent FrameClass.Base formulas` — temporal needs its own `TPoint` with `Temporal.SetMaximalConsistent`
- `bx_modal_equiv`: BIMODAL-ONLY (box equivalence relation) — NOT NEEDED for temporal
- `bx_le_refl`: sorry'd under irreflexive semantics — same issue for temporal

**What changes**:
- Define `TPoint` (temporal point) with `Temporal.SetMaximalConsistent`
- `bx_le` definition (`g_content w ⊆ v`) transfers directly
- Remove all `bx_modal_equiv` references
- Remove `FrameClass` parameter

**Abstraction candidate**: MEDIUM. `TPoint`-like structures could be parameterized but the MCS type differs.

### BXCanonical/CanonicalChain.lean (95 lines) → Task 46

**What transfers directly**: 100% of the temporal content. `F_imp_top_until_mcs`, `P_imp_top_since_mcs`, `absorb_until_mcs`, `absorb_since_mcs`, delegation bridges — all operate on U/S/F/P.

**Bimodal-specific elements**: NONE in logic; only `BXPoint` type reference and `FrameClass.Base`.

**What changes**: Replace `BXPoint` → `TPoint`; remove `FrameClass.Base`.

**Abstraction candidate**: HIGH — these are pure axiom instantiations.

### BXCanonical/OrderedSeedConsistency.lean (151 lines) → Task 46

**What transfers directly**: 100%. `enriched_resolving_seed_consistent`, `temp_linearity_mcs`, `two_defect_consistent_seed`, `no_new_f_defects`, `resolved_target_in_successor` — all purely temporal.

**Bimodal-specific elements**: NONE. Only namespace and `FrameClass.Base`.

**What changes**: Mechanical rewrite.

**Abstraction candidate**: HIGH — completely logic-agnostic modulo the MCS type.

### BXCanonical/TruthLemma.lean (223 lines) → Task 49

**What transfers directly**: ~70%. `bot_not_in_mcs`, `imp_iff_mcs`, `G_iff_mcs`, `H_iff_mcs`, `until_forward_mcs`, `since_forward_mcs`, `bx_lt`, `F_from_witness`, `P_from_witness` — all temporal.

**Bimodal-specific elements**:
- `box_iff_mcs` (30 lines): BIMODAL-ONLY — NOT NEEDED for temporal
- References to `bx_modal_witness`

**What changes**: Remove `box_iff_mcs`; replace `BXPoint` → `TPoint`.

**Abstraction candidate**: MEDIUM. The truth lemma for atom/bot/imp/G/H/U/S is essentially identical for both logics.

### BXCanonical/CanonicalModel.lean (771 lines) → Task 49

**What transfers directly**: ~40%. The Z-chain MCS propagation patterns (forward_G, backward_H) transfer. The FMCS/BFMCS construction is heavily bimodal-specific.

**Bimodal-specific elements**:
- `FMCS`, `BFMCS` structures (bundle of families of MCS indexed by Int) — bimodal-specific
- `bx_modal_witness_fc` — NOT NEEDED
- Modal saturation, box-equivalence classes — NOT NEEDED

**What changes**: For temporal, the canonical model is simpler — just a Z-chain of MCS (which the existing `Completeness.lean` already sketches). No need for BFMCS/modal families.

**Abstraction candidate**: LOW. The bimodal canonical model is structurally different (indexed families of Z-chains) from the temporal canonical model (single Z-chain).

### Chronicle/ChronicleToCountermodelBasic.lean (1170 lines) → Task 49

**What transfers directly**: ~50%. The `LimitDomSubtype`, countability instance, `NoMinOrder`/`NoMaxOrder` instances, and the dense-case Cantor isomorphism transfer. The discrete-case pipeline is bimodal-specific (depends on task 36).

**Bimodal-specific elements**:
- Dense case uses `ParametricCompleteness`, `ParametricTruthLemma` — algebraic completeness machinery from Bimodal/Algebraic/
- Discrete case depends entirely on WeakCanonical (task 36) — sorry'd

**What changes**: The temporal version needs its OWN truth-lemma-to-model pipeline. For pure temporal completeness (no box), this is SIMPLER: the chronicle directly provides a model on Rat (dense case) without needing the algebraic parametric machinery.

**Abstraction candidate**: LOW for the integration; MEDIUM for `LimitDomSubtype` utilities.

### Chronicle/ChronicleToCountermodel.lean (229 lines) → Task 49

**What transfers directly**: ~20%. The `mcs_mixed_case_absurd` theorem is fully proved but is bimodal-specific (about box(next_top)). The discrete pipeline stubs are all sorry'd.

**Bimodal-specific elements**: Everything after `mcs_mixed_case_absurd` is bimodal-specific (box, S5 axioms, BFMCS).

**What changes**: For temporal completeness, this file is NOT NEEDED. The temporal case doesn't have a dense/discrete case split driven by box — the chronicle on Rat directly gives a dense model. The "discrete temporal completeness" (task 39) uses entirely different machinery.

**Abstraction candidate**: NONE.

## Existing Temporal Infrastructure Assessment

### Completeness.lean (418 lines) — The Target

**Available** (fully proved):
- `mcs_mp_axiom`, `mcs_top_mem`, `mcs_f_top_mem`, `mcs_p_top_mem`, `mcs_g_bot_not_mem`, `mcs_h_bot_not_mem`
- `derive_dne` (double negation elimination)
- `derive_h_nec` (H-necessitation from derivability)
- `mcs_dne` (¬¬X ∈ Ω ↔ X ∈ Ω)
- `mcs_ff_imp_f` (F-idempotency)
- `mcs_pp_imp_p` (P-idempotency)
- `mcs_g_trans` (G-transitivity)
- `mcs_h_trans` (H-transitivity)
- `past_of_future_subset`, `future_of_past_subset` (BX4/BX4' consequences)
- `CanonicalWorld`, `canonical_acc`, truth lemma for G/H
- `exists_future_successor`, `exists_past_predecessor`
- `neg_consistent_of_not_derivable`
- `completeness` theorem with single `sorry`

**The sorry** is at line 416: building a Z-chain canonical model and proving the full truth lemma including Until/Since. This is exactly what the Chronicle construction provides.

### MCS.lean (100+ lines)
- `Temporal.SetConsistent`, `Temporal.SetMaximalConsistent` abbreviations
- `temporal_lindenbaum` (Lindenbaum's lemma)
- `temporal_closed_under_derivation`, `temporal_implication_property`, `temporal_negation_complete`
- `mcs_bot_not_mem`, `mcs_neg_of_not_mem`, `mcs_not_mem_of_neg`
- `mcs_g_mp` (G-distribution)
- `mcs_g_witness`, `mcs_h_witness`

### DeductionTheorem.lean
- Full deduction theorem for temporal BX

### What's Missing for Chronicle Port

The temporal module needs these that exist in Bimodal but not yet in Temporal:

1. **g_content / h_content definitions** — `{φ | G(φ) ∈ M}` and `{φ | H(φ) ∈ M}` — trivial to define
2. **forward/past temporal witness seed consistency** — seeds like `{ψ} ∪ g_content(M)` are consistent when `F(ψ) ∈ M`
3. **g_content_closed_derivation / h_content_closed_derivation** — using G-necessitation + K-distribution
4. **Temporal axiom instantiations** (BX3-BX13 at MCS level) — many already exist in `Completeness.lean` but as private theorems
5. **Propositional combinators** (pairing, lce_imp, rce_imp, identity, imp_trans, contraposition, efq_axiom, double_negation) — most exist in Bimodal but not Temporal
6. **Temporal derived theorems** (`temp_k_dist_derived`, etc.)

## Recommended Approach

### Direct Port First, Abstract Later (Recommended)

**Phase 1** (Tasks 46-49): Port directly, creating a parallel `Cslib/Logics/Temporal/Metalogic/Chronicle/` directory with temporal-specific versions of each file. This is straightforward because:
- 90%+ of proof content is temporal-only
- Changes are mechanical (import paths, remove FrameClass, swap MCS types)
- No cross-module dependencies to manage
- Can test incrementally

**Phase 2** (Task 41): After both temporal and bimodal versions exist, identify the common core and abstract. Priority abstraction targets:
- `rRelation`, `rMaximal`, `SetDeductivelyClosed`, deductive closure (RRelation.lean)
- `Chronicle` structure and conditions C0-C5 (ChronicleTypes.lean)
- Counterexample structures and elimination (CounterexampleElimination.lean)
- Omega-chain construction (ChronicleConstruction.lean)
- Seed consistency theorems (OrderedSeedConsistency.lean)

### Pre-Port Preparation (Before Task 46)

Before starting the Chronicle port, create temporal-side helper infrastructure:

1. **`Temporal/Metalogic/TemporalContent.lean`**: Define `g_content`, `h_content`, `f_content`, `p_content` for `Temporal.Formula`
2. **`Temporal/Theorems/Propositional/Core.lean`**: Port propositional combinators (pairing, lce_imp, rce_imp, etc.)
3. **`Temporal/Theorems/TemporalDerived.lean`**: Port `temp_k_dist_derived`, `past_necessitation`, `past_k_dist`
4. **Promote private helpers in Completeness.lean**: `derive_dne`, `derive_h_nec`, `mcs_dne`, etc. should be accessible outside the file

### Quick Wins for Abstraction (Low-Risk, High-Value)

Even during the direct port, two abstractions are safe to do immediately:

1. **Propositional combinators**: These are formula-type-agnostic. A `Cslib.Foundations.Logic.Propositional` module could serve Modal, Temporal, and Bimodal.
2. **Deductive closure + Zorn's lemma extension**: The `deductiveClosure`, `rMaximal_extension_exists` pattern only needs a derivation system — it's the same proof for any logic.

## Confidence Level

**Overall**: HIGH

- The Chronicle files are well-documented, explicitly reference Burgess 1982, and note their porting provenance
- The bimodal/temporal boundary is clean — box modality appears only in integration files
- The existing temporal infrastructure (phases 1-5) provides a solid foundation
- The remaining sorry in `completeness` is exactly the gap the Chronicle construction fills
- Line count estimates in task descriptions (800-3000 per task) are realistic given the mechanical nature of the port
