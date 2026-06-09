# Seed Research Report: Task 46 — Temporal R-relation and Witness Infrastructure

**Task**: 46 — Temporal R-relation and witness infrastructure
**Date**: 2026-06-09
**Source**: Task 50 team research (teammates A, B, C, D)
**Purpose**: Pre-digested research to allow task 46 to skip or accelerate its research phase

---

## Overview

Task 46 ports the Burgess R-relation and witness infrastructure from the bimodal `BXCanonical/Chronicle/RRelation.lean` to a new temporal-only module. It also creates the prerequisite infrastructure (Phase 0) that all Chronicle files depend on but that is not yet present in the temporal module. The bimodal source material is ~95% purely temporal — the only barrier is type-porting (different `Formula` types), not mathematical restructuring.

---

## 1. Literature Map: Burgess 1982 Section 2, Lemmas 2.2-2.5

### Lemma 2.2 — Consistency Criterion

**Statement**: If A is an MCS and U(γ,δ) ∈ A, then γ is consistent. Mirror: if A is MCS and S(γ,δ) ∈ A, then γ is consistent.

**Axioms used**: TG (temporal generalization), Replacement Lemma 2.1, axiom A2a.

**Lean target**: A lemma of the form `temporal_u_first_consistent : U γ δ ∈ A → Consistent {γ}` where A is a temporal MCS.

### Lemma 2.3 — The r-relation

**Statement**: For MCSs A, C and formula β, define r(A, β, C) as:
- (a) ∀γ ∈ C: U(γ, β) ∈ A  ⟺  (b) ∀α ∈ A: S(α, β) ∈ C

**Proof of (a)⟹(b)**: Assume (a), suppose α ∈ A with ¬S(α,β) ∈ C. By (a), U(¬S(α,β), β) ∈ A. By A3a, U(¬S(α,β) ∧ S(α,β), β) ∈ A, contradicting 2.2.

**Key axiom**: A3a bridges U and S — "the bridging axiom".

**Lean name convention**: `rRelation` (matching bimodal `rRelation` for future abstraction).

### Extensions of r

- `r(A, B, C)`: B is a DCS (deductively closed set) and r(A, β, C) holds for all β ∈ B
- `R(A, B, C)` (= `rMaximal`): B is maximal w.r.t. r(A, —, C)
- Key maximality property: if R(A,B,C) and δ ∉ B, then ∃β ∈ B, γ ∈ C: U(γ, β∧δ) ∉ A

**Lean name conventions**: `rRelation`, `rMaximal` (matching bimodal naming exactly).

### Lemma 2.4 — Witness Existence

**Statement**: If A is MCS and U(γ,β) ∈ A, then ∃B,C with β ∈ B, γ ∈ C, and R(A,B,C).

**Proof strategy**: Construct C₀ = {γ} ∪ {S(α,β) : α ∈ A}, show C₀ is consistent using A3a and 2.2, extend C₀ to MCS C, take B maximal with β ∈ B and r(A,B,C).

**Lean target**: `rMaximal_witness_exists : U γ β ∈ A → ∃ B C, β ∈ B ∧ γ ∈ C ∧ rMaximal A B C`

### Lemma 2.5 — Intersection Lemma

**Statement**: If R(A,B,C), r(A,B',D), r(D,B'',C) and B ⊆ B' ∩ D ∩ B'', then B = B' ∩ D ∩ B''.

**Key axiom**: A6a — U(δ∧U(γ,δ), δ) ∈ A implies U(γ,δ) ∈ A (transitivity).

### Axiom Correspondence Table

| Burgess J₀ | BdRV B | Role in Proof |
|---|---|---|
| A1a | A1a | U monotone in first arg |
| A2a | A2a | U monotone in second arg |
| A3a | A3a | Bridge U↔S (key for r-relation) |
| A4a | A4a | Connect current to future witness |
| A5a | A5a | U self-reinforcing |
| A6a | A6a | Transitivity of temporal order |
| A7a | A7a | Linearity (three-way disjunction) |
| Mirror images | Aib | Dual properties for S |
| TG | TG | Temporal generalization rule |

---

## 2. Infrastructure Audit: Per-File Transfer Analysis

### BXCanonical/Chronicle/RRelation.lean (1695 lines) → ~95% transfer rate

**What transfers directly**: The entire r-relation definition, `rRelation_guard_continues'`, deductive closure infrastructure, `rMaximal_extension_exists`, `rMaximalSince_extension_exists`, `r3Maximal_extension_exists`, and all Burgess R3 machinery.

**Bimodal-specific elements**: NONE in proof content. Only:
- Namespace (`Cslib.Logic.Bimodal...`)
- Import paths
- `FrameClass` parameter (temporal has single derivation system — remove this)
- `SetMaximalConsistent fc M` becomes `Temporal.SetMaximalConsistent M`
- `liftBase` helper (unnecessary — no frame class lattice)
- `DerivationTree fc L φ` becomes `temporalDerivationSystem.Deriv L φ` (wrapped in `Nonempty`)

**Mechanical changes only**:
1. Import path rewrite: `Cslib.Logics.Bimodal.X` → `Cslib.Logics.Temporal.X`
2. Remove `FrameClass` parameter everywhere
3. Swap `SetMaximalConsistent fc` → `Temporal.SetMaximalConsistent`
4. Replace bimodal theorem references with temporal equivalents (see prerequisite section)

### BXCanonical/Frame.lean (464 lines) → ~60% transfer rate

**What transfers**:
- `g_content_closed_derivation`, `h_content_closed_derivation`
- `g_content_set_consistent`, `h_content_set_consistent`
- `bx_le_trans`, `bx_forward_witness`, `bx_backward_witness`
- G/H forward/backward propagation

**What does NOT transfer (bimodal-only)**:
- `BXPoint` structure → replace with temporal `TPoint` (Set (Formula Atom) + Temporal.SetMaximalConsistent)
- `bx_modal_equiv` (box equivalence relation) → REMOVE entirely
- `bx_le_refl` sorry (irreflexive semantics issue) → same sorry likely needed

**Key work**: Define `TPoint` as the temporal analogue of `BXPoint`, define `bx_le` (= `g_content w ⊆ v`) for temporal formulas.

### BXCanonical/CanonicalChain.lean (95 lines) → 100% transfer rate

**All content transfers**: `F_imp_top_until_mcs`, `P_imp_top_since_mcs`, `absorb_until_mcs`, `absorb_since_mcs`, delegation bridges — all operate on U/S/F/P only.

**Mechanical changes**: Replace `BXPoint` → `TPoint`, remove `FrameClass.Base`.

### BXCanonical/OrderedSeedConsistency.lean (151 lines) → 100% transfer rate

**All content transfers**: `enriched_resolving_seed_consistent`, `temp_linearity_mcs`, `two_defect_consistent_seed`, `no_new_f_defects`, `resolved_target_in_successor`.

**Mechanical changes only**: Import path rewrite, remove `FrameClass.Base`.

---

## 3. Phase 0 Prerequisites (Critical — Must Create Before Chronicle Port)

The bimodal Chronicle files import Bundle/ infrastructure that does not yet exist in the temporal module. These must be created as Phase 0 deliverables of Task 46.

### 3.1 g_content / h_content definitions

**Source**: `Bundle/TemporalContent.lean` (169 lines)

**Content**: `g_content M := {φ | G(φ) ∈ M}`, `h_content M := {φ | H(φ) ∈ M}`, and similarly `f_content`, `p_content`, `u_content`, `s_content`.

**Note**: The temporal `Completeness.lean` uses `futureSet`/`pastSet` inline. The chronicle construction uses the `g_content`/`h_content` formulation (mathematically equivalent but packaged differently). Create a dedicated `Temporal/Metalogic/TemporalContent.lean` or inline in the chronicle infrastructure.

**Alternative**: Teammate D suggests these could live in `Foundations/Logic/Metalogic/TemporalContent.lean` parameterized over a `HasTemporalOps` typeclass. For Task 46, the simpler approach is to put them in `Temporal/Metalogic/TemporalContent.lean` and refactor to shared in Task 41.

### 3.2 Witness Seed Consistency

**Source**: `Bundle/WitnessSeed.lean` (607 lines)

**Content**: Forward temporal witness seed consistency — sets like `{ψ} ∪ g_content(M)` are consistent when `F(ψ) ∈ M`. Analogous for past. These are foundational for the r-relation construction in Lemma 2.4.

**Key lemmas needed**:
- `forward_seed_consistent : F ψ ∈ M → SetConsistent ({ψ} ∪ g_content M)`
- `past_seed_consistent : P ψ ∈ M → SetConsistent ({ψ} ∪ h_content M)`

### 3.3 SetDeductivelyClosed (DCS) Type

**Source**: `BXCanonical/Chronicle/ChronicleTypes.lean` (within the 386 lines)

**Content**: `SetDeductivelyClosed Γ := ∀ φ, temporalSystem.Deriv Γ φ → φ ∈ Γ` and `mcs_is_dcs : SetMaximalConsistent M → SetDeductivelyClosed M`.

**Note**: This can be created as part of Task 46 even though it logically belongs to ChronicleTypes (Task 47). The r-relation definition depends on DCS.

### 3.4 Propositional Combinators

**Source**: `Theorems/Propositional/Core.lean` (~200 lines in bimodal module)

**Content**: Pairing, `lce_imp`, `rce_imp`, identity, `imp_trans`, contraposition, `efq_axiom`, `double_negation`, De Morgan laws. These are formula-type-agnostic proofs about derivability.

**Target**: Create `Cslib/Logics/Temporal/Theorems/Propositional/Core.lean`. Note: Teammate D suggests these could ultimately live in `Cslib/Foundations/Logic/` — for now, create in Temporal.

**Existing**: The temporal `Completeness.lean` already has `derive_dne` and `derive_h_nec` as private theorems. Promote these and add the missing ones.

### 3.5 Temporal Derived Theorems

**Source**: `Theorems/TemporalDerived.lean` (~150 lines in bimodal module)

**Content**: `temp_k_dist_derived`, `past_necessitation`, `past_k_dist`, and similar derived rules about temporal operators.

**Target**: Create `Cslib/Logics/Temporal/Theorems/TemporalDerived.lean`.

**Existing**: Many of these patterns exist privately in `Temporal/Metalogic/Completeness.lean` (e.g., `mcs_g_trans`, `mcs_h_trans`). Promote these.

---

## 4. Existing Temporal Infrastructure Available

From `Temporal/Metalogic/`:

### MCS.lean (100+ lines) — Already available
- `Temporal.SetConsistent`, `Temporal.SetMaximalConsistent` abbreviations
- `temporal_lindenbaum` (Lindenbaum's lemma) ✓
- `temporal_closed_under_derivation`, `temporal_implication_property`, `temporal_negation_complete` ✓
- `mcs_bot_not_mem`, `mcs_neg_of_not_mem`, `mcs_not_mem_of_neg` ✓
- `futureSet` / `pastSet` definitions ✓
- `mcs_g_witness`, `mcs_h_witness` ✓

### Completeness.lean (418 lines) — Available / partially usable
- `mcs_mp_axiom`, `mcs_top_mem`, `mcs_f_top_mem`, `mcs_p_top_mem` ✓
- `derive_dne` (double negation) ✓
- `derive_h_nec` (H-necessitation) ✓
- `mcs_dne`, `mcs_ff_imp_f`, `mcs_pp_imp_p` ✓
- `mcs_g_trans`, `mcs_h_trans`, `past_of_future_subset`, `future_of_past_subset` ✓
- `CanonicalWorld`, `canonical_acc`, G/H truth lemma ✓
- `exists_future_successor`, `exists_past_predecessor` ✓
- Single `sorry` at line 416 — the target for Task 49

---

## 5. Naming Conventions (from Teammate D)

Use identical names to bimodal to enable clean abstraction in Task 41:

| Bimodal Name | Temporal Name | Notes |
|---|---|---|
| `rRelation` | `rRelation` | Keep identical |
| `rMaximal` | `rMaximal` | Keep identical |
| `rRelationSince` | `rRelationSince` | Keep identical |
| `rMaximalSince` | `rMaximalSince` | Keep identical |
| `chronicle_defect` | `chronicle_defect` | Keep identical (Task 48) |
| `BXPoint` | `TPoint` | Must differ (different MCS types) |
| `bx_le` | `bx_le` (or `t_le`) | Prefer `t_le` for clarity |

**Design principle**: If names match, Task 41 becomes extraction. If names diverge, Task 41 becomes archaeology.

---

## 6. Implementation Strategy

### Recommended Phase Sequence for Task 46

1. **Phase 0a** (~169 lines): Create `Temporal/Metalogic/TemporalContent.lean` with g_content, h_content, f_content, p_content, u_content, s_content.
2. **Phase 0b** (~200 lines): Create `Temporal/Theorems/Propositional/Core.lean` (propositional combinators). Promote existing private theorems from Completeness.lean.
3. **Phase 0c** (~150 lines): Create `Temporal/Theorems/TemporalDerived.lean`. Port from bimodal, reuse from existing Completeness.lean.
4. **Phase 0d** (~607 lines): Create temporal witness seed consistency (inline in `TemporalContent.lean` or separate `WitnessSeed.lean`). Port from `Bundle/WitnessSeed.lean`.
5. **Phase 1**: Create `Chronicle/Frame.lean` — TPoint, t_le, g_content_closed_derivation, G/H forward/backward.
6. **Phase 2**: Create `Chronicle/CanonicalChain.lean` — 100% transfer, pure mechanical rewrite.
7. **Phase 3**: Create `Chronicle/OrderedSeedConsistency.lean` — 100% transfer, pure mechanical rewrite.
8. **Phase 4**: Create `Chronicle/RRelation.lean` — 95% transfer, most complex file.

### Key Simplifications vs Bimodal

- **No FrameClass parameter**: Temporal has a single proof system. Remove `fc : FrameClass` parameter everywhere.
- **No bx_modal_equiv**: The box equivalence relation in `Frame.lean` is entirely absent from temporal.
- **No liftBase**: The frame class lattice structure is absent.
- **Simpler MCS**: `Temporal.SetMaximalConsistent` vs `SetMaximalConsistent fc M`.

---

## 7. Risks and Warnings (from Teammate C)

### Risk 1: Scope Underestimate

The original 800-1,500 line estimate excluded Phase 0 prerequisites (~850-1,000 lines). Revised: **1,200-2,000 lines**.

### Risk 2: g_content/h_content Naming Overlap

The existing `Completeness.lean` uses `futureSet`/`pastSet`. The chronicle uses `g_content`/`h_content`. These are mathematically equivalent. Decision needed: adopt `g_content`/`h_content` naming throughout (for Task 41 alignment), OR adapt the chronicle to use `futureSet`/`pastSet`. Recommendation: use `g_content`/`h_content` in new chronicle files, leave Completeness.lean as-is for now, reconcile in Task 49.

### Risk 3: Open Guard Semantics Sorrys

The bimodal `RRelation.lean` has sorry stubs for "open guard semantics (Task 113 in upstream)". Check whether these sorry stubs are in used lemmas or optional branches. If temporal does not have open guard semantics, these stubs may be eliminated entirely.

### Risk 4: DeductionSystem API Differences

The bimodal chronicle uses `DerivationTree fc L φ` wrapped in `Nonempty`. The temporal side may use a different derivation API. Verify the exact type before starting.

---

## 8. Abstraction Notes (from Teammate D)

### Safe to Do Now (Tier 1)

- **FrameClass unification**: Both logics define identical `FrameClass` inductives — move to `Foundations/Logic/Metalogic/FrameClass.lean` before starting Task 46.
- **g_content typeclass**: Consider defining `g_content` over a `HasTemporalOps F` typeclass so both logics share the definition. Cost: ~2-3 hours. Saves refactoring in Task 41.

### Defer to Task 41 (Tier 2-3)

- r-relation, ordered seed consistency, point insertion — too tightly coupled to port abstractly. Copy-adapt first, abstract in Task 41.

### Name Alignment Recommendation

The biggest win for Task 41 is ensuring temporal and bimodal chronicle use the same conceptual vocabulary. Use `rRelation`, `rMaximal`, `chronicle_defect`, `insert_point`, `counterexample_eliminated` throughout.

---

## 9. Relevant Codebase Paths

### Source Files (bimodal — adapt from these)
```
Cslib/Logics/Bimodal/Metalogic/BXCanonical/
├── Chronicle/RRelation.lean         (1695 lines — primary source for Task 46 Phase 4)
├── Frame.lean                       (464 lines — primary source for Task 46 Phase 1)
├── CanonicalChain.lean              (95 lines — primary source for Task 46 Phase 2)
└── OrderedSeedConsistency.lean      (151 lines — primary source for Task 46 Phase 3)

Cslib/Logics/Bimodal/Metalogic/Bundle/
├── TemporalContent.lean             (169 lines — source for Phase 0a)
└── WitnessSeed.lean                 (607 lines — source for Phase 0d)

Cslib/Logics/Bimodal/Theorems/
├── Propositional/Core.lean          (source for Phase 0b)
└── TemporalDerived.lean             (source for Phase 0c)
```

### Target Files (temporal — create these)
```
Cslib/Logics/Temporal/Metalogic/
├── TemporalContent.lean             (new — Phase 0a, ~169 lines)
└── Chronicle/
    ├── Frame.lean                   (new — Phase 1, ~200-300 lines)
    ├── CanonicalChain.lean          (new — Phase 2, ~50-70 lines)
    ├── OrderedSeedConsistency.lean  (new — Phase 3, ~80-100 lines)
    └── RRelation.lean               (new — Phase 4, ~600-900 lines)

Cslib/Logics/Temporal/Theorems/
├── Propositional/Core.lean          (new — Phase 0b, ~200 lines)
└── TemporalDerived.lean             (new — Phase 0c, ~150 lines)
```

### Existing Infrastructure (use, do not modify)
```
Cslib/Logics/Temporal/Metalogic/
├── MCS.lean                         (Lindenbaum, MCS properties — use as-is)
├── DeductionTheorem.lean            (use as-is)
└── Completeness.lean                (418 lines — use CanonicalWorld, mcs_g_trans, etc.)
```

---

## References

- Burgess 1982, Section 2, Lemmas 2.2-2.5
- Xu 1988, Definition 2.5 (cleaner C0-C6 formulation for Lean target)
- Blackburn/de Rijke/Venema 2002, Theorem 7.15 (completeness target)
- `specs/050_burgess_prior_art_seed_research/reports/01_team-research.md` (synthesized research)
- `specs/050_burgess_prior_art_seed_research/reports/01_teammate-a-findings.md` (Burgess literature)
- `specs/050_burgess_prior_art_seed_research/reports/01_teammate-b-findings.md` (infrastructure audit)
- `specs/050_burgess_prior_art_seed_research/reports/01_teammate-c-findings.md` (critic: gaps/risks)
- `specs/050_burgess_prior_art_seed_research/reports/01_teammate-d-findings.md` (abstraction strategy)
