# Research Report: Task 21 -- Modal Proof System and Theorems

**Task**: 21 -- Port modal proof system and theorems
**Date**: 2026-06-08
**Session**: sess_1780970224_ba1435_21
**Builds on**: 01_seed-research.md (Task 19 findings)

---

## 1. Executive Summary

Task 21 ports modal proof infrastructure from BimodalLogic to cslib. The core deliverables are:
1. Modal-specific derived theorems (box_mono, diamond_mono, k_dist_diamond, etc.) expressed generically over `[ModalHilbert S]` and `[ModalS5Hilbert S]`
2. S5-specific theorems (t_box_to_diamond, box_contrapose, box_conj_iff, s5_diamond_box, etc.)
3. S4-specific theorems (s4_diamond_box_conj, s4_diamond_box_diamond, etc.)
4. Generalized necessitation for the modal operator

The key insight is that cslib already has a well-designed typeclass hierarchy (`ModalHilbert`, `ModalS5Hilbert`) with polymorphic axiom definitions, but NO concrete derivation trees and NO modal-level theorems. Task 21 fills this gap entirely within the typeclass framework -- no concrete `DerivationTree` inductive is needed. All theorems are stated and proved generically using `InferenceSystem.DerivableIn`.

**Estimated scope**: ~1,200-1,400 lines of new Lean code across 4-5 files.

---

## 2. Source Analysis: BimodalLogic Files

### 2.1 Files Containing Purely Modal Content

| Source File | Lines | Modal Content | Temporal Content |
|------------|-------|---------------|------------------|
| `Theorems/ModalS5.lean` | 859 | 100% modal | None |
| `Theorems/ModalS4.lean` | 468 | 100% modal | None |
| `Theorems/GeneralizedNecessitation.lean` | 240 | `generalized_modal_k` only | `generalized_temporal_k`, `generalized_past_k` |
| `Theorems/Perpetuity/Bridge.lean` | 993 | `box_mono`, `diamond_mono`, `modal_duality_*` | `future_mono`, `past_mono`, temporal duality |
| `Theorems/Perpetuity/Principles.lean` | 900 | `contraposition`, `diamond_4`, `modal_5` | Perpetuity P1-P6 |
| `Theorems/Combinators.lean` | ~300 | None (already ported in Task 20) | None |
| `Theorems/Propositional/*` | ~600 | None (already ported in Task 20) | None |

### 2.2 What Gets Ported vs What Stays

**Port to cslib (Task 21 scope)**:
- `box_mono`, `diamond_mono` (from Bridge.lean)
- `modal_duality_neg`, `modal_duality_neg_rev` (from Bridge.lean)
- `box_dne`, `double_contrapose` (from Bridge.lean)
- `contraposition` (from Principles.lean, but already done in Task 20 as `contrapose_imp`/`contraposition`)
- `diamond_4`, `modal_5` (from Principles.lean)
- All of `ModalS5.lean` (t_box_to_diamond, box_disj_intro, box_contrapose, k_dist_diamond, box_iff_intro, t_box_consistency, box_conj_iff, diamond_disj_iff, s5_diamond_box, s5_diamond_box_to_truth)
- All of `ModalS4.lean` (s4_diamond_box_conj, s4_box_diamond_box, s4_diamond_box_diamond, s5_diamond_conj_diamond)
- `generalized_modal_k` from GeneralizedNecessitation.lean (modal portion only)

**Stays in BimodalLogic (NOT ported)**:
- `future_mono`, `past_mono`, `always_mono` (temporal)
- Temporal duality lemmas (temporal)
- `generalized_temporal_k`, `generalized_past_k` (temporal)
- Perpetuity principles P1-P6 (temporal-modal interaction)
- `bridge1`, `bridge2` (temporal-modal interaction)

---

## 3. Target Architecture in cslib

### 3.1 Existing cslib Infrastructure

**Typeclass hierarchy** (in `Cslib/Foundations/Logic/ProofSystem.lean`):
```
PropositionalHilbert S
  extends ModusPonens, HasAxiomImplyK, HasAxiomImplyS, HasAxiomEFQ, HasAxiomPeirce

ModalHilbert S
  extends PropositionalHilbert, Necessitation, HasAxiomK

ModalS5Hilbert S
  extends ModalHilbert, HasAxiomT, HasAxiom4, HasAxiomB
```

**Polymorphic axiom definitions** (in `Cslib/Foundations/Logic/Axioms.lean`):
- `Axioms.AxiomK`, `Axioms.AxiomT`, `Axioms.Axiom4`, `Axioms.AxiomB`, `Axioms.Axiom5`, `Axioms.AxiomD`
- All defined using `HasBot`, `HasImp`, `HasBox` typeclasses

**Connective typeclasses** (in `Cslib/Foundations/Logic/Connectives.lean`):
- `HasBot`, `HasImp`, `HasBox` (and temporal: `HasUntil`, `HasSince`)
- `ModalConnectives extends PropositionalConnectives, HasBox`

**Propositional theorems** (from Task 20, in `Cslib/Foundations/Logic/Theorems/`):
- `Combinators.lean`: imp_trans, identity, b_combinator, theorem_flip, theorem_app1, theorem_app2, pairing, dni, combine_imp_conj, combine_imp_conj_3
- `Propositional/Core.lean`: efq_axiom, peirce_axiom, double_negation, raa, efq_neg, rcp, lce_imp, rce_imp, lem
- `Propositional/Connectives.lean`: contrapose_imp, contraposition, classical_merge, iff_intro, contrapose_iff, iff_neg_intro, demorgan_conj_neg_forward/backward, demorgan_disj_neg_forward/backward
- `Propositional/Reasoning.lean`: bi_imp
- `BigConj.lean`: bigconj operations

**Modal semantics** (in `Cslib/Logics/Modal/`):
- `Basic.lean`: Model, Proposition, Satisfies, semantic validity (K, T, B, 4, 5, D axiom soundness)
- `Cube.lean`: Modal logic cube definitions
- `Denotation.lean`: Denotational semantics

**Tag types** (in `ProofSystem.lean`):
- `Modal.HilbertK`, `Modal.HilbertS5` (opaque, uninstantiated)

**What is MISSING (Task 21 fills)**:
- No modal-level derived theorems (box_mono, diamond_mono, etc.)
- No S4/S5 specific theorems
- No InferenceSystem instance for any modal tag type
- No generalized necessitation

### 3.2 Proposed File Layout

```
Cslib/Foundations/Logic/Theorems/
├── Combinators.lean              # [EXISTS] (Task 20)
├── Propositional/                # [EXISTS] (Task 20)
│   ├── Core.lean
│   ├── Connectives.lean
│   └── Reasoning.lean
├── BigConj.lean                  # [EXISTS] (Task 20)
├── Modal/                        # [NEW - Task 21]
│   ├── Basic.lean                # box_mono, diamond_mono, k_dist_diamond, box_contrapose
│   ├── S5.lean                   # S5-specific: t_box_to_diamond, box_conj_iff, s5_diamond_box, ...
│   ├── S4.lean                   # S4-specific: s4_diamond_box_conj, s4_diamond_box_diamond, ...
│   └── GeneralizedNecessitation.lean  # generalized_modal_k (requires deduction theorem)
└── Theorems.lean                 # [EXISTS] - update to import Modal/
```

**Rationale for this layout**:
1. Keeps modal theorems in `Foundations/Logic/Theorems/Modal/` (alongside propositional theorems), NOT in `Logics/Modal/` (which houses semantics). This follows the pattern that `Foundations/Logic/` contains the proof system infrastructure while `Logics/` contains semantics.
2. `Modal/Basic.lean` contains theorems generic over `[ModalHilbert S]` (K-level).
3. `Modal/S5.lean` contains theorems requiring `[ModalS5Hilbert S]`.
4. `Modal/S4.lean` contains theorems requiring S4 axioms (T + 4, a subset of S5).
5. `GeneralizedNecessitation.lean` is separate because it requires a deduction theorem.

### 3.3 Alternative: No GeneralizedNecessitation

The `generalized_modal_k` theorem from BimodalLogic depends on the deduction theorem (`Bimodal.Metalogic.Core.DeductionTheorem`), which is a complex metalogical result tied to BimodalLogic's concrete `DerivationTree`. In the typeclass-generic setting of cslib, there is no deduction theorem available.

**Options**:
1. **Skip GeneralizedNecessitation** -- It is primarily used in the bimodal metalogic (MCS, completeness), not in the derived modal theorems. The ModalS4/S5 theorems do NOT depend on it.
2. **Add a `HasDeductionTheorem` typeclass** -- This would enable generic generalized necessitation but adds complexity.
3. **Defer to Task 7** (Bimodal MCS/Deduction), which is where the deduction theorem naturally lives.

**Recommendation**: Option 1 (skip). The ModalS4/S5 theorems are self-contained and do not require generalized necessitation. This can be added later when a concrete derivation tree is registered.

---

## 4. Theorem Inventory and Dependencies

### 4.1 Modal/Basic.lean -- Generic `[ModalHilbert S]` Theorems

These require only K axiom + necessitation (no T, 4, B):

| Theorem | Signature | Source | Dependencies |
|---------|-----------|--------|-------------|
| `box_mono` | `⊢ (φ → ψ) → ⊢ (□φ → □ψ)` | Bridge.lean:151 | Necessitation, HasAxiomK |
| `diamond_mono` | `⊢ (φ → ψ) → ⊢ (◇φ → ◇ψ)` | Bridge.lean:161 | box_mono, contraposition |
| `box_contrapose` | `⊢ □(φ → ψ) → □(¬ψ → ¬φ)` | ModalS5.lean:251 | box_mono, b_combinator, theorem_flip |
| `k_dist_diamond` | `⊢ □(φ → ψ) → (◇φ → ◇ψ)` | ModalS5.lean:299 | box_contrapose, HasAxiomK, contrapose_imp |
| `modal_duality_neg` | `⊢ ◇¬φ → ¬□φ` | Bridge.lean:82 | dni, box_mono (via K), contraposition |
| `modal_duality_neg_rev` | `⊢ ¬□φ → ◇¬φ` | Bridge.lean:116 | double_negation, box_mono (via K), contraposition |

### 4.2 Modal/S5.lean -- `[ModalS5Hilbert S]` Theorems

| Theorem | Signature | Source | Extra Axioms Used |
|---------|-----------|--------|-------------------|
| `t_box_to_diamond` | `⊢ □φ → ◇φ` | ModalS5.lean:105 | HasAxiomT |
| `box_disj_intro` | `⊢ (□φ ∨ □ψ) → □(φ ∨ ψ)` | ModalS5.lean:186 | box_mono, classical_merge |
| `t_box_consistency` | `⊢ ¬□(φ ∧ ¬φ)` | ModalS5.lean:397 | HasAxiomT |
| `box_iff_intro` | `⊢ (φ ↔ ψ) → ⊢ (□φ ↔ □ψ)` | ModalS5.lean:362 | box_mono, lce_imp, rce_imp |
| `box_conj_iff` | `⊢ □(φ ∧ ψ) ↔ (□φ ∧ □ψ)` | ModalS5.lean:497 | HasAxiomK, box_mono, pairing |
| `diamond_disj_iff` | `⊢ ◇(φ ∨ ψ) ↔ (◇φ ∨ ◇ψ)` | ModalS5.lean:604 | box_conj_iff, demorgan, contraposition |
| `diamond_4` | `⊢ ◇◇φ → ◇φ` | Principles.lean:236 | HasAxiomT, HasAxiom4 (S4 characteristic) |
| `modal_5` | `⊢ ◇φ → □◇φ` | Principles.lean:331 | HasAxiomB, HasAxiom4 |
| `s5_diamond_box` | `⊢ ◇□φ ↔ □φ` | ModalS5.lean:788 | HasAxiom4, modal_5_collapse |
| `s5_diamond_box_to_truth` | `⊢ ◇□φ → φ` | ModalS5.lean:848 | modal_5_collapse, HasAxiomT |

**Note on axiom dependencies**: The BimodalLogic axiom system has `modal_5_collapse` (◇□φ → □φ) as a primitive axiom. In cslib's ModalS5Hilbert, the axioms are T + 4 + B (no explicit 5 or 5_collapse). We need to either:
- Derive `modal_5_collapse` from T + 4 + B (standard modal logic result), or
- Add `HasAxiom5` to ModalS5Hilbert

**Analysis**: In standard modal logic, axiom 5 (◇φ → □◇φ) is derivable from B + 4. And modal_5_collapse (◇□φ → □φ) is derivable from T + 5. So in the S5 system (T + 4 + B), both are derivable. This is the correct approach for cslib.

### 4.3 Modal/S4.lean -- Theorems Using S4 Axioms (T + 4)

| Theorem | Signature | Source | Extra Axioms |
|---------|-----------|--------|-------------|
| `s4_diamond_box_conj` | `⊢ (◇A ∧ □B) → ◇(A ∧ □B)` | ModalS4.lean:64 | T, 4 |
| `s4_box_diamond_box` | `⊢ □A → □(◇□A)` | ModalS4.lean:156 | B (uses modal_b directly) |
| `s4_diamond_box_diamond` | `⊢ ◇(□(◇A)) ↔ ◇A` | ModalS4.lean:179 | 4, 5_collapse (derived) |
| `s5_diamond_conj_diamond` | `⊢ ◇(A ∧ ◇B) ↔ (◇A ∧ ◇B)` | ModalS4.lean:310 | 5, diamond_4 |

**Note**: Despite the filename "ModalS4", several theorems in this file actually use S5-specific axioms (B, 5_collapse). In cslib, these should all go into Modal/S5.lean since they require `[ModalS5Hilbert S]`.

---

## 5. Key Design Decisions

### 5.1 Generic Typeclass Approach (No Concrete DerivationTree)

The seed research report suggested creating a concrete `Modal.DerivationTree` inductive type. After deeper analysis, this is **not necessary** and would be counterproductive.

**Rationale**:
1. cslib already has the typeclass hierarchy (`ModalHilbert`, `ModalS5Hilbert`) designed for exactly this purpose.
2. All BimodalLogic theorems in ModalS4/S5 use only: modus ponens, necessitation, K axiom, T/4/B axiom instances, and propositional combinators. These are all available through the typeclasses.
3. Creating a concrete `DerivationTree` would require instantiating it as the InferenceSystem for Modal.Proposition, which is a separate concern (tag type registration).
4. The generic approach means the theorems are reusable by ANY system satisfying `[ModalHilbert S]` or `[ModalS5Hilbert S]` -- including both Modal and Bimodal logics.

**Translation pattern** from BimodalLogic to cslib:
```lean
-- BimodalLogic (concrete DerivationTree):
def box_mono {A B : Formula} (h : ⊢ A.imp B) : ⊢ A.box.imp B.box := by
  have box_h := DerivationTree.necessitation _ h
  have mk := DerivationTree.axiom [] _ (Axiom.modal_k_dist A B) trivial
  exact DerivationTree.modus_ponens [] _ _ mk box_h

-- cslib (generic typeclass):
theorem box_mono {φ ψ : F}
    (h : InferenceSystem.DerivableIn S (HasImp.imp φ ψ)) :
    InferenceSystem.DerivableIn S (HasImp.imp (HasBox.box φ) (HasBox.box ψ)) := by
  have box_h := Necessitation.nec h
  have mk := HasAxiomK.K (S := S) (φ := φ) (ψ := ψ)
  exact ModusPonens.mp mk box_h
```

### 5.2 Axiom 5 Derivation

The BimodalLogic system has `modal_5_collapse` (◇□φ → □φ) as a primitive axiom. In cslib's `ModalS5Hilbert`, the axioms are T + 4 + B. We need to derive both axiom 5 and its "collapse" variant.

**Derivation of axiom 5 (◇φ → □◇φ) from B + 4**:
1. B axiom: φ → □◇φ
2. Apply to ◇φ: ◇φ → □◇◇φ
3. From T + 4, derive ◇◇φ → ◇φ (diamond_4)
4. Apply box_mono: □◇◇φ → □◇φ
5. Compose: ◇φ → □◇φ

**Derivation of 5_collapse (◇□φ → □φ) from T + 4 + B**:
1. First derive axiom 5 as above
2. T axiom: □φ → φ
3. Contrapose: ¬φ → ¬□φ (i.e., ¬φ → ◇¬φ with duality)
4. Apply axiom 5 to ¬φ: ◇¬φ → □◇¬φ
5. Contrapose ◇¬φ → □◇¬φ to get ◇□φ → □φ (by duality)

This is standard modal logic. The cslib theorems should derive these as early results in Modal/S5.lean.

### 5.3 Diamond Definition Compatibility

In cslib's `Modal.Proposition`: `diamond φ := neg (box (neg φ))` where `neg φ := imp φ bot`.

In BimodalLogic's `Formula`: `diamond φ := φ.neg.box.neg` (same pattern).

Both encode `◇φ = ¬□¬φ` using the Lukasiewicz convention. Since the cslib theorems are generic over `HasBot`/`HasImp`/`HasBox`, diamond is not a primitive -- it must be built using `HasImp.imp (HasBox.box (HasImp.imp φ HasBot.bot)) HasBot.bot`. This matches the approach in BimodalLogic.

### 5.4 Noncomputability

Most modal theorems in BimodalLogic use `noncomputable` due to DNE (Peirce + EFQ) and `classical_merge`. The cslib propositional theorems (Task 20) are already `noncomputable`. The modal theorems will follow the same pattern.

---

## 6. Structural Challenges

### 6.1 Formula Encoding Without `abbrev` Access

The cslib generic theorems use raw `HasImp.imp`/`HasBot.bot`/`HasBox.box` instead of `abbrev` connectives like `.and`, `.or`, `.diamond`, `.neg`. This makes the type signatures more verbose but is necessary for polymorphism.

**Mitigation**: Define local abbreviations at the top of each file:
```lean
-- Local abbreviations for readability
local notation "¬" φ => HasImp.imp φ HasBot.bot
local notation "□" φ => HasBox.box φ
local notation "◇" φ => HasImp.imp (HasBox.box (HasImp.imp φ HasBot.bot)) HasBot.bot
```

### 6.2 Deduction Theorem Dependency

`generalized_modal_k` requires a deduction theorem. In BimodalLogic this is a 500+ line file using well-founded recursion on `DerivationTree.height`. Since cslib doesn't have concrete derivation trees, this cannot be ported directly.

**Resolution**: Skip generalized necessitation. It is used in:
- Metalogic (MCS, completeness proofs) -- not in scope for Task 21
- Perpetuity principles P1-P6 -- temporal, not in scope

The ModalS4/S5 theorems do NOT depend on generalized necessitation. They use only:
- Standard necessitation (`Necessitation.nec`)
- Modus ponens (`ModusPonens.mp`)
- Axiom instances

### 6.3 `contraposition` and `contrapose_imp` Already Exist

BimodalLogic's `contraposition` (from `⊢ A → B`, derive `⊢ ¬B → ¬A`) and `contrapose_imp` (`⊢ (A → B) → (¬B → ¬A)`) are both already ported to cslib in Task 20:
- `Cslib.Logic.Theorems.Propositional.Connectives.contraposition`
- `Cslib.Logic.Theorems.Propositional.Connectives.contrapose_imp`

### 6.4 Missing `HasAxiom5` in ModalS5Hilbert

cslib's `ModalS5Hilbert` extends `ModalHilbert` with `HasAxiomT`, `HasAxiom4`, `HasAxiomB`. It does NOT include `HasAxiom5` (◇φ → □◇φ), which BimodalLogic has as `modal_5_collapse` (the related but distinct ◇□φ → □φ).

Since axiom 5 is derivable from B + 4, this is correct -- no change to the typeclass is needed. But the derivation should be an early theorem in Modal/S5.lean.

---

## 7. Theorem-by-Theorem Translation Plan

### Phase 1: Modal/Basic.lean (~250 lines)

Generic over `[ModalHilbert S]` (K + necessitation):

1. `box_mono`: From `⊢ φ → ψ`, derive `⊢ □φ → □ψ` (uses Necessitation + K)
2. `diamond_mono`: From `⊢ φ → ψ`, derive `⊢ ◇φ → ◇ψ` (uses box_mono + contraposition)
3. `box_contrapose`: `⊢ □(φ → ψ) → □(¬ψ → ¬φ)` (uses box_mono + b_combinator)
4. `k_dist_diamond`: `⊢ □(φ → ψ) → (◇φ → ◇ψ)` (uses box_contrapose + K + contrapose_imp)
5. `modal_duality_neg`: `⊢ ◇¬φ → ¬□φ` (uses dni + box_mono + contraposition)
6. `modal_duality_neg_rev`: `⊢ ¬□φ → ◇¬φ` (uses double_negation + box_mono + contraposition)
7. `box_iff_intro`: From `⊢ φ ↔ ψ`, derive `⊢ □φ ↔ □ψ` (uses box_mono + iff_intro)

### Phase 2: Modal/S5.lean (~600-800 lines)

Generic over `[ModalS5Hilbert S]`:

**Early derivations** (axiom 5 and 5_collapse):
1. `axiom5_derived`: `⊢ ◇φ → □◇φ` (from B + 4 + box_mono)
2. `axiom5_collapse_derived`: `⊢ ◇□φ → □φ` (from 5 + T + duality)

**Core S5 theorems**:
3. `t_box_to_diamond`: `⊢ □φ → ◇φ` (T + raa)
4. `diamond_4`: `⊢ ◇◇φ → ◇φ` (T + 4 via duality)
5. `t_box_consistency`: `⊢ ¬□(φ ∧ ¬φ)` (T + dni)
6. `box_disj_intro`: `⊢ (□φ ∨ □ψ) → □(φ ∨ ψ)` (box_mono + classical_merge)
7. `box_conj_iff`: `⊢ □(φ ∧ ψ) ↔ (□φ ∧ □ψ)` (K + box_mono + pairing)
8. `diamond_disj_iff`: `⊢ ◇(φ ∨ ψ) ↔ (◇φ ∨ ◇ψ)` (box_conj_iff + demorgan)
9. `s5_diamond_box`: `⊢ ◇□φ ↔ □φ` (4 + t_box_to_diamond + 5_collapse)
10. `s5_diamond_box_to_truth`: `⊢ ◇□φ → φ` (5_collapse + T)

**S4-level theorems** (T + 4 only, but stated under S5):
11. `s4_diamond_box_conj`: `⊢ (◇A ∧ □B) → ◇(A ∧ □B)` (4 + k_dist_diamond)
12. `s4_box_diamond_box`: `⊢ □A → □(◇□A)` (B directly)
13. `s4_diamond_box_diamond`: `⊢ ◇(□(◇A)) ↔ ◇A` (5 + 4 + T)
14. `s5_diamond_conj_diamond`: `⊢ ◇(A ∧ ◇B) ↔ (◇A ∧ ◇B)` (5 + diamond_4)

### Phase 3: Aggregator Update (~10 lines)

Update `Cslib/Foundations/Logic/Theorems.lean` to import the new Modal files.

---

## 8. Dependency Graph

```
Combinators.lean (Task 20)
    │
    ├── Propositional/Core.lean (Task 20)
    │       │
    │       └── Propositional/Connectives.lean (Task 20)
    │               │
    │               └── Modal/Basic.lean [NEW]     -- [ModalHilbert S]
    │                       │
    │                       └── Modal/S5.lean [NEW]  -- [ModalS5Hilbert S]
    │
    └── BigConj.lean (Task 20)
```

---

## 9. Risk Assessment

### Low Risk
- **Propositional foundation is solid**: All required propositional combinators (imp_trans, b_combinator, theorem_flip, pairing, contrapose_imp, classical_merge, demorgan, iff_intro, etc.) are already proven in Task 20.
- **Translation is mechanical**: Each theorem from BimodalLogic maps directly to the typeclass framework.

### Medium Risk
- **Axiom 5 derivation from B + 4**: This is standard modal logic but requires careful proof engineering. The derivation chain is: B applied to ◇φ gives ◇φ → □◇◇φ, then diamond_4 gives ◇◇φ → ◇φ, then box_mono gives □◇◇φ → □◇φ, compose to get ◇φ → □◇φ. However, diamond_4 itself requires T + 4, creating a proof ordering dependency.
- **Verbose type signatures**: Without `abbrev` access, diamond formulas expand to `HasImp.imp (HasBox.box (HasImp.imp φ HasBot.bot)) HasBot.bot`. This affects readability but not correctness.

### Low Risk (Mitigated)
- **DecidableEq dependency**: Task 16 completed this, so `DecidableEq` on `Modal.Proposition` is available. However, the generic modal theorems don't actually need it -- they work at the typeclass level.

---

## 10. Relationship to Other Tasks

| Task | Relationship |
|------|-------------|
| **Task 16** (DecidableEq) | **Dependency (completed)**. Not directly used by generic theorems, but needed if concrete derivation trees are added later. |
| **Task 20** (Propositional Theorems) | **Dependency (completed)**. Provides all propositional combinators used by modal theorems. |
| **Task 5** (Bimodal Derived Theorems) | **Downstream**. After Task 21, bimodal theorems can import modal theorems instead of duplicating. |
| **Task 7** (Bimodal MCS/Deduction) | **Related**. Generalized necessitation and deduction theorem live here, not in Task 21. |
| **Task 28** (Structure Metalogic Across Systems) | **Related**. Task 21's generic typeclass approach supports Task 28's goal of shared infrastructure. |

---

## 11. Mathlib Contribution Assessment

The modal theorem files would be a strong Mathlib contribution candidate:
- Generic over typeclasses (not tied to a specific formula type)
- Well-structured (K-level vs S5-level theorems)
- Complements existing cslib Modal semantics (Basic.lean, Cube.lean)
- Standard results with clear mathematical content

---

## 12. Recommendations

1. **Proceed with generic typeclass approach** -- No concrete DerivationTree needed.
2. **Skip GeneralizedNecessitation** -- Not needed by any S4/S5 theorem; defer to Task 7.
3. **Derive axiom 5 early** in Modal/S5.lean as a foundation for other S5 theorems.
4. **Keep all "S4" theorems in Modal/S5.lean** since they use S5 axioms (B, 5_collapse) despite their BimodalLogic filename.
5. **Use local notation** to manage verbose type signatures.
6. **Estimated effort**: 3-4 phases, ~1,200-1,400 lines total.
