# Research Report: Generic MCS Foundations

**Task**: 29 - Generic MCS foundations
**Session**: sess_1749361200_a3f2c1
**Date**: 2026-06-08

## 1. Existing MCS Code in BimodalLogic

The BimodalLogic project (`/home/benjamin/Projects/BimodalLogic/`) contains a mature, battle-tested MCS implementation hardcoded to the bimodal `Formula` and `DerivationTree` types. Key files:

### Core MCS Theory

| File | Lines | Key Definitions |
|------|-------|-----------------|
| `Theories/Bimodal/Metalogic/Core/MaximalConsistent.lean` | 528 | `Consistent`, `MaximalConsistent`, `SetConsistent`, `SetMaximalConsistent`, `ConsistentExtensions`, `ConsistentSupersets`, `finite_list_in_chain_member`, `consistent_chain_union`, `set_lindenbaum`, `maximal_consistent_closed`, `maximal_negation_complete`, `theorem_in_mcs` |
| `Theories/Bimodal/Metalogic/Core/MCSProperties.lean` | 367 | `SetMaximalConsistent.closed_under_derivation`, `SetMaximalConsistent.implication_property`, `SetMaximalConsistent.negation_complete`, `set_consistent_not_both`, `SetMaximalConsistent.neg_excludes`, temporal-specific properties (`all_future_all_future`, `all_past_all_past`) |
| `Theories/Bimodal/Metalogic/Core/DeductionTheorem.lean` | 441 | `deduction_theorem`, `deduction_with_mem`, helper lemmas |
| `Theories/Bimodal/Metalogic/Core/RestrictedMCS/Basic.lean` | 653 | `RestrictedMCS`, `RestrictedConsistent`, `restricted_lindenbaum`, closure-specific properties |
| `Theories/Bimodal/ProofSystem/Derivable.lean` | 222 | `Derivable` Prop-wrapper, aesop/simp integration |

### What is Generic vs Logic-Specific

**Generic (can be abstracted)** -- approximately 60% of the MCS theory:
- `SetConsistent` definition (parametrized over derivation relation)
- `SetMaximalConsistent` definition
- `ConsistentExtensions` / `ConsistentSupersets`
- `finite_list_in_chain_member` (pure set/chain theory)
- `consistent_chain_union` (uses only SetConsistent)
- `set_lindenbaum` (Zorn application, uses only chain union + SetConsistent)
- `base_mem_consistent_extensions` / `self_mem_consistent_supersets`
- `set_consistent_not_both` (uses only modus ponens structure)

**Logic-specific (requires deduction theorem)** -- approximately 40%:
- `maximal_consistent_closed` / `closed_under_derivation` -- needs deduction theorem
- `maximal_negation_complete` / `negation_complete` -- needs deduction theorem
- `implication_property` -- needs deduction theorem (via closed_under_derivation)
- `theorem_in_mcs` -- needs deduction theorem
- `derives_neg_from_inconsistent_extension` -- IS the deduction theorem application
- Temporal-specific: `all_future_all_future`, `all_past_all_past`, `temp_4_past`
- Restricted MCS: `RestrictedMCS`, `restricted_lindenbaum` (logic-specific closure)

### Critical Insight: The Deduction Theorem Boundary

The key architectural boundary is the deduction theorem. Looking at how the proofs work:

1. `closed_under_derivation` proves: if `L ⊆ S` and `L ⊢ φ`, then `φ ∈ S`. The proof proceeds by contradiction: assume `φ ∉ S`, then `insert φ S` is inconsistent, meaning some `L' ⊆ insert φ S` derives `⊥`. If `φ ∈ L'`, the deduction theorem extracts `L' \ {φ} ⊢ ¬φ`, which combined with `L ⊢ φ` yields a contradiction.

2. `implication_property` and `negation_complete` both reduce to `closed_under_derivation`.

3. The deduction theorem itself is proven by structural induction on derivation trees, which is inherently logic-specific (it must handle each rule: axioms, assumptions, modus ponens, necessitation, weakening, etc.).

**However**, the task description says to include `closed_under_derivation` and `implication_property` in the generic module. This is achievable if we:
- Parameterize over a `DeductionTheorem` hypothesis (as a field in a typeclass or structure)
- The generic module states these lemmas with the deduction theorem as an assumption
- Per-logic instances supply the actual deduction theorem proof

## 2. Existing cslib Infrastructure

### Relevant Foundations

| File | Purpose |
|------|---------|
| `Cslib/Foundations/Logic/InferenceSystem.lean` | `InferenceSystem S F` typeclass with `derivation` and `DerivableIn` |
| `Cslib/Foundations/Logic/ProofSystem.lean` | `PropositionalHilbert`, `ModalHilbert`, `TemporalBXHilbert`, `BimodalTMHilbert` bundled classes |
| `Cslib/Foundations/Logic/Connectives.lean` | `HasBot`, `HasImp`, `HasBox`, `HasUntil`, `HasSince` typeclasses |
| `Cslib/Foundations/Logic/Axioms.lean` | Axiom schema definitions |
| `Cslib/Foundations/Logic/Theorems/Combinators.lean` | `identity`, `imp_trans`, etc. over `PropositionalHilbert` |

### Temporal Logic Already in cslib

| File | Purpose |
|------|---------|
| `Cslib/Logics/Temporal/ProofSystem/Derivation.lean` | `DerivationTree fc Gamma phi` inductive type |
| `Cslib/Logics/Temporal/ProofSystem/Derivable.lean` | `Temporal.Derivable` Prop-wrapper |
| `Cslib/Logics/Temporal/ProofSystem/Axioms.lean` | Axiom schemata + `FrameClass` |
| `Cslib/Logics/Temporal/Syntax/Context.lean` | `Context Atom := List (Formula Atom)` |

### What Does NOT Exist Yet

- No `Cslib/Foundations/Logic/Metalogic/` directory
- No `Consistency.lean` or any MCS-related definitions
- No deduction theorem for any logic in cslib
- The `InferenceSystem` typeclass works at the **theorem level** (empty context / `DerivableIn`), not at the **context-derivability level** needed for MCS theory

### Gap Analysis

The existing `InferenceSystem` typeclass in cslib defines `DerivableIn S a` as `Nonempty (S ⇓ a)`, where derivation is from empty context. MCS theory needs **context-based** derivation: `Gamma ⊢ phi` where `Gamma` is a set/list of assumptions. The BimodalLogic codebase uses `DerivationTree fc Gamma phi` directly.

For the generic MCS module, we need to abstract over a binary relation `Deriv : Set F -> F -> Prop` (or equivalently `List F -> F -> Prop`) that represents "the set/list of assumptions derives the formula."

## 3. Mathlib Dependencies

### Available and Needed

| Mathlib Module | Key Definitions | Status |
|----------------|-----------------|--------|
| `Mathlib.Order.Zorn` | `zorn_subset_nonempty`, `zorn_subset` | Available, exact API used in BimodalLogic |
| `Mathlib.Order.Preorder.Chain` | `IsChain`, `IsChain.total`, `IsChain.mono` | Available |
| `Mathlib.Order.Defs.Unbundled` | `Maximal` predicate | Available |
| `Mathlib.Order.Minimal` | `maximal_subset_iff`, `maximal_subset_iff'` | Available |
| `Mathlib.Data.Set.Basic` | `Set.sUnion`, `Set.subset_sUnion_of_mem`, `Set.mem_sUnion`, `Set.mem_insert_iff` | Available |

### Key Mathlib Signatures

```
zorn_subset_nonempty :
  ∀ {α} (S : Set (Set α)),
  (∀ c ⊆ S, IsChain (· ⊆ ·) c → c.Nonempty → ∃ ub ∈ S, ∀ s ∈ c, s ⊆ ub) →
  ∀ x ∈ S, ∃ m, x ⊆ m ∧ Maximal (· ∈ S) m

IsChain : {α : Type*} → (α → α → Prop) → Set α → Prop
-- IsChain r S means any two distinct elements of S are related by r

Maximal : {α : Type*} → [LE α] → (α → Prop) → α → Prop
-- Maximal P x means P x ∧ ∀ y, P y → x ≤ y → x = y (for sets: P x ∧ ∀ y, P y → x ⊆ y → x = y)
```

## 4. Proposed Abstraction Design

### Design Decision: How to Parameterize

There are three options for parameterizing over the derivation relation:

**Option A: Structure with derivation relation as field**
```lean
structure DerivationSystem (F : Type*) where
  Deriv : List F → F → Prop
  weakening : ∀ {Γ Δ φ}, Deriv Γ φ → (∀ x ∈ Γ, x ∈ Δ) → Deriv Δ φ
  mp : ∀ {Γ φ ψ}, Deriv Γ (imp φ ψ) → Deriv Γ φ → Deriv Γ ψ
```

**Option B: Typeclass with derivation relation**
```lean
class HasContextDerivation (F : Type*) where
  ContextDeriv : List F → F → Prop
  ...
```

**Option C: Plain variable with axioms as hypotheses**
```lean
variable {F : Type*} [HasBot F] [HasImp F]
variable (Deriv : List F → F → Prop)
variable (h_weak : ...) (h_mp : ...) (h_ax : ...)
```

### Recommended: Option A (Structure)

A structure is the best choice because:
1. It bundles the derivation relation with its properties, making it easy to instantiate
2. It avoids typeclass resolution overhead (MCS theory is used in specific metalogic proofs, not in general automation)
3. It matches the pattern in BimodalLogic where `DerivationTree fc Gamma phi` is used directly
4. Downstream tasks (30, 31) will create instances: `mkDerivationSystem (fun Γ φ => Nonempty (DerivationTree fc Γ φ))`

### Proposed Type Signature

```lean
/-- A derivation system abstracts over logic-specific proof systems.

    `F` is the formula type with bottom and implication.
    `Deriv` maps a context (list of assumptions) and a conclusion to a Prop.

    Required properties:
    - weakening: derivations can be extended with additional assumptions
    - assumption: any formula in the context is derivable from it
    - mp: modus ponens is admissible
    - efq: ex falso quodlibet (⊥ → anything)
    - ax_weakening: theorems (derivable from []) can be weakened to any context
-/
structure DerivationSystem (F : Type*) [HasBot F] [HasImp F] where
  /-- Context-based derivability: `Deriv Γ φ` means φ is derivable from Γ. -/
  Deriv : List F → F → Prop
  /-- Weakening: if Γ ⊢ φ and Γ ⊆ Δ, then Δ ⊢ φ. -/
  weakening : ∀ {Γ Δ : List F} {φ : F},
    Deriv Γ φ → (∀ x ∈ Γ, x ∈ Δ) → Deriv Δ φ
  /-- Assumption: if φ ∈ Γ, then Γ ⊢ φ. -/
  assumption : ∀ {Γ : List F} {φ : F}, φ ∈ Γ → Deriv Γ φ
  /-- Modus ponens: from Γ ⊢ φ → ψ and Γ ⊢ φ, derive Γ ⊢ ψ. -/
  mp : ∀ {Γ : List F} {φ ψ : F},
    Deriv Γ (HasImp.imp φ ψ) → Deriv Γ φ → Deriv Γ ψ
```

### Why Not Include the Deduction Theorem in the Base Structure

The deduction theorem is NOT needed for the base MCS definitions (`SetConsistent`, `SetMaximalConsistent`, `consistent_chain_union`, `set_lindenbaum`). It IS needed for the closure properties (`closed_under_derivation`, `implication_property`, `negation_complete`).

Two design options:
1. **Extended structure**: Add `deduction_theorem` as a field to `DerivationSystem`
2. **Separate assumption**: State closure lemmas with an explicit hypothesis

**Recommendation**: Use option 1. Include the deduction theorem as a field because:
- Tasks 30 and 31 will both need these closure properties
- Having it in the structure forces each instantiation to provide it
- It keeps the API surface clean

```lean
/-- Extended derivation system with deduction theorem support. -/
structure DerivationSystemWithDT (F : Type*) [HasBot F] [HasImp F]
    extends DerivationSystem F where
  /-- Deduction theorem: if (φ :: Γ) ⊢ ψ then Γ ⊢ φ → ψ. -/
  deduction : ∀ {Γ : List F} {φ ψ : F},
    Deriv (φ :: Γ) ψ → Deriv Γ (HasImp.imp φ ψ)
```

**However**, re-reading the task description more carefully: "These are the ~60% of MCS theory that do not depend on per-logic deduction theorems." This suggests the module should contain the generic lemmas that work WITHOUT the deduction theorem, and the deduction-theorem-dependent properties go into per-logic metalogic modules (tasks 30, 31).

**Revised recommendation**: The `DerivationSystem` structure should NOT include the deduction theorem. Instead:
- `SetConsistent`, `SetMaximalConsistent`, `consistent_chain_union`, `set_lindenbaum` use `DerivationSystem`
- `closed_under_derivation` and `implication_property` take an ADDITIONAL hypothesis for the deduction theorem
- This way the module is truly generic and the deduction theorem obligation falls on each logic

## 5. Proposed API Surface

### Target File: `Cslib/Foundations/Logic/Metalogic/Consistency.lean`

```lean
import Mathlib.Order.Zorn
import Mathlib.Order.Preorder.Chain
import Cslib.Foundations.Logic.Connectives

namespace Cslib.Logic.Metalogic

-- === Core Structure ===

structure DerivationSystem (F : Type*) [HasBot F] [HasImp F] where
  Deriv : List F → F → Prop
  weakening : ...
  assumption : ...
  mp : ...

-- === Consistency Definitions ===

/-- List-based consistency: Γ is consistent iff Γ does not derive ⊥. -/
def Consistent (D : DerivationSystem F) (Γ : List F) : Prop :=
  ¬ D.Deriv Γ HasBot.bot

/-- Set-based consistency: S is set-consistent iff every finite subset is consistent. -/
def SetConsistent (D : DerivationSystem F) (S : Set F) : Prop :=
  ∀ L : List F, (∀ φ ∈ L, φ ∈ S) → Consistent D L

/-- Set-based maximal consistency. -/
def SetMaximalConsistent (D : DerivationSystem F) (S : Set F) : Prop :=
  SetConsistent D S ∧ ∀ φ : F, φ ∉ S → ¬ SetConsistent D (insert φ S)

-- === Chain Union ===

/-- Any finite list from a chain union is in some chain member. -/
lemma finite_list_in_chain_member ...

/-- The union of a nonempty chain of consistent sets is consistent. -/
theorem consistent_chain_union (D : DerivationSystem F)
    {C : Set (Set F)} (hchain : IsChain (· ⊆ ·) C) (hCne : C.Nonempty)
    (hcons : ∀ S ∈ C, SetConsistent D S) :
    SetConsistent D (⋃₀ C)

-- === Lindenbaum's Lemma ===

/-- Consistent supersets of a base set. -/
def ConsistentSupersets (D : DerivationSystem F) (S : Set F) : Set (Set F) :=
  {T | S ⊆ T ∧ SetConsistent D T}

/-- Every consistent set extends to a maximally consistent set. -/
theorem set_lindenbaum (D : DerivationSystem F) (S : Set F)
    (hS : SetConsistent D S) :
    ∃ M : Set F, S ⊆ M ∧ SetMaximalConsistent D M

-- === Closure Properties (require deduction theorem hypothesis) ===

/-- Deduction theorem hypothesis type. -/
def HasDeductionTheorem (D : DerivationSystem F) : Prop :=
  ∀ {Γ : List F} {φ ψ : F},
    D.Deriv (φ :: Γ) ψ → D.Deriv Γ (HasImp.imp φ ψ)

/-- MCS is closed under derivation (requires deduction theorem). -/
theorem SetMaximalConsistent.closed_under_derivation
    (D : DerivationSystem F) (hdt : HasDeductionTheorem D)
    {S : Set F} (h_mcs : SetMaximalConsistent D S)
    (L : List F) (h_sub : ∀ ψ ∈ L, ψ ∈ S)
    (h_deriv : D.Deriv L φ) : φ ∈ S

/-- Implication property: if (φ → ψ) ∈ S and φ ∈ S, then ψ ∈ S. -/
theorem SetMaximalConsistent.implication_property
    (D : DerivationSystem F) (hdt : HasDeductionTheorem D)
    {S : Set F} (h_mcs : SetMaximalConsistent D S)
    (h_imp : HasImp.imp φ ψ ∈ S) (h_phi : φ ∈ S) : ψ ∈ S

-- === Additional Properties ===

/-- In a set-consistent set, φ and ¬φ cannot both be members. -/
theorem set_consistent_not_both (D : DerivationSystem F)
    {S : Set F} (h_cons : SetConsistent D S)
    (φ : F) (h_phi : φ ∈ S) (h_neg : HasImp.imp φ HasBot.bot ∈ S) : False

/-- Negation completeness (requires deduction theorem). -/
theorem SetMaximalConsistent.negation_complete
    (D : DerivationSystem F) (hdt : HasDeductionTheorem D)
    {S : Set F} (h_mcs : SetMaximalConsistent D S) (φ : F) :
    φ ∈ S ∨ HasImp.imp φ HasBot.bot ∈ S
```

### Estimated Line Count

| Section | Lines |
|---------|-------|
| Module header + imports | 15 |
| `DerivationSystem` structure | 25 |
| Consistency definitions (3 defs) | 30 |
| `finite_list_in_chain_member` | 25 |
| `consistent_chain_union` | 15 |
| `ConsistentSupersets` + helper | 15 |
| `set_lindenbaum` | 40 |
| `HasDeductionTheorem` + closure properties | 80 |
| Additional properties | 30 |
| **Total** | **~275** |

This falls within the target range of 200-300 lines.

## 6. Recommendations for Implementation

### Phase 1: Structure + Definitions (Priority)
1. Create `Cslib/Foundations/Logic/Metalogic/Consistency.lean`
2. Define `DerivationSystem` structure
3. Define `Consistent`, `SetConsistent`, `SetMaximalConsistent`
4. These are definitional only, no proofs needed

### Phase 2: Chain Union + Lindenbaum
1. Port `finite_list_in_chain_member` -- this is pure set/chain theory, identical to BimodalLogic
2. Port `consistent_chain_union` -- replace `fc` parameter with `D : DerivationSystem`
3. Port `set_lindenbaum` -- identical structure, replace concrete types with generic

### Phase 3: Deduction-Dependent Properties
1. Define `HasDeductionTheorem` as a Prop (or make it a field in an extended structure)
2. Port `closed_under_derivation` with deduction theorem hypothesis
3. Port `implication_property` (reduces to `closed_under_derivation`)
4. Port `negation_complete` with deduction theorem hypothesis

### Phase 4: Additional Properties
1. `set_consistent_not_both` -- uses only modus ponens
2. `neg_excludes` -- follows from `set_consistent_not_both`

### Key Porting Notes

1. **Replace `Formula` with `F`**: Every occurrence of `Bimodal.Syntax.Formula` becomes the generic type variable `F`.

2. **Replace `DerivationTree fc Γ φ` with `D.Deriv Γ φ`**: The concrete derivation tree is replaced by the abstract derivation predicate.

3. **Replace `Formula.bot` with `HasBot.bot`**: Use the typeclass connective.

4. **Replace `Formula.imp` with `HasImp.imp`**: Use the typeclass connective.

5. **Replace `Formula.neg φ` with `HasImp.imp φ HasBot.bot`**: Negation is defined as `φ → ⊥` in the Lukasiewicz encoding. Do NOT add a separate `neg` parameter; use the structural definition directly.

6. **`FrameClass` parameter disappears**: The generic module is not parameterized by frame class. Each logic's instantiation will fix this internally.

7. **`Nonempty` wrapping**: In BimodalLogic, `Consistent` is defined as `¬Nonempty (DerivationTree ...)`. In the generic version, `Deriv` is already Prop-valued, so `Consistent D Γ` is simply `¬ D.Deriv Γ HasBot.bot`.

8. **Derivation tree constructors become structure fields**: `DerivationTree.assumption` becomes `D.assumption`, `DerivationTree.modus_ponens` becomes `D.mp`, `DerivationTree.weakening` becomes `D.weakening`.

### Downstream Integration (Tasks 30, 31)

Tasks 30 (Modal metalogic) and 31 (Temporal metalogic) will:
1. Create a `DerivationSystem` instance from their respective `DerivationTree` types
2. Provide deduction theorem proofs
3. Import generic MCS theory from `Cslib.Foundations.Logic.Metalogic.Consistency`
4. Add logic-specific properties (modal saturation, temporal coherence, etc.)

Example instantiation for temporal logic:
```lean
noncomputable def Temporal.derivationSystem (fc : FrameClass) : DerivationSystem (Formula Atom) where
  Deriv := fun Γ φ => Nonempty (DerivationTree fc Γ φ)
  weakening := fun ⟨d⟩ h => ⟨DerivationTree.weakening _ _ _ d h⟩
  assumption := fun h => ⟨DerivationTree.assumption _ _ h⟩
  mp := fun ⟨d1⟩ ⟨d2⟩ => ⟨DerivationTree.modus_ponens _ _ _ d1 d2⟩
```

### Potential Issues

1. **Universe polymorphism**: The generic `F` type may need universe annotations. BimodalLogic uses a fixed universe; cslib uses `Type u` for formula types. The `DerivationSystem` should be universe-polymorphic.

2. **`DecidableEq` on formulas**: Some BimodalLogic proofs use `List.filter (· != phi)` which requires `DecidableEq Formula`. The generic module should either add a `[DecidableEq F]` constraint or use `Classical.propDecidable`.

3. **`imp` vs `neg`**: BimodalLogic uses `Formula.neg` which is an abbrev for `φ.imp .bot`. The generic module should consistently use `HasImp.imp φ HasBot.bot` and never assume a separate `neg` constructor.

4. **Lean 4 `List.filter` API changes**: BimodalLogic uses `List.filter (fun y => decide (y != phi))`. Current Lean 4 may have different `List.filter` signatures. Verify against current Mathlib's `List` API.

## 7. Risk Assessment

| Risk | Likelihood | Mitigation |
|------|-----------|------------|
| Universe issues with `DerivationSystem` | Medium | Use explicit universe annotation `{F : Type u}` |
| `List.filter` API differences | Low | Use `Classical.propDecidable` + current Lean API |
| Import cycle with existing ProofSystem | Low | New file in `Metalogic/` has no upstream imports from `Logics/` |
| Proof porting difficulty | Low | Proofs are structural, same shape with different types |
| Missing `HasImp.imp` simp lemmas | Medium | May need local simp lemmas for `imp bot` patterns |

## 8. File Dependencies

```
Cslib/Foundations/Logic/Metalogic/Consistency.lean
  imports:
    - Mathlib.Order.Zorn
    - Mathlib.Order.Preorder.Chain
    - Cslib.Foundations.Logic.Connectives  (for HasBot, HasImp)

  imported by (future):
    - Cslib/Logics/Modal/Metalogic/...     (task 30)
    - Cslib/Logics/Temporal/Metalogic/...  (task 31)
```

No circular dependencies. The module sits in `Foundations/Logic/Metalogic/` which is a new directory, cleanly separated from both the existing `Foundations/Logic/` infrastructure and the `Logics/` implementations.
