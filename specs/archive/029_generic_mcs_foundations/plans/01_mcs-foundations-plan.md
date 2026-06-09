# Implementation Plan: Task #29

- **Task**: 29 - Generic MCS foundations
- **Status**: [NOT STARTED]
- **Effort**: 3 hours
- **Dependencies**: None
- **Research Inputs**: specs/029_generic_mcs_foundations/reports/01_mcs-foundations-research.md
- **Artifacts**: plans/01_mcs-foundations-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: true

## Overview

Create a single file `Cslib/Foundations/Logic/Metalogic/Consistency.lean` (~200-300 lines) providing generic MCS (maximal consistent set) foundations parameterized over an abstract derivation relation. The module defines `DerivationSystem F` as a structure bundling a context-based derivability predicate with weakening, assumption, and modus ponens properties. It then builds the standard Lindenbaum lemma infrastructure: `SetConsistent`, `SetMaximalConsistent`, `consistent_chain_union`, and `set_lindenbaum` (via Zorn). Finally, it defines `HasDeductionTheorem` as a separate hypothesis type and proves `closed_under_derivation`, `implication_property`, and `negation_complete` contingent on it. Downstream tasks 30 (Modal metalogic) and 31 (Temporal metalogic) will instantiate `DerivationSystem` from their concrete `DerivationTree` types and supply deduction theorem proofs.

### Research Integration

Key findings from the research report integrated into this plan:

- **Generic vs. logic-specific boundary**: ~60% of BimodalLogic's MCS theory (SetConsistent, SetMaximalConsistent, chain union, Lindenbaum) is generic; ~40% (closure properties) requires a deduction theorem hypothesis. The plan separates these into distinct phases (3 vs. 5).
- **DerivationSystem structure (Option A)**: The research recommends a structure (not typeclass) bundling `Deriv : List F -> F -> Prop` with weakening, assumption, and modus ponens. This avoids typeclass resolution overhead and matches the downstream usage pattern.
- **HasDeductionTheorem as separate Prop**: The deduction theorem is NOT included in the base `DerivationSystem` structure. Instead, `closed_under_derivation` and `implication_property` take an explicit `HasDeductionTheorem D` hypothesis. This keeps the module truly generic.
- **Mathlib dependencies verified**: `zorn_subset_nonempty`, `IsChain`, `Maximal` all available with the expected signatures.
- **Negation encoding**: Use `HasImp.imp phi HasBot.bot` consistently; no separate `neg` constructor.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This plan advances the following ROADMAP.md items:
- Phase 4 (Standalone Metalogic) -- Task 29: Generic MCS Foundations
- Success metric: "Generic MCS foundations in Foundations/Logic/Metalogic/Consistency.lean (Task 29: ~200-300 new lines)"

## Goals & Non-Goals

**Goals**:
- Define `DerivationSystem F` structure with `Deriv`, `weakening`, `assumption`, `mp` fields
- Define `Consistent`, `SetConsistent`, `SetMaximalConsistent` predicates
- Prove `consistent_chain_union` (chain union preserves set-consistency)
- Prove `set_lindenbaum` (Zorn-based existence of maximal consistent extensions)
- Define `HasDeductionTheorem` hypothesis type
- Prove `closed_under_derivation`, `implication_property`, `negation_complete` (conditional on deduction theorem)
- Prove `set_consistent_not_both` (purely structural, no deduction theorem needed)
- Ensure zero sorry occurrences
- Ensure `lake build` passes

**Non-Goals**:
- Logic-specific instantiations (those belong in tasks 30, 31, 7)
- RestrictedMCS or temporal/modal-specific witness conditions
- Bimodal-specific MCS properties (all_future_all_future, etc.)
- Deduction theorem proofs (each logic proves its own by structural induction)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Universe polymorphism issues with `DerivationSystem` | M | M | Use explicit `{F : Type*}` annotation; test with `universe u` if needed |
| `HasImp.imp` / `HasBot.bot` simp lemma gaps | M | M | Add local simp lemmas or use `show` to unfold definitions |
| `List.filter` API differences from BimodalLogic | L | L | Use `Classical.propDecidable` + current Lean 4 `List` API |
| `zorn_subset_nonempty` signature changes in Mathlib | M | L | Verify exact signature via `lean_hover_info` before writing proof |
| Import cycle with existing ProofSystem | L | L | New file in `Metalogic/` has no upstream imports from `Logics/` |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |
| 5 | 5 | 4 |
| 6 | 6 | 5 |

Phases within the same wave can execute in parallel.

---

### Phase 1: File setup, imports, DerivationSystem structure [COMPLETED]

**Goal**: Create the target file with correct module header, imports, namespace, and the core `DerivationSystem` structure.

**Tasks**:
- [ ] Create directory `Cslib/Foundations/Logic/Metalogic/`
- [ ] Create file `Cslib/Foundations/Logic/Metalogic/Consistency.lean` with Apache 2.0 header
- [ ] Add imports: `Mathlib.Order.Zorn`, `Mathlib.Order.Chain` (or `Mathlib.Order.Preorder.Chain`), `Cslib.Foundations.Logic.Connectives`
- [ ] Open namespace `Cslib.Logic.Metalogic`
- [ ] Define `DerivationSystem` structure with fields:
  ```lean
  structure DerivationSystem (F : Type*) [HasBot F] [HasImp F] where
    Deriv : List F → F → Prop
    weakening : ∀ {Γ Δ : List F} {φ : F}, Deriv Γ φ → (∀ x ∈ Γ, x ∈ Δ) → Deriv Δ φ
    assumption : ∀ {Γ : List F} {φ : F}, φ ∈ Γ → Deriv Γ φ
    mp : ∀ {Γ : List F} {φ ψ : F}, Deriv Γ (HasImp.imp φ ψ) → Deriv Γ φ → Deriv Γ ψ
  ```
- [ ] Add docstring explaining purpose and downstream usage pattern
- [ ] Verify file compiles with `lean_goal` or `lake build Cslib.Foundations.Logic.Metalogic.Consistency`

**Timing**: 20 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Foundations/Logic/Metalogic/Consistency.lean` - NEW file creation

**Verification**:
- File compiles with no errors
- `DerivationSystem` structure is accessible in namespace

---

### Phase 2: SetConsistent and SetMaximalConsistent definitions + basic lemmas [COMPLETED]

**Goal**: Define the core consistency predicates and basic structural lemmas.

**Tasks**:
- [ ] Define `Consistent`:
  ```lean
  def Consistent (D : DerivationSystem F) (Γ : List F) : Prop :=
    ¬ D.Deriv Γ HasBot.bot
  ```
- [ ] Define `SetConsistent`:
  ```lean
  def SetConsistent (D : DerivationSystem F) (S : Set F) : Prop :=
    ∀ L : List F, (∀ φ ∈ L, φ ∈ S) → Consistent D L
  ```
- [ ] Define `SetMaximalConsistent`:
  ```lean
  def SetMaximalConsistent (D : DerivationSystem F) (S : Set F) : Prop :=
    SetConsistent D S ∧ ∀ φ : F, φ ∉ S → ¬ SetConsistent D (insert φ S)
  ```
- [ ] Define `ConsistentSupersets`:
  ```lean
  def ConsistentSupersets (D : DerivationSystem F) (S : Set F) : Set (Set F) :=
    {T | S ⊆ T ∧ SetConsistent D T}
  ```
- [ ] Prove `set_consistent_not_both`: in a set-consistent set, `phi` and `imp phi bot` cannot both be members. Uses only `mp` and `assumption` from `DerivationSystem`.
- [ ] Prove `base_mem_consistent_supersets`: `SetConsistent D S -> S in ConsistentSupersets D S`
- [ ] Add docstrings to all definitions
- [ ] Verify compilation

**Timing**: 30 minutes

**Depends on**: 1

**Files to modify**:
- `Cslib/Foundations/Logic/Metalogic/Consistency.lean` - add definitions after `DerivationSystem`

**Verification**:
- All definitions compile
- `set_consistent_not_both` proof complete with zero sorry

---

### Phase 3: Chain union lemmas (consistent_chain_union for Zorn) [COMPLETED]

**Goal**: Prove that the union of a chain of consistent sets is consistent, which is the key input to Zorn's lemma.

**Tasks**:
- [ ] Prove `finite_list_in_chain_member`: any finite list whose elements all belong to `sUnion C` (a chain union) has all its elements in some single chain member. This is pure set/chain theory.
  ```lean
  lemma finite_list_in_chain_member {C : Set (Set F)}
      (hchain : IsChain (· ⊆ ·) C) (hCne : C.Nonempty)
      (L : List F) (h : ∀ φ ∈ L, φ ∈ ⋃₀ C) :
      ∃ S ∈ C, ∀ φ ∈ L, φ ∈ S
  ```
  The proof proceeds by induction on `L`. Base case: use `hCne`. Inductive case: for `a :: L`, get `S1 in C` containing `a` and `S2 in C` containing all of `L`; by `hchain.total` one contains the other; take the larger.
- [ ] Prove `consistent_chain_union`: the union of a nonempty chain of set-consistent sets is set-consistent.
  ```lean
  theorem consistent_chain_union (D : DerivationSystem F)
      {C : Set (Set F)} (hchain : IsChain (· ⊆ ·) C) (hCne : C.Nonempty)
      (hcons : ∀ S ∈ C, SetConsistent D S) :
      SetConsistent D (⋃₀ C)
  ```
  Uses `finite_list_in_chain_member` to reduce to a single chain member, then applies `hcons`.
- [ ] Verify both proofs compile with zero sorry

**Timing**: 45 minutes

**Depends on**: 2

**Files to modify**:
- `Cslib/Foundations/Logic/Metalogic/Consistency.lean` - add chain union section

**Verification**:
- `consistent_chain_union` compiles
- No sorry in any proof
- `lean_verify` on key theorems to check axiom usage

---

### Phase 4: Lindenbaum's lemma (Zorn-based existence of maximal consistent extensions) [COMPLETED]

**Goal**: Prove that every consistent set can be extended to a maximally consistent set, using Zorn's lemma.

**Tasks**:
- [ ] Prove `set_lindenbaum`:
  ```lean
  theorem set_lindenbaum (D : DerivationSystem F) {S : Set F}
      (hS : SetConsistent D S) :
      ∃ M : Set F, S ⊆ M ∧ SetMaximalConsistent D M
  ```
  The proof applies `zorn_subset_nonempty` to `ConsistentSupersets D S`:
  1. Show `ConsistentSupersets D S` is nonempty (contains `S` itself via `base_mem_consistent_supersets`)
  2. Show every chain in `ConsistentSupersets` has an upper bound in `ConsistentSupersets` (the chain union, using `consistent_chain_union`)
  3. Extract the maximal element `M` with `S ⊆ M` and `Maximal (· ∈ ConsistentSupersets D S) M`
  4. Show `Maximal` implies `SetMaximalConsistent`: if `phi not in M`, then `insert phi M` strictly extends `M` in `ConsistentSupersets`, contradicting maximality unless `insert phi M` is inconsistent
- [ ] Verify proof compiles with zero sorry
- [ ] Run `lake build Cslib.Foundations.Logic.Metalogic.Consistency` to verify module-scoped build

**Timing**: 45 minutes

**Depends on**: 3

**Files to modify**:
- `Cslib/Foundations/Logic/Metalogic/Consistency.lean` - add Lindenbaum section

**Verification**:
- `set_lindenbaum` compiles with zero sorry
- Module builds cleanly

---

### Phase 5: HasDeductionTheorem class + closure properties [COMPLETED]

**Goal**: Define the deduction theorem hypothesis and prove the closure properties that depend on it.

**Tasks**:
- [ ] Define `HasDeductionTheorem`:
  ```lean
  def HasDeductionTheorem (D : DerivationSystem F) : Prop :=
    ∀ {Γ : List F} {φ ψ : F},
      D.Deriv (φ :: Γ) ψ → D.Deriv Γ (HasImp.imp φ ψ)
  ```
- [ ] Prove `SetMaximalConsistent.closed_under_derivation`:
  ```lean
  theorem SetMaximalConsistent.closed_under_derivation
      (D : DerivationSystem F) (hdt : HasDeductionTheorem D)
      {S : Set F} (h_mcs : SetMaximalConsistent D S)
      {L : List F} (h_sub : ∀ ψ ∈ L, ψ ∈ S)
      {φ : F} (h_deriv : D.Deriv L φ) : φ ∈ S
  ```
  Proof strategy: By contradiction. Assume `phi not in S`. By maximality, `insert phi S` is inconsistent: some `L' subset insert phi S` derives `bot`. If `phi in L'`, apply deduction theorem to get `L' \ {phi} derives imp phi bot`. Combined with `L derives phi` (via weakening), get `L'' derives bot` where `L'' subset S`, contradicting set-consistency.
- [ ] Prove `SetMaximalConsistent.implication_property`:
  ```lean
  theorem SetMaximalConsistent.implication_property
      (D : DerivationSystem F) (hdt : HasDeductionTheorem D)
      {S : Set F} (h_mcs : SetMaximalConsistent D S)
      {φ ψ : F} (h_imp : HasImp.imp φ ψ ∈ S) (h_phi : φ ∈ S) : ψ ∈ S
  ```
  Proof: `[imp phi psi, phi]` derives `psi` via modus ponens. Apply `closed_under_derivation`.
- [ ] Prove `SetMaximalConsistent.negation_complete`:
  ```lean
  theorem SetMaximalConsistent.negation_complete
      (D : DerivationSystem F) (hdt : HasDeductionTheorem D)
      {S : Set F} (h_mcs : SetMaximalConsistent D S)
      (φ : F) : φ ∈ S ∨ HasImp.imp φ HasBot.bot ∈ S
  ```
  Proof: By contradiction on both. If `phi not in S`, then `insert phi S` inconsistent: some `L derives bot` with `phi in L`. Apply deduction theorem: `L \ {phi} derives imp phi bot`. Since `L \ {phi} subset S`, by `closed_under_derivation`, `imp phi bot in S`. Contradiction.
- [ ] Add docstrings explaining the deduction theorem boundary
- [ ] Verify all proofs compile with zero sorry

**Timing**: 45 minutes

**Depends on**: 4

**Files to modify**:
- `Cslib/Foundations/Logic/Metalogic/Consistency.lean` - add closure properties section

**Verification**:
- All three closure theorems compile
- No sorry anywhere in the file
- Each theorem correctly takes `HasDeductionTheorem D` as an explicit hypothesis

---

### Phase 6: Build verification [COMPLETED]

**Goal**: Full project build verification, zero-sorry scan, and linter compliance.

**Tasks**:
- [ ] Run `lake build` to verify full project builds with zero errors
- [ ] Run `grep -r sorry Cslib/Foundations/Logic/Metalogic/Consistency.lean` to confirm zero sorry
- [ ] Verify line count is within 200-300 line target
- [ ] Run `lean_verify` on key definitions (`SetConsistent`, `SetMaximalConsistent`, `set_lindenbaum`, `closed_under_derivation`) to check axiom usage
- [ ] Verify namespace structure: all definitions accessible as `Cslib.Logic.Metalogic.*`
- [ ] Verify downstream import path works: a test `import Cslib.Foundations.Logic.Metalogic.Consistency` should compile

**Timing**: 15 minutes

**Depends on**: 5

**Files to modify**:
- No new modifications expected; fix any issues found

**Verification**:
- `lake build` passes with zero errors
- Zero sorry occurrences
- File is 200-300 lines
- All key theorems verified

---

## Testing & Validation

- [ ] `lake build Cslib.Foundations.Logic.Metalogic.Consistency` passes
- [ ] `lake build` (full project) passes with zero errors
- [ ] Zero `sorry` occurrences in the file
- [ ] `lean_verify` confirms no axiom misuse on `set_lindenbaum` and `closed_under_derivation`
- [ ] File line count is within 200-300 lines
- [ ] All definitions are in `Cslib.Logic.Metalogic` namespace
- [ ] `DerivationSystem` structure compiles with `[HasBot F] [HasImp F]` constraints
- [ ] `HasDeductionTheorem` is a `Prop`-valued definition, not a typeclass

## Artifacts & Outputs

- `Cslib/Foundations/Logic/Metalogic/Consistency.lean` - The implementation (NEW, ~200-300 lines)
- `specs/029_generic_mcs_foundations/plans/01_mcs-foundations-plan.md` - This plan
- `specs/029_generic_mcs_foundations/summaries/01_mcs-foundations-summary.md` - Post-implementation summary

## Rollback/Contingency

- The implementation is a single new file with no modifications to existing files. Rollback is trivial: delete `Cslib/Foundations/Logic/Metalogic/Consistency.lean` and the `Metalogic/` directory.
- If Zorn-based `set_lindenbaum` proof encounters unexpected Mathlib API issues, fall back to checking exact `zorn_subset_nonempty` signature via `lean_hover_info` and adapting arguments.
- If closure properties (Phase 5) prove difficult with the abstract `HasDeductionTheorem` hypothesis, consider making it a class field in an extended structure `DerivationSystemWithDT` as an alternative design.
