# Implementation Plan: Task #10

- **Task**: 10 - Port Separation Theorem (PR 9)
- **Status**: [NOT STARTED]
- **Effort**: 18 hours
- **Dependencies**: Tasks 4 (ProofSystem), 5 (Theorems), 7 (MCS/Deduction) -- all completed
- **Research Inputs**: specs/010_port_separation_theorem_bimodal/reports/01_separation-research.md
- **Artifacts**: plans/01_separation-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: false

## Overview

Port the Separation Theorem (GHR94 Theorem 10.2.9) from BimodalLogic to cslib. This involves 15 core files totaling approximately 6,420 lines (excluding SemanticBridge.lean and KampTranslation.lean which depend on unported completeness infrastructure). The separation theorem proves that every {U,S}-formula over integer time is equivalent to a syntactically separated formula. The main porting challenge is systematic Atom type parameterization from a concrete `Atom` struct to generic `Atom : Type*` with `[DecidableEq Atom]` and `[Infinite Atom]` constraints.

### Research Integration

Key findings from the research report (01_separation-research.md):
- 17 source files totaling ~8,544 lines; 15 core files (~6,420 lines) are in scope after excluding SemanticBridge and KampTranslation
- All proofs are complete: zero sorry, zero axiom declarations, 4 noncomputable defs (fresh_atom, fresh_atoms, extract_innermost_U_type, extract_U_type)
- The cslib `Formula.swap_temporal` with involution and simp lemmas already exists, enabling Duality.lean to reference cslib APIs directly
- Atom parameterization: source uses concrete `Atom` struct; cslib uses generic `{Atom : Type*}` requiring `[DecidableEq Atom]` and `[Infinite Atom]`
- The separation module is self-contained: it does NOT depend on derivation, axioms, MCS, or soundness -- only on `Formula` syntax and its own `IntStructure`/`int_truth` semantics

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md items checked for this task.

## Goals & Non-Goals

**Goals**:
- Port all 15 core separation files to `Cslib/Logics/Bimodal/Metalogic/Separation/`
- Parameterize Atom type throughout: `{Atom : Type*}` with `[DecidableEq Atom]` and `[Infinite Atom]`
- Maintain zero sorry, zero axiom status
- Create barrel import file at `Cslib/Logics/Bimodal/Metalogic/Separation.lean`
- All files pass `lake build` with cslib conventions (copyright headers, namespaces, imports)

**Non-Goals**:
- Porting SemanticBridge.lean (depends on unported MonadicFO/Table infrastructure)
- Porting KampTranslation.lean (blocked on n-variable Fraisse game, depends on unported StaviConnectives)
- Refactoring or simplifying proofs beyond what Atom parameterization requires
- Adding new lemmas not present in the source

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Atom parameterization cascading through all files | M | H | Systematic: add `variable {Atom : Type*} [DecidableEq Atom]` everywhere; `[Infinite Atom]` only where freshness is needed |
| formula_atoms (Set) vs .atoms (Finset) mismatch | M | M | Define local `formula_atoms` returning `Set Atom` in Defs.lean, matching source semantics exactly |
| Mathlib API changes between v4.27 and v4.31 | L | M | Fix at build time with `exact?`/`simp?`; most arithmetic lemmas are stable |
| Large files (1000+ lines) causing implementation timeout | M | M | Each large file gets its own phase; port in logical chunks |
| `open Classical` vs `Classical.propDecidable` convention | L | L | cslib already uses `attribute [local instance] Classical.propDecidable`; adjust Eliminations.lean accordingly |
| Freshness proof refactoring for `[Infinite Atom]` | M | M | Replace `exists_atom_not_in_finset` with `Infinite.exists_notMem_finset` from Mathlib |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3, 4, 5 | 1 |
| 3 | 6 | 3, 4 |
| 4 | 7 | 5, 6 |
| 5 | 8 | 7 |
| 6 | 9, 10 | 5, 8 |
| 7 | 11 | 9, 10 |
| 8 | 12 | 11 |
| 9 | 13 | 12 |
| 10 | 14 | 7, 13 |
| 11 | 15 | 14 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Defs.lean -- Foundation Types and Predicates [COMPLETED]

**Goal**: Port the core definitions: IntStructure, int_truth, int_equiv, syntactic predicates (is_U_free, is_S_free, is_syntactically_separated), semantic predicates (is_separable), formula_atoms (Set-based), and structural measures (junction_depth, etc.).

**Tasks**:
- [ ] Create directory `Cslib/Logics/Bimodal/Metalogic/Separation/`
- [ ] Create `Cslib/Logics/Bimodal/Metalogic/Separation/Defs.lean` with Apache 2.0 header
- [ ] Port `IntStructure` as `IntStructure (Atom : Type*)` with `val : Atom -> Set Z`
- [ ] Port `int_truth` with `{Atom : Type*}` parameter; `Formula` becomes `Formula Atom`
- [ ] Port all `int_truth` simp lemmas (all_past, all_future, some_past, some_future, neg, and, or, top, diamond)
- [ ] Port `formula_atoms : Formula Atom -> Set Atom` (Set-based, matching source)
- [ ] Port `formula_atoms` simp lemmas
- [ ] Port `int_equiv`, `is_pure_past`, `is_pure_future`, `is_pure_present`
- [ ] Port `is_U_free`, `is_S_free`, `is_syntactically_separated` (Bool-returning, decidable)
- [ ] Port `is_separable` predicate
- [ ] Port `junction_depth`, `U_depth_under_S`, `count_U_subformulas` and related measures
- [ ] Port `int_truth_depends_on_atoms` and other dependence lemmas
- [ ] Remap namespace from `Bimodal.Metalogic.WeakCanonical.Separation` to `Cslib.Logic.Bimodal.Metalogic.Separation`
- [ ] Replace `import Bimodal.Syntax.Formula` with `import Cslib.Logics.Bimodal.Syntax.Formula`
- [ ] Add `import Mathlib.Algebra.Order.Group.Int`
- [ ] Add linter options: `set_option linter.style.emptyLine false` and `set_option linter.flexible false`
- [ ] Verify `lake build Cslib.Logics.Bimodal.Metalogic.Separation.Defs`

**Timing**: 2 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/Separation/Defs.lean` -- create (553 lines source)

**Verification**:
- File compiles with zero errors
- Zero sorry occurrences
- Namespace is `Cslib.Logic.Bimodal.Metalogic.Separation`
- `IntStructure` is parameterized by `Atom : Type*`

---

### Phase 2: FormulaOps.lean -- Substitution and Freshness [COMPLETED]

**Goal**: Port substitution infrastructure, IntStructure.withAtom, subst_correctness, freshness infrastructure (fresh_atom, fresh_atoms), and multi-substitution.

**Tasks**:
- [ ] Create `Cslib/Logics/Bimodal/Metalogic/Separation/FormulaOps.lean`
- [ ] Port `subst_formula` with `{Atom : Type*} [DecidableEq Atom]`
- [ ] Port `IntStructure.withAtom` with parameterized Atom
- [ ] Port `subst_correctness` theorem
- [ ] Replace `exists_atom_not_in_finset` proof with `Infinite.exists_notMem_finset` from Mathlib (requires `[Infinite Atom]`)
- [ ] Port `exists_n_fresh_atoms` using `[Infinite Atom]`
- [ ] Port `noncomputable def fresh_atom` with `[DecidableEq Atom] [Infinite Atom]`
- [ ] Port `noncomputable def fresh_atoms` with same constraints
- [ ] Port `fresh_atom_not_in`, `fresh_atoms_disjoint`, `fresh_atoms_nodup`, `fresh_atoms_length`
- [ ] Port `multi_subst`, `multi_subst_nil`, `multi_subst_singleton`
- [ ] Update imports to `Cslib.Logics.Bimodal.Metalogic.Separation.Defs`
- [ ] Verify `lake build Cslib.Logics.Bimodal.Metalogic.Separation.FormulaOps`

**Timing**: 1 hour

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/Separation/FormulaOps.lean` -- create (235 lines source)

**Verification**:
- File compiles with zero errors
- `fresh_atom` and `fresh_atoms` are noncomputable with `[Infinite Atom]` constraint
- `subst_correctness` type-checks with parameterized types

---

### Phase 3: IntHelpers.lean -- Integer Arithmetic Lemmas [COMPLETED]

**Goal**: Port integer-specific helper lemmas for finite intervals and witness constructions needed by the separation proof.

**Tasks**:
- [ ] Create `Cslib/Logics/Bimodal/Metalogic/Separation/IntHelpers.lean`
- [ ] Port all integer-arithmetic lemmas (finite intervals, first-failure witnesses)
- [ ] Update imports to reference Cslib modules and `Mathlib.Data.Int.Interval`
- [ ] Verify `lake build Cslib.Logics.Bimodal.Metalogic.Separation.IntHelpers`

**Timing**: 0.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/Separation/IntHelpers.lean` -- create (131 lines source)

**Verification**:
- File compiles with zero errors
- All integer arithmetic lemmas intact

---

### Phase 4: Duality.lean -- Temporal Duality [COMPLETED]

**Goal**: Port IntStructure.reverse, swap_temporal_int_truth, and duality preservation lemmas. Leverage cslib's existing `Formula.swap_temporal` and its involution/simp lemmas.

**Tasks**:
- [ ] Create `Cslib/Logics/Bimodal/Metalogic/Separation/Duality.lean`
- [ ] Port `IntStructure.reverse` with parameterized Atom
- [ ] Port `IntStructure.reverse_reverse`
- [ ] Port `swap_temporal_int_truth` -- reference cslib's `Formula.swap_temporal` via `open Cslib.Logic.Bimodal`
- [ ] Port `dual_equiv`, `dual_U_free_iff_S_free`, `dual_separated`
- [ ] Port boolean closure lemmas for purity predicates
- [ ] Update imports; open `Cslib.Logic.Bimodal` for swap_temporal access
- [ ] Verify `lake build Cslib.Logics.Bimodal.Metalogic.Separation.Duality`

**Timing**: 1.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/Separation/Duality.lean` -- create (342 lines source)

**Verification**:
- File compiles with zero errors
- `swap_temporal_int_truth` references cslib's `Formula.swap_temporal` (not a local copy)

---

### Phase 5: Distributivity.lean -- Lemma 10.2.1 [COMPLETED]

**Goal**: Port the four distributivity theorems (U/S distribute over boolean ops).

**Tasks**:
- [ ] Create `Cslib/Logics/Bimodal/Metalogic/Separation/Distributivity.lean`
- [ ] Port `until_distrib_or_left`, `since_distrib_or_left`
- [ ] Port `until_distrib_and_right`, `since_distrib_and_right`
- [ ] Parameterize all formulas as `Formula Atom`
- [ ] Verify `lake build Cslib.Logics.Bimodal.Metalogic.Separation.Distributivity`

**Timing**: 0.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/Separation/Distributivity.lean` -- create (188 lines source)

**Verification**:
- File compiles with zero errors
- All four distributivity theorems present

---

### Phase 6: NegationEquiv.lean -- Lemma 10.2.2 [COMPLETED]

**Goal**: Port the Z-dependent negation equivalences (neg_until_equiv, neg_since_equiv). These are the key integer-specific step using discreteness of Z.

**Tasks**:
- [ ] Create `Cslib/Logics/Bimodal/Metalogic/Separation/NegationEquiv.lean`
- [ ] Port `neg_until_equiv` with parameterized Atom
- [ ] Port `neg_since_equiv`
- [ ] Import Duality and IntHelpers from Cslib paths
- [ ] Verify `lake build Cslib.Logics.Bimodal.Metalogic.Separation.NegationEquiv`

**Timing**: 0.5 hours

**Depends on**: 3, 4

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/Separation/NegationEquiv.lean` -- create (159 lines source)

**Verification**:
- File compiles with zero errors
- Both negation equivalences proven without sorry

---

### Phase 7: Eliminations.lean -- Lemma 10.2.3 [COMPLETED]

**Goal**: Port the 8 elimination cases that form the core of the separation proof (pulling U out from under S).

**Tasks**:
- [ ] Create `Cslib/Logics/Bimodal/Metalogic/Separation/Eliminations.lean`
- [ ] Port all 8 elimination case theorems with parameterized Atom
- [ ] Replace `open Classical` with appropriate classical reasoning pattern (e.g., `open Classical in` or section-scoped)
- [ ] Import NegationEquiv, Distributivity, IntHelpers from Cslib paths
- [ ] Verify `lake build Cslib.Logics.Bimodal.Metalogic.Separation.Eliminations`

**Timing**: 2 hours

**Depends on**: 5, 6

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/Separation/Eliminations.lean` -- create (902 lines source)

**Verification**:
- File compiles with zero errors
- All 8 elimination cases present
- Zero sorry occurrences

---

### Phase 8: DedekindZ -- QLemma and Cases [COMPLETED]

**Goal**: Port the DedekindZ subdirectory: K+/K- operators, Q-lemma, and Cases 5-8 separability proofs.

**Tasks**:
- [ ] Create directory `Cslib/Logics/Bimodal/Metalogic/Separation/DedekindZ/`
- [ ] Create `Cslib/Logics/Bimodal/Metalogic/Separation/DedekindZ/QLemma.lean`
- [ ] Port K+/K- operator definitions with parameterized Atom
- [ ] Port Q-lemma (forward and backward)
- [ ] Port Q_Z syntactic properties and Case 3 equivalence
- [ ] Create `Cslib/Logics/Bimodal/Metalogic/Separation/DedekindZ/Cases.lean`
- [ ] Port Replace-U infrastructure and congruence lemmas
- [ ] Port Cases 5-8 separability proofs
- [ ] Import QLemma, Eliminations, NegationEquiv from Cslib paths
- [ ] Verify `lake build Cslib.Logics.Bimodal.Metalogic.Separation.DedekindZ.QLemma`
- [ ] Verify `lake build Cslib.Logics.Bimodal.Metalogic.Separation.DedekindZ.Cases`

**Timing**: 2 hours

**Depends on**: 7

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/Separation/DedekindZ/QLemma.lean` -- create (459 lines source)
- `Cslib/Logics/Bimodal/Metalogic/Separation/DedekindZ/Cases.lean` -- create (1768 lines source)

**Verification**:
- Both files compile with zero errors
- Cases 5-8 all proven without sorry
- Zero axiom declarations

---

### Phase 9: NormalForm.lean -- Lemma 10.2.4 [COMPLETED]

**Goal**: Port normal form reduction using the 8 elimination cases and DedekindZ Cases.

**Tasks**:
- [ ] Create `Cslib/Logics/Bimodal/Metalogic/Separation/NormalForm.lean`
- [ ] Port normal form reduction theorem with parameterized Atom
- [ ] Import Eliminations, Distributivity, DedekindZ.Cases from Cslib paths
- [ ] Verify `lake build Cslib.Logics.Bimodal.Metalogic.Separation.NormalForm`

**Timing**: 1.5 hours

**Depends on**: 5, 8

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/Separation/NormalForm.lean` -- create (554 lines source)

**Verification**:
- File compiles with zero errors
- Normal form reduction theorem proven

---

### Phase 10: TemporalClosure.lean -- Temporal Closure Infrastructure [COMPLETED]

**Goal**: Port temporal closure predicates and infrastructure (replace_box_with_top, no_U/S_nested predicates).

**Tasks**:
- [ ] Create `Cslib/Logics/Bimodal/Metalogic/Separation/TemporalClosure.lean`
- [ ] Port all temporal closure definitions with parameterized Atom
- [ ] Port `replace_box_with_top`, `has_no_allpast_allfuture`
- [ ] Port `no_U_nested_in_S`, `no_S_nested_in_U` and their properties
- [ ] Import Defs and Duality from Cslib paths
- [ ] Verify `lake build Cslib.Logics.Bimodal.Metalogic.Separation.TemporalClosure`

**Timing**: 1.5 hours

**Depends on**: 1, 4

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/Separation/TemporalClosure.lean` -- create (674 lines source)

**Verification**:
- File compiles with zero errors
- All temporal closure predicates and lemmas present

---

### Phase 11: Hierarchy/HierarchyDefs.lean -- Hierarchy Definitions [COMPLETED]

**Goal**: Port has_single_U_type, U/S-formula abstraction, junction-depth monotonicity, and related definitions.

**Tasks**:
- [ ] Create directory `Cslib/Logics/Bimodal/Metalogic/Separation/Hierarchy/`
- [ ] Create `Cslib/Logics/Bimodal/Metalogic/Separation/Hierarchy/HierarchyDefs.lean`
- [ ] Port `has_single_U_type` and related predicates with parameterized Atom
- [ ] Port U/S-formula abstraction definitions
- [ ] Port junction-depth monotonicity lemmas
- [ ] Port semantic correctness and preservation lemmas
- [ ] Import NormalForm, TemporalClosure, DedekindZ.Cases, FormulaOps from Cslib paths
- [ ] Verify `lake build Cslib.Logics.Bimodal.Metalogic.Separation.Hierarchy.HierarchyDefs`

**Timing**: 2 hours

**Depends on**: 9, 10

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/Separation/Hierarchy/HierarchyDefs.lean` -- create (1051 lines source)

**Verification**:
- File compiles with zero errors
- All hierarchy definitions present
- Atom parameterization consistent with upstream modules

---

### Phase 12: Hierarchy/HierarchyCaseSep.lean -- Case-Specific Separability [COMPLETED]

**Goal**: Port case-specific is_separable_with_U_type theorems (extracted to break circular dependency).

**Tasks**:
- [ ] Create `Cslib/Logics/Bimodal/Metalogic/Separation/Hierarchy/HierarchyCaseSep.lean`
- [ ] Port all case-specific separability theorems
- [ ] Import HierarchyDefs from Cslib path
- [ ] Verify `lake build Cslib.Logics.Bimodal.Metalogic.Separation.Hierarchy.HierarchyCaseSep`

**Timing**: 1.5 hours

**Depends on**: 11

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/Separation/Hierarchy/HierarchyCaseSep.lean` -- create (655 lines source)

**Verification**:
- File compiles with zero errors
- All case-specific separability theorems present

---

### Phase 13: Hierarchy/HierarchyInduction.lean and HierarchyCompletion.lean [COMPLETED]

**Goal**: Port the substitution-based induction engine (Steps 1-5b) and the hierarchy completion (Steps 5c-5d, all_formulas_separable).

**Tasks**:
- [ ] Create `Cslib/Logics/Bimodal/Metalogic/Separation/Hierarchy/HierarchyInduction.lean`
- [ ] Port substitution preservation theorems
- [ ] Port strict count decrease lemmas
- [ ] Port `noncomputable def extract_innermost_U_type` with `[DecidableEq Atom] [Infinite Atom]`
- [ ] Port `noncomputable def extract_U_type` with same constraints
- [ ] Port S/U-nesting depth measures and callback infrastructure
- [ ] Import HierarchyDefs and HierarchyCaseSep from Cslib paths
- [ ] Verify `lake build Cslib.Logics.Bimodal.Metalogic.Separation.Hierarchy.HierarchyInduction`
- [ ] Create `Cslib/Logics/Bimodal/Metalogic/Separation/Hierarchy/HierarchyCompletion.lean`
- [ ] Port U-type-preserving separation and `separable_with_U_type` strengthening
- [ ] Port combinators and Cases 5-8 with U-type preservation
- [ ] Port single-U-type separability (axiom-free)
- [ ] Port GHR94 Lemma 10.2.6/10.2.7
- [ ] Port `all_formulas_separable` -- the master separation theorem
- [ ] Import HierarchyInduction from Cslib path
- [ ] Verify `lake build Cslib.Logics.Bimodal.Metalogic.Separation.Hierarchy.HierarchyCompletion`

**Timing**: 2.5 hours

**Depends on**: 12

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/Separation/Hierarchy/HierarchyInduction.lean` -- create (1437 lines source)
- `Cslib/Logics/Bimodal/Metalogic/Separation/Hierarchy/HierarchyCompletion.lean` -- create (981 lines source)

**Verification**:
- Both files compile with zero errors
- `all_formulas_separable` theorem is proven
- `extract_innermost_U_type` and `extract_U_type` are noncomputable
- Zero sorry, zero axiom

---

### Phase 14: SeparationThm.lean and DualEliminations.lean -- Final Wrappers [COMPLETED]

**Goal**: Port the separation theorem wrapper (Theorem 10.2.9 corollaries, temporal closure corollaries, atom-preserving separation) and the dual elimination cases.

**Tasks**:
- [ ] Create `Cslib/Logics/Bimodal/Metalogic/Separation/SeparationThm.lean`
- [ ] Port congruence helpers (all_past_congr, all_future_congr)
- [ ] Port GHR94 Theorem 10.2.9 wrapper
- [ ] Port temporal closure corollaries
- [ ] Port atom-preserving separation theorem
- [ ] Import Defs, Eliminations, FormulaOps, Distributivity, Duality, HierarchyCompletion
- [ ] Create `Cslib/Logics/Bimodal/Metalogic/Separation/DualEliminations.lean`
- [ ] Port dual elimination cases (S out of U) that follow from all_formulas_separable + duality
- [ ] Import Eliminations, Duality, SeparationThm
- [ ] Verify `lake build Cslib.Logics.Bimodal.Metalogic.Separation.SeparationThm`
- [ ] Verify `lake build Cslib.Logics.Bimodal.Metalogic.Separation.DualEliminations`

**Timing**: 1.5 hours

**Depends on**: 7, 13

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/Separation/SeparationThm.lean` -- create (354 lines source)
- `Cslib/Logics/Bimodal/Metalogic/Separation/DualEliminations.lean` -- create (101 lines source)

**Verification**:
- Both files compile with zero errors
- Separation theorem (all_formulas_separable) is accessible
- Dual elimination cases follow from the master theorem

---

### Phase 15: Barrel Import and Final Verification [COMPLETED]

**Goal**: Create the barrel import file, run full lake build, verify zero sorry/axiom across all files.

**Tasks**:
- [ ] Create `Cslib/Logics/Bimodal/Metalogic/Separation.lean` (barrel file)
- [ ] Import all 15 core files (13 direct + transitive coverage for QLemma, Cases, HierarchyCaseSep, TemporalClosure)
- [ ] Run `lake build` for full project verification
- [ ] Run `grep -rn "sorry" Cslib/Logics/Bimodal/Metalogic/Separation/` to confirm zero sorry
- [ ] Run `grep -rn "axiom " Cslib/Logics/Bimodal/Metalogic/Separation/` to confirm zero axioms
- [ ] Verify all 15 files + barrel have Apache 2.0 copyright headers
- [ ] Verify all files use `Cslib.Logic.Bimodal.Metalogic.Separation` namespace

**Timing**: 0.5 hours

**Depends on**: 14

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/Separation.lean` -- create (barrel)

**Verification**:
- Full `lake build` passes with zero errors
- Zero sorry across all separation files
- Zero axiom declarations across all separation files
- Barrel imports compile and expose all public API

## Porting Checklist (Applied Per-File)

Every file in Phases 1-14 must satisfy:
1. Rename namespace: `Bimodal.Metalogic.WeakCanonical.Separation` to `Cslib.Logic.Bimodal.Metalogic.Separation`
2. Add Apache 2.0 copyright header (matching `Cslib/Logics/Bimodal/Metalogic/Core/MCSProperties.lean` format)
3. Replace `import Bimodal.*` with `import Cslib.Logics.Bimodal.*`
4. Replace `open Bimodal.Syntax` with `open Cslib.Logic.Bimodal`
5. Parameterize `Formula` as `Formula Atom` where `{Atom : Type*}`
6. Add `[DecidableEq Atom]` where `.atoms` (Finset) or substitution is used
7. Add `[Infinite Atom]` where freshness (`fresh_atom`, `fresh_atoms`) is used
8. Add `set_option linter.style.emptyLine false` and `set_option linter.flexible false`
9. Verify `lake build ModuleName` passes with zero errors
10. Confirm zero sorry occurrences

## Testing & Validation

- [ ] Each phase builds independently via `lake build Cslib.Logics.Bimodal.Metalogic.Separation.{Module}`
- [ ] Full project `lake build` passes after Phase 15
- [ ] Zero sorry across all 15 ported files
- [ ] Zero axiom declarations across all 15 ported files
- [ ] 4 noncomputable definitions preserved (fresh_atom, fresh_atoms, extract_innermost_U_type, extract_U_type)
- [ ] `all_formulas_separable` theorem is accessible from barrel import
- [ ] Atom parameterization consistent: `{Atom : Type*}` with appropriate typeclass constraints

## Artifacts & Outputs

- `Cslib/Logics/Bimodal/Metalogic/Separation/Defs.lean`
- `Cslib/Logics/Bimodal/Metalogic/Separation/FormulaOps.lean`
- `Cslib/Logics/Bimodal/Metalogic/Separation/IntHelpers.lean`
- `Cslib/Logics/Bimodal/Metalogic/Separation/Duality.lean`
- `Cslib/Logics/Bimodal/Metalogic/Separation/Distributivity.lean`
- `Cslib/Logics/Bimodal/Metalogic/Separation/NegationEquiv.lean`
- `Cslib/Logics/Bimodal/Metalogic/Separation/Eliminations.lean`
- `Cslib/Logics/Bimodal/Metalogic/Separation/DedekindZ/QLemma.lean`
- `Cslib/Logics/Bimodal/Metalogic/Separation/DedekindZ/Cases.lean`
- `Cslib/Logics/Bimodal/Metalogic/Separation/NormalForm.lean`
- `Cslib/Logics/Bimodal/Metalogic/Separation/TemporalClosure.lean`
- `Cslib/Logics/Bimodal/Metalogic/Separation/Hierarchy/HierarchyDefs.lean`
- `Cslib/Logics/Bimodal/Metalogic/Separation/Hierarchy/HierarchyCaseSep.lean`
- `Cslib/Logics/Bimodal/Metalogic/Separation/Hierarchy/HierarchyInduction.lean`
- `Cslib/Logics/Bimodal/Metalogic/Separation/Hierarchy/HierarchyCompletion.lean`
- `Cslib/Logics/Bimodal/Metalogic/Separation/SeparationThm.lean`
- `Cslib/Logics/Bimodal/Metalogic/Separation/DualEliminations.lean`
- `Cslib/Logics/Bimodal/Metalogic/Separation.lean` (barrel)

## Rollback/Contingency

- All new files are in `Cslib/Logics/Bimodal/Metalogic/Separation/` -- rollback is `rm -rf Cslib/Logics/Bimodal/Metalogic/Separation/ Cslib/Logics/Bimodal/Metalogic/Separation.lean`
- No existing files are modified; the port is purely additive
- If a phase blocks on Mathlib API differences, mark phase `[BLOCKED]` and continue with independent phases in the same or later waves
- If Atom parameterization causes cascading issues, fall back to a concrete Atom type matching the source and refactor later
