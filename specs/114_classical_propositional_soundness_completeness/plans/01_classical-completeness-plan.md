# Implementation Plan: Task #114

- **Task**: 114 - Classical propositional soundness and completeness
- **Status**: [NOT STARTED]
- **Effort**: 4 hours
- **Dependencies**: None (uses existing DerivationTree, MCS infrastructure; does NOT depend on task 113 refactoring)
- **Research Inputs**: specs/114_classical_propositional_soundness_completeness/reports/01_classical-completeness-research.md
- **Artifacts**: plans/01_classical-completeness-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: true

## Overview

Create three new Lean files implementing bivalent truth-value semantics, soundness, and completeness for classical propositional logic (HilbertCl). The propositional case is a direct simplification of the existing modal K completeness (KCompleteness.lean): no box constructor, no accessibility relation, no canonical model structure, no axiom hypothesis threading. All required MCS infrastructure already exists via `prop_lindenbaum`, `prop_closed_under_derivation`, `prop_implication_property`, `prop_negation_complete`, and `prop_mcs_bot_not_mem`.

### Research Integration

The research report confirms:
- `Valuation` should be `abbrev Valuation (Atom : Type*) := Atom -> Prop` for definitional transparency.
- `Evaluate` is a 3-case recursive function on `Proposition` (atom/bot/imp), mirroring modal `Satisfies` without the box case.
- Soundness has 4 axiom cases (K, S, EFQ, Peirce) and 4 derivation tree cases (ax, assumption, modus_ponens, weakening).
- Completeness follows the k_completeness pattern: contraposition, show `{neg phi}` consistent, Lindenbaum to MCS, truth lemma to contradiction.
- The truth lemma imp-forward case is the hardest part, requiring explicit `DerivationTree` construction using EFQ + Peirce (same derivation as KCompleteness.lean lines 198-217 and 228-240, but with `PropositionalAxiom` directly instead of axiom hypothesis callbacks).
- The propositional MCS API (`prop_*` functions) is monomorphic, eliminating all axiom hypothesis threading present in the modal version.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No specific ROADMAP.md items identified for this task (propositional completeness subtask of parent task 112).

## Goals & Non-Goals

**Goals**:
- Define `Valuation`, `Evaluate`, `Tautology` in `Semantics/Basic.lean`
- Prove `prop_axiom_sound` and `prop_soundness` in `Metalogic/Soundness.lean`
- Define `canonicalValuation` and prove `prop_truth_lemma` and `prop_completeness` in `Metalogic/Completeness.lean`
- All files build successfully with `lake build`
- Zero `sorry` occurrences

**Non-Goals**:
- Modifying any existing files (Defs.lean, Axioms.lean, Derivation.lean, MCS.lean, DeductionTheorem.lean)
- Adding Cslib.lean imports (deferred to task 118: integration)
- Handling intuitionistic or minimal logic (tasks 115-117)
- Refactoring DerivationTree to be axiom-parameterized (task 113)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Truth lemma imp-forward case complexity | M | M | Follow KCompleteness.lean lines 198-240 exactly, adapting `PropositionalAxiom` constructors |
| `propDerivationSystem.Deriv` vs `Deriv` bridging | L | M | Use `Nonempty.intro` / angle brackets as demonstrated in MCS.lean line 97-98 |
| Universe polymorphism issues with `Valuation` | L | L | Use `Type*` consistently, matching existing `Proposition (Atom : Type u)` pattern |
| Completeness consistency argument derivation chain | M | L | Copy derivation chain from k_completeness lines 274-307, substitute `PropositionalAxiom.*` for `KAxiom.*` |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 1, 2 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Semantics/Basic.lean [COMPLETED]

**Goal**: Create the semantic definitions for bivalent propositional logic: Valuation, Evaluate, Tautology.

**Tasks**:
- [ ] Create file `Cslib/Logics/Propositional/Semantics/Basic.lean` with copyright header and module declaration
- [ ] Import `Cslib.Logics.Propositional.Defs`
- [ ] Define `abbrev Valuation (Atom : Type*) := Atom -> Prop` in namespace `Cslib.Logic.PL`
- [ ] Define `def Evaluate (v : Valuation Atom) : PL.Proposition Atom -> Prop` with 3 cases: `.atom x => v x`, `.bot => False`, `.imp a b => Evaluate v a -> Evaluate v b`
- [ ] Define `def Tautology (phi : PL.Proposition Atom) : Prop := forall (v : Valuation Atom), Evaluate v phi`
- [ ] Verify file builds: `lake build Cslib.Logics.Propositional.Semantics.Basic`

**Timing**: 0.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Basic.lean` - CREATE: Valuation, Evaluate, Tautology definitions (~40-50 lines)

**Verification**:
- `lake build Cslib.Logics.Propositional.Semantics.Basic` succeeds
- `lean_verify` on `Evaluate` confirms no sorry/axioms
- `lean_goal` confirms `Evaluate` reduces correctly on all 3 cases

---

### Phase 2: Metalogic/Soundness.lean [COMPLETED]

**Goal**: Prove soundness of classical propositional logic: every derivable formula is a tautology.

**Tasks**:
- [ ] Create file `Cslib/Logics/Propositional/Metalogic/Soundness.lean` with copyright header
- [ ] Import `Cslib.Logics.Propositional.Semantics.Basic` and `Cslib.Logics.Propositional.ProofSystem.Derivation`
- [ ] Prove `theorem prop_axiom_sound` by cases on `PropositionalAxiom`:
  - `implyK`: `intro h_phi _; exact h_phi`
  - `implyS`: `intro h1 h2 h3; exact h1 h3 (h2 h3)`
  - `efq`: `intro h; exact absurd h id`
  - `peirce`: `intro h; by_contra h_not; exact h_not (h (fun h_phi => absurd h_phi h_not))`
- [ ] Prove `theorem prop_soundness` by match on `DerivationTree` (4 constructors):
  - `.ax`: apply `prop_axiom_sound`
  - `.assumption`: context lookup
  - `.modus_ponens`: recursive calls
  - `.weakening`: recursive call with subset
- [ ] Prove `theorem prop_soundness_derivable` wrapper for empty context
- [ ] Prove `theorem soundness_tautology : Derivable phi -> Tautology phi` wrapper
- [ ] Verify file builds: `lake build Cslib.Logics.Propositional.Metalogic.Soundness`

**Timing**: 1 hour

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/Metalogic/Soundness.lean` - CREATE: prop_axiom_sound, prop_soundness, wrappers (~50-70 lines)

**Verification**:
- `lake build Cslib.Logics.Propositional.Metalogic.Soundness` succeeds
- `lean_verify` on `prop_soundness` and `soundness_tautology` confirms no sorry
- All 4 axiom cases and 4 derivation tree cases handled

---

### Phase 3: Metalogic/Completeness.lean [COMPLETED]

**Goal**: Prove completeness of classical propositional logic: every tautology is derivable.

**Tasks**:
- [ ] Create file `Cslib/Logics/Propositional/Metalogic/Completeness.lean` with copyright header
- [ ] Import `Cslib.Logics.Propositional.Semantics.Basic` and `Cslib.Logics.Propositional.Metalogic.MCS`
- [ ] Define `def canonicalValuation (S : Set (PL.Proposition Atom)) : Valuation Atom := fun p => Proposition.atom p in S`
- [ ] Prove `theorem prop_truth_lemma` by structural recursion on `phi` (3 cases):
  - `.atom p`: Both directions by definition/identity
  - `.bot`: Forward vacuous (False -> anything), backward contradicts `prop_mcs_bot_not_mem`
  - `.imp phi psi` forward: Use `prop_negation_complete` on `phi.imp psi`, if `neg (phi.imp psi) in S` then derive `phi in S` via EFQ+Peirce derivation (adapt KCompleteness lines 198-217), get `Evaluate v phi` by IH backward, get `Evaluate v psi` by assumption, get `psi in S` by IH forward, derive `neg psi in S` via implyK derivation (adapt KCompleteness lines 228-240), contradiction via `prop_implication_property` + `prop_mcs_bot_not_mem`
  - `.imp phi psi` backward: Use `prop_implication_property` + IH both directions
- [ ] Prove `theorem prop_completeness (phi : PL.Proposition Atom) (h_taut : Tautology phi) : Derivable phi` by contraposition:
  - Assume `not (Derivable phi)`
  - Show `{Proposition.neg phi}` is `PropSetConsistent` (adapt k_completeness lines 274-307: deduction theorem gives `[] |- neg phi -> bot`, then EFQ+implyK+implyS+Peirce derivation chain to get `[] |- phi`, contradiction)
  - `prop_lindenbaum` to extend to MCS `M`
  - `neg phi in M` from subset
  - `canonicalValuation M` + `prop_truth_lemma` backward gives `Evaluate v (neg phi)`
  - `h_taut` gives `Evaluate v phi`, contradiction
- [ ] Prove `theorem completeness_iff_tautology : Tautology phi <-> Derivable phi` biconditional wrapper using soundness_tautology + prop_completeness
- [ ] Verify file builds: `lake build Cslib.Logics.Propositional.Metalogic.Completeness`

**Timing**: 2.5 hours

**Depends on**: 1, 2

**Files to modify**:
- `Cslib/Logics/Propositional/Metalogic/Completeness.lean` - CREATE: canonicalValuation, prop_truth_lemma, prop_completeness, completeness_iff_tautology (~100-130 lines)

**Verification**:
- `lake build Cslib.Logics.Propositional.Metalogic.Completeness` succeeds
- `lean_verify` on `prop_completeness` and `completeness_iff_tautology` confirms no sorry and no non-standard axioms (only Classical.choice/propDecidable expected)
- Truth lemma covers all 3 cases (atom/bot/imp) with both directions

## Testing & Validation

- [ ] `lake build Cslib.Logics.Propositional.Semantics.Basic` succeeds (Phase 1)
- [ ] `lake build Cslib.Logics.Propositional.Metalogic.Soundness` succeeds (Phase 2)
- [ ] `lake build Cslib.Logics.Propositional.Metalogic.Completeness` succeeds (Phase 3)
- [ ] `lean_verify` on `prop_completeness` shows no sorry, no non-standard axioms
- [ ] `lean_verify` on `completeness_iff_tautology` shows no sorry
- [ ] Zero sorry occurrences across all 3 files: `grep -r sorry Cslib/Logics/Propositional/Semantics/Basic.lean Cslib/Logics/Propositional/Metalogic/Soundness.lean Cslib/Logics/Propositional/Metalogic/Completeness.lean`

## Artifacts & Outputs

- `Cslib/Logics/Propositional/Semantics/Basic.lean` - Valuation, Evaluate, Tautology
- `Cslib/Logics/Propositional/Metalogic/Soundness.lean` - prop_axiom_sound, prop_soundness, soundness_tautology
- `Cslib/Logics/Propositional/Metalogic/Completeness.lean` - canonicalValuation, prop_truth_lemma, prop_completeness, completeness_iff_tautology

## Rollback/Contingency

All 3 files are new creations with no modifications to existing files. Rollback is simply deleting the 3 new files:
```bash
rm -f Cslib/Logics/Propositional/Semantics/Basic.lean
rm -f Cslib/Logics/Propositional/Metalogic/Soundness.lean
rm -f Cslib/Logics/Propositional/Metalogic/Completeness.lean
```
If Phase 3 (completeness) encounters difficulties, Phases 1-2 (semantics + soundness) can be committed independently as partial progress.
