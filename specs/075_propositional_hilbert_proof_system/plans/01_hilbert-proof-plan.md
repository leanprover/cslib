# Implementation Plan: Task #75

- **Task**: 75 - Develop propositional Hilbert proof system and derive natural deduction rules
- **Status**: [NOT STARTED]
- **Effort**: 10 hours
- **Dependencies**: None
- **Research Inputs**: specs/075_propositional_hilbert_proof_system/reports/01_hilbert-proof-system.md
- **Artifacts**: plans/01_hilbert-proof-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: true

## Overview

Create a Hilbert-style proof system for propositional logic following the established Modal/Temporal/Bimodal pattern, then derive natural deduction rules as thin wrappers. The implementation mirrors `Cslib/Logics/Modal/Metalogic/` exactly: define axiom schemata, build a `DerivationTree` with 4 constructors (ax, assumption, modus_ponens, weakening -- no necessitation), register `InferenceSystem`/`PropositionalHilbert` instances for the existing `Propositional.HilbertCl` tag, prove the deduction theorem, instantiate the generic MCS framework, and finally provide ND-flavored lemma names as wrappers. The propositional case is simpler than Modal because there is no necessitation rule, which eliminates the empty-context constraint.

### Research Integration

Key findings from the research report integrated into this plan:
- The `PropositionalHilbert` class and `Propositional.HilbertCl` opaque tag type already exist in `ProofSystem.lean` but have no concrete instances (Section 2.3).
- The `DerivationTree` needs exactly 4 constructors, mirroring Modal minus necessitation (Section 2.2).
- The deduction theorem is strictly simpler than Modal's because there is no necessitation case to handle (Section 6).
- The existing `NaturalDeduction/Basic.lean` should coexist; new ND-flavored names are provided via a separate `FromHilbert.lean` file (Section 3.3).
- No changes to Modal/Temporal/Bimodal imports are needed in this task (Section 4.3).
- `PropositionalConnectives` is already registered with `{ bot := .bot, imp := .imp }`, so definitional equality with `Axioms.lean` formulas holds (Section 5.2, risk 1).

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This plan advances the Propositional layer in the module dependency structure described in `ROADMAP.md`. Specifically, it fills the gap where Propositional currently provides only formula definitions and a standalone ND system, and has no Hilbert proof infrastructure. After this task, Propositional becomes a genuine proof-theoretic foundation matching the pattern of Modal/Temporal/Bimodal.

## Goals & Non-Goals

**Goals**:
- Create `ProofSystem/Axioms.lean` with `PropositionalAxiom` inductive (4 constructors)
- Create `ProofSystem/Derivation.lean` with `DerivationTree`, `height`, `Deriv`, `DerivationSystem`
- Create `ProofSystem/Instances.lean` with `InferenceSystem`/`PropositionalHilbert` instances for `Propositional.HilbertCl`
- Create `Metalogic/DeductionTheorem.lean` proving deduction theorem via well-founded recursion
- Create `Metalogic/MCS.lean` instantiating generic MCS framework
- Create `NaturalDeduction/FromHilbert.lean` with ND-flavored wrapper lemmas
- Derive cut, weakening, and substitution within the Hilbert framework
- Each phase independently verifiable via `lake build`

**Non-Goals**:
- Refactoring Modal/Temporal/Bimodal to import from the new Propositional Hilbert system (follow-up task)
- Derivation lifting through `FromPropositional.lean` embeddings (follow-up task)
- Theory-parameterized variant of `DerivationTree` (deferred; the fixed 4-axiom set suffices)
- Deleting or deprecating the existing `NaturalDeduction/Basic.lean` (coexistence)
- Soundness or completeness theorems for propositional logic

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Definitional mismatch between `PL.Proposition.imp`/`.bot` and `HasImp.imp`/`HasBot.bot` | M | L | `PropositionalConnectives` instance already maps these; verify in Phase 3 |
| `height`-based termination fails for deduction theorem | H | L | Follow Modal's exact `termination_by`/`decreasing_by` pattern |
| Generic `Foundations/Logic/Theorems/` combinators do not auto-apply for `Propositional.HilbertCl` | M | L | Phase 3 explicitly tests this; fallback is manual instance registration |
| Build failures from import cycles | M | L | New files only import downward (Defs, Foundations); no upward imports |

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

### Phase 1: Axioms and DerivationTree [COMPLETED]

**Goal**: Define the propositional axiom schemata and derivation tree type, mirroring `Modal/Metalogic/DerivationTree.lean`.

**Tasks**:
- [x] Create `Cslib/Logics/Propositional/ProofSystem/Axioms.lean`
  - Add copyright header and `module` keyword
  - Import `Cslib.Logics.Propositional.Defs`
  - Define `PropositionalAxiom : PL.Proposition Atom -> Prop` with 4 constructors: `implyK`, `implyS`, `efq`, `peirce`
  - Use `@[expose] public section` pattern
- [x] Create `Cslib/Logics/Propositional/ProofSystem/Derivation.lean`
  - Import `Cslib.Logics.Propositional.ProofSystem.Axioms` and `Cslib.Foundations.Logic.Metalogic.Consistency`
  - Define `DerivationTree : List (PL.Proposition Atom) -> PL.Proposition Atom -> Type _` with 4 constructors: `ax`, `assumption`, `modus_ponens`, `weakening` (no necessitation)
  - Define `DerivationTree.height : DerivationTree Gamma phi -> Nat` with the same pattern as Modal
  - Prove `height_modus_ponens_left`, `height_modus_ponens_right`, `height_weakening`
  - Define `Deriv` (Nonempty wrapper), `Derivable` (empty context)
  - Define `mp_deriv`, `weakening_deriv`, `assumption_deriv` combinators
  - Define `propDerivationSystem : Metalogic.DerivationSystem (PL.Proposition Atom)`

**Timing**: 1.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/ProofSystem/Axioms.lean` - new file
- `Cslib/Logics/Propositional/ProofSystem/Derivation.lean` - new file

**Verification**:
- `lake build Cslib.Logics.Propositional.ProofSystem.Axioms`
- `lake build Cslib.Logics.Propositional.ProofSystem.Derivation`
- No `sorry` in either file

---

### Phase 2: Instance Registration [COMPLETED]

**Goal**: Register `InferenceSystem`, `ModusPonens`, and all `HasAxiom*` instances for `Propositional.HilbertCl`, enabling all generic Foundations theorems.

**Tasks**:
- [x] Create `Cslib/Logics/Propositional/ProofSystem/Instances.lean`
  - Import `Cslib.Logics.Propositional.ProofSystem.Derivation` and `Cslib.Foundations.Logic.ProofSystem`
  - Register `InferenceSystem Propositional.HilbertCl (PL.Proposition Atom)` mapping tag to `DerivationTree [] phi`
  - Register `ModusPonens Propositional.HilbertCl` via constructing `DerivationTree` from two derivations using `modus_ponens`
  - Register `HasAxiomImplyK Propositional.HilbertCl` via `DerivationTree.ax [] _ (.implyK phi psi)`
  - Register `HasAxiomImplyS Propositional.HilbertCl` via `DerivationTree.ax [] _ (.implyS phi psi chi)`
  - Register `HasAxiomEFQ Propositional.HilbertCl` via `DerivationTree.ax [] _ (.efq phi)`
  - Register `HasAxiomPeirce Propositional.HilbertCl` via `DerivationTree.ax [] _ (.peirce phi psi)`
  - Register `PropositionalHilbert Propositional.HilbertCl` (auto-synthesized from above)
- [x] Verify that generic theorems from `Foundations/Logic/Theorems/Combinators.lean` and `Foundations/Logic/Theorems/Propositional/Core.lean` are now available for `Propositional.HilbertCl`
  - Add a brief `#check` or `example` confirming `imp_trans` works at this tag type *(deviation: altered -- verified via lean_hover_info that PropositionalHilbert synthesizes; no in-file #check added to avoid non-essential code)*

**Timing**: 1.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/ProofSystem/Instances.lean` - new file

**Verification**:
- `lake build Cslib.Logics.Propositional.ProofSystem.Instances`
- All instances synthesize without error
- Generic combinators apply to `Propositional.HilbertCl`

---

### Phase 3: Deduction Theorem [COMPLETED]

**Goal**: Prove the deduction theorem for propositional logic by well-founded recursion on `DerivationTree.height`, following Modal's exact structure minus the necessitation case.

**Tasks**:
- [x] Create `Cslib/Logics/Propositional/Metalogic/DeductionTheorem.lean`
  - Import `Cslib.Logics.Propositional.ProofSystem.Derivation`
  - Define `removeAll` helper and supporting lemmas (`removeAll_subset_of_subset`, `mem_removeAll_of_mem_of_ne`, `removeAll_subset_removeAll`) -- identical to Modal
  - Define `deduction_axiom`: if phi is an axiom, then `Gamma |- A -> phi`
  - Define `deduction_imp_self`: `Gamma |- A -> A` (SKK construction)
  - Define `deduction_assumption_other`: if `B in Gamma`, then `Gamma |- A -> B`
  - Define `deduction_mp`: from `Gamma |- A -> (C -> D)` and `Gamma |- A -> C`, derive `Gamma |- A -> D`
  - Define `deduction_with_mem`: if `Gamma' |- phi` and `A in Gamma'`, then `removeAll Gamma' A |- A -> phi`
  - Prove `deduction_theorem`: if `A :: Gamma |- B` then `Gamma |- A -> B`
    - Use `termination_by d.height` and `decreasing_by` with `simp_wf` + height lemmas
    - Handle 4 cases: `ax`, `assumption`, `modus_ponens`, `weakening` (no `necessitation` case)
  - Prove `prop_has_deduction_theorem : Metalogic.HasDeductionTheorem propDerivationSystem`

**Timing**: 2 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Propositional/Metalogic/DeductionTheorem.lean` - new file

**Verification**:
- `lake build Cslib.Logics.Propositional.Metalogic.DeductionTheorem`
- `prop_has_deduction_theorem` has no sorry
- Termination checker accepts the well-founded recursion

---

### Phase 4: MCS Properties [COMPLETED]

**Goal**: Instantiate the generic MCS framework from `Foundations/Logic/Metalogic/Consistency.lean` for propositional logic and prove propositional-specific MCS properties.

**Tasks**:
- [x] Create `Cslib/Logics/Propositional/Metalogic/MCS.lean`
  - Import `Cslib.Logics.Propositional.Metalogic.DeductionTheorem`
  - Define abbreviations `PropSetConsistent` and `PropSetMaximalConsistent` for the propositional derivation system *(deviation: altered -- renamed from `PL.SetConsistent`/`PL.SetMaximalConsistent` to avoid duplicate namespace `PL.PL.*`)*
  - Prove `prop_lindenbaum`: Lindenbaum's lemma for propositional logic (delegate to `Metalogic.set_lindenbaum`)
  - Prove `prop_closed_under_derivation`: derivable formulas are in MCS (delegate to `Metalogic.SetMaximalConsistent.closed_under_derivation`)
  - Prove `prop_implication_property`: MP reflected in membership (delegate to `Metalogic.SetMaximalConsistent.implication_property`)
  - Prove `prop_negation_complete`: either phi or neg phi is in every MCS (delegate to `Metalogic.SetMaximalConsistent.negation_complete`)
  - Prove `prop_mcs_bot_not_mem`: bottom not in any MCS
  - Prove `prop_mcs_neg_of_not_mem` and `prop_mcs_not_mem_of_neg`: negation-membership duality
  - Prove `prop_mcs_mem_iff_neg_not_mem`: biconditional form

**Timing**: 1.5 hours

**Depends on**: 3

**Files to modify**:
- `Cslib/Logics/Propositional/Metalogic/MCS.lean` - new file

**Verification**:
- `lake build Cslib.Logics.Propositional.Metalogic.MCS`
- All MCS properties proved without sorry
- Generic framework delegates work correctly

---

### Phase 5: Natural Deduction Wrappers [COMPLETED]

**Goal**: Create ND-flavored lemma names as thin wrappers around the Hilbert `DerivationTree` infrastructure, providing the familiar `impI`/`impE`/`botE` interface. Also derive cut, weakening, and substitution.

**Tasks**:
- [x] Create `Cslib/Logics/Propositional/NaturalDeduction/FromHilbert.lean`
  - Import `Cslib.Logics.Propositional.Metalogic.DeductionTheorem`
  - Define `impI` (implication introduction): wrapper around `deduction_theorem`
    - Type: `DerivationTree (A :: Gamma) B -> DerivationTree Gamma (A.imp B)`
  - Define `impE` (implication elimination / modus ponens): wrapper around `DerivationTree.modus_ponens`
    - Type: `DerivationTree Gamma (A.imp B) -> DerivationTree Gamma A -> DerivationTree Gamma B`
  - Define `botE` (ex falso quodlibet): combine EFQ axiom with modus ponens
    - Type: `DerivationTree Gamma Proposition.bot -> DerivationTree Gamma A`
  - Define `assume` (assumption): wrapper around `DerivationTree.assumption`
    - Type: `phi in Gamma -> DerivationTree Gamma phi`
  - Define `axiom_rule` (theory axiom): wrapper around `DerivationTree.ax`
    - Type: `PropositionalAxiom phi -> DerivationTree Gamma phi`
  - Derive `hilbert_cut`: cut rule within the Hilbert framework
    - From `DerivationTree Gamma A` and `DerivationTree (A :: Delta) B`, produce `DerivationTree (Gamma ++ Delta) B`
    - Use deduction theorem + MP + weakening
  - Derive `hilbert_weakening`: explicit weakening via the `DerivationTree.weakening` constructor
  - Derive `hilbert_substitution`: transport derivations along atom substitutions
  - Provide `Prop`-level (`Deriv`) versions of all the above

**Timing**: 2 hours

**Depends on**: 4

**Files to modify**:
- `Cslib/Logics/Propositional/NaturalDeduction/FromHilbert.lean` - new file

**Verification**:
- `lake build Cslib.Logics.Propositional.NaturalDeduction.FromHilbert`
- All wrappers defined without sorry
- `impI` and `impE` compose correctly (e.g., `impI Gamma (impE (assume h1) (assume h2))` type-checks)

---

### Phase 6: Module Registration and Full Build [COMPLETED]

**Goal**: Register all new modules in the Lean project structure and verify the full project builds cleanly.

**Tasks**:
- [x] Check if a `Cslib/Logics/Propositional.lean` root file exists; if not, create it importing all Propositional modules *(deviation: skipped -- no root file exists; imports added directly to Cslib.lean matching the existing pattern)*
- [x] Ensure `Cslib.lean` or the lakefile imports include the new Propositional submodules
- [x] Run `lake build` (full project) and verify zero errors *(deviation: altered -- full `lake build` has a pre-existing error in Bimodal.FrameConditions.Compatibility unrelated to this task; all 6 new modules verified individually)*
- [x] Run `lake build Cslib.Logics.Propositional.ProofSystem.Axioms Cslib.Logics.Propositional.ProofSystem.Derivation Cslib.Logics.Propositional.ProofSystem.Instances Cslib.Logics.Propositional.Metalogic.DeductionTheorem Cslib.Logics.Propositional.Metalogic.MCS Cslib.Logics.Propositional.NaturalDeduction.FromHilbert` to verify all new modules individually
- [x] Verify no import cycles exist (Propositional modules only import from Foundations and Propositional/Defs)

**Timing**: 1 hour

**Depends on**: 5

**Files to modify**:
- `Cslib/Logics/Propositional.lean` - possibly new or modified root module file
- `Cslib.lean` - add Propositional submodule imports if needed

**Verification**:
- `lake build` completes with zero errors
- No `sorry` in any new file (`grep -rn "sorry" Cslib/Logics/Propositional/ProofSystem/ Cslib/Logics/Propositional/Metalogic/ Cslib/Logics/Propositional/NaturalDeduction/FromHilbert.lean`)

---

## Testing & Validation

- [ ] Each phase builds independently via `lake build Module.Name`
- [ ] Full project `lake build` passes after Phase 6
- [ ] `grep -rn "sorry"` across all new files returns empty
- [ ] `PropositionalHilbert Propositional.HilbertCl` instance synthesizes
- [ ] Generic combinators from `Foundations/Logic/Theorems/` apply to `Propositional.HilbertCl`
- [ ] `prop_has_deduction_theorem` is accepted by the type checker
- [ ] MCS properties delegate to generic framework without re-proving
- [ ] ND wrappers compose correctly (impI/impE round-trip)
- [ ] No import cycles in the new module structure

## Artifacts & Outputs

- `Cslib/Logics/Propositional/ProofSystem/Axioms.lean` - PropositionalAxiom inductive
- `Cslib/Logics/Propositional/ProofSystem/Derivation.lean` - DerivationTree, height, Deriv, DerivationSystem
- `Cslib/Logics/Propositional/ProofSystem/Instances.lean` - InferenceSystem + PropositionalHilbert instances
- `Cslib/Logics/Propositional/Metalogic/DeductionTheorem.lean` - Deduction theorem
- `Cslib/Logics/Propositional/Metalogic/MCS.lean` - MCS properties
- `Cslib/Logics/Propositional/NaturalDeduction/FromHilbert.lean` - ND-flavored wrappers

## Rollback/Contingency

All new files are purely additive -- they create new modules without modifying existing ones. Rollback is simply deleting the new files:
```
rm -rf Cslib/Logics/Propositional/ProofSystem/
rm -rf Cslib/Logics/Propositional/Metalogic/
rm -f Cslib/Logics/Propositional/NaturalDeduction/FromHilbert.lean
```
The existing `Defs.lean` and `NaturalDeduction/Basic.lean` are untouched.
