# Implementation Plan: Derived Intro/Elim Rules for Propositional Connectives

- **Task**: 89 - Add derived intro/elim rules for defined propositional connectives in both ND and Hilbert
- **Status**: [NOT STARTED]
- **Effort**: 6 hours
- **Dependencies**: None
- **Research Inputs**: specs/089_derived_connective_rules/reports/01_derived-connective-rules.md
- **Artifacts**: plans/01_derived-connective-rules.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: true

## Overview

Implement derived introduction and elimination rules for the Lukasiewicz-encoded propositional connectives (and, or, neg, top, iff) in both the standalone Natural Deduction system (`Theory.Derivation` with `Finset` contexts) and the Hilbert system (`DerivationTree` with `List` contexts). The connectives are already defined as `abbrev` reductions to `imp`/`bot` in `Defs.lean`. Each rule will be provided at both the type level (computable proof terms) and the Prop level (`DerivableIn`/`Deriv` wrappers). The ND system requires `[IsClassical T]` for elimination rules that need double negation elimination, while the Hilbert system has Peirce's law as a primitive axiom.

### Research Integration

Research report identified all 13 rules needed, their computability status per system, and proof sketches for each. Key findings:
- Hilbert rules using `impI` (deduction theorem) are `noncomputable`; pure axiom+MP rules are computable
- ND rules are all computable (primitive `impI` constructor), but `andE1`, `andE2`, `orE`, `dne`, `iffE1`, `iffE2` require `[IsClassical T]`
- `Proposition.iff` is missing from `Defs.lean` and must be added as prerequisite
- Existing Foundations-layer theorems (`lce_imp`, `rce_imp`, `pairing`, `double_negation`, `classical_merge`, `iff_intro`) provide the key proof patterns

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md found.

## Goals & Non-Goals

**Goals**:
- Add `Proposition.iff` definition and notation to `Defs.lean`
- Create `NaturalDeduction/DerivedRules.lean` with all 13 derived rules for the ND system
- Create `NaturalDeduction/HilbertDerivedRules.lean` with all 13 derived rules for the Hilbert system
- Provide Prop-level wrappers (`DerivableIn`/`Deriv`) for every rule
- Maintain the existing pattern from `FromHilbert.lean` (naming, doc comments, `noncomputable` annotations)
- Ensure `lake build` succeeds for all new files

**Non-Goals**:
- Modifying the Foundations layer (existing generic theorems are sufficient)
- Adding notation beyond `iff` (and/or/neg/top notation already exists)
- Proving completeness or soundness of the derived rules
- Adding Sequent calculus rules
- Adding `IsClassical` or `IsIntuitionistic` instances for the Hilbert system's axiom theory

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `andE1`/`andE2` Hilbert proofs are complex (Peirce + EFQ composition) | M | M | Proof sketches from research are detailed; can reuse `lce_imp`/`rce_imp` patterns from Foundations layer directly since they use the same axiom names |
| `orE` proof is the most complex derived rule | M | M | Research provides a clean proof via `classical_merge` pattern; break into helper lemmas if needed |
| `noncomputable` cascading in Hilbert system | L | H | Expected behavior -- annotate explicitly, verify no unexpected noncomputable leaks |
| Finset vs List context differences cause proof engineering friction | M | L | ND system uses `insert`/`Finset.mem_insert` which are well-supported; follow existing `Basic.lean` patterns |
| `iff` notation conflicts with existing modal `iff` | M | L | Check scope; propositional `iff` uses `scoped` notation within `Cslib.Logic.PL` namespace |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3 | 1 |
| 3 | 4 | 2, 3 |

Phases within the same wave can execute in parallel.

### Phase 1: Add `Proposition.iff` to Defs.lean [COMPLETED]

**Goal**: Define the biconditional connective and its notation as a prerequisite for iff rules in later phases.

**Tasks**:
- [x] Add `Proposition.iff` abbrev to `Defs.lean` after the `Proposition.and` definition: `abbrev Proposition.iff (A B : Proposition Atom) : Proposition Atom := (A.imp B).and (B.imp A)`
- [x] Add scoped notation: `@[inherit_doc] scoped infix:30 " ↔ " => Proposition.iff` *(deviation: skipped -- `↔` notation at infix:30 conflicts with Lean's builtin `Iff` notation, causing parse errors in Basic.lean where `↔` is used for `Prop`-level biconditional. The `abbrev` alone suffices; users can write `A.iff B`.)*
- [x] Verify no notation conflicts with `lake build Cslib.Logics.Propositional.Defs`

**Timing**: 0.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Defs.lean` - Add `iff` abbreviation and notation

**Verification**:
- `lake build Cslib.Logics.Propositional.Defs` succeeds
- No downstream build errors in existing files that import `Defs.lean`

---

### Phase 2: ND System Derived Rules [COMPLETED]

**Goal**: Create `NaturalDeduction/DerivedRules.lean` with all 13 derived rules for `Theory.Derivation`, providing both type-level and Prop-level (`DerivableIn`) versions.

**Tasks**:
- [x] Create file `Cslib/Logics/Propositional/NaturalDeduction/DerivedRules.lean` with module header and imports from `Basic.lean`
- [x] Implement negation rules (simplest, direct wrappers):
  - `negI : T.Derivation (insert A Gamma) bot -> T.Derivation Gamma (neg A)` -- literally `impI Gamma`
  - `negE : T.Derivation Gamma (neg A) -> T.Derivation Gamma A -> T.Derivation Gamma bot` -- literally `impE`
- [x] Implement `topI : T.Derivation Gamma top` -- `impI Gamma (ass mem_insert_self)`
- [x] Implement conjunction intro (no classical constraint):
  - `andI : T.Derivation Gamma A -> T.Derivation Gamma B -> T.Derivation Gamma (A.and B)` -- uses `impI`, `ass`, `impE`, `weakCtx`
- [x] Implement conjunction elim (requires `[IsClassical T]`):
  - `andE1 : [IsClassical T] -> T.Derivation Gamma (A.and B) -> T.Derivation Gamma A` -- uses `negI` to build `neg neg A`, then `dne` via `T.dne`
  - `andE2 : [IsClassical T] -> T.Derivation Gamma (A.and B) -> T.Derivation Gamma B` -- similar pattern for extracting B
- [x] Implement disjunction intro (no classical constraint):
  - `orI1 : T.Derivation Gamma A -> T.Derivation Gamma (A.or B)` -- uses `impI`, `ass`, `impE`, `botE`, `weakCtx`
  - `orI2 : T.Derivation Gamma B -> T.Derivation Gamma (A.or B)` -- uses `impI`, `weakCtx`
- [x] Implement disjunction elim (requires `[IsClassical T]`):
  - `orE : [IsClassical T] -> T.Derivation Gamma (A.or B) -> T.Derivation (insert A Gamma) C -> T.Derivation (insert B Gamma) C -> T.Derivation Gamma C` -- uses `impI`, composition, Peirce via `dne`
- [x] Implement `dne : [IsClassical T] -> T.Derivation Gamma (neg (neg A)) -> T.Derivation Gamma A` -- uses `T.dne` axiom + `impE`
- [x] Implement iff rules:
  - `iffI : T.Derivation Gamma (A.imp B) -> T.Derivation Gamma (B.imp A) -> T.Derivation Gamma (A.iff B)` -- via `andI`
  - `iffE1 : [IsClassical T] -> T.Derivation Gamma (A.iff B) -> T.Derivation Gamma (A.imp B)` -- via `andE1`
  - `iffE2 : [IsClassical T] -> T.Derivation Gamma (A.iff B) -> T.Derivation Gamma (B.imp A)` -- via `andE2`
- [x] Add `DerivableIn`-level wrappers for all 13 rules (following `DerivableIn.cut` pattern in `Basic.lean`)
- [x] Verify with `lake build Cslib.Logics.Propositional.NaturalDeduction.DerivedRules`

**Timing**: 2.5 hours

**Depends on**: 1

**Files to create**:
- `Cslib/Logics/Propositional/NaturalDeduction/DerivedRules.lean` - All ND derived rules

**Verification**:
- `lake build Cslib.Logics.Propositional.NaturalDeduction.DerivedRules` succeeds with no `sorry`
- `lean_verify` on key definitions confirms no axiom leaks beyond `propDecidable` for classical rules
- All rules have correct computability (all computable in ND system)

---

### Phase 3: Hilbert System Derived Rules [COMPLETED]

**Goal**: Create `NaturalDeduction/HilbertDerivedRules.lean` with all 13 derived rules for `DerivationTree`/`Deriv`, following the `FromHilbert.lean` pattern.

**Tasks**:
- [x] Create file `Cslib/Logics/Propositional/NaturalDeduction/HilbertDerivedRules.lean` with module header, importing `FromHilbert.lean`
- [x] Implement negation rules (direct wrappers, matching `FromHilbert.lean` style):
  - `noncomputable def negI : DerivationTree (A :: Gamma) bot -> DerivationTree Gamma (neg A)` -- literally `impI`
  - `def negE : DerivationTree Gamma (neg A) -> DerivationTree Gamma A -> DerivationTree Gamma bot` -- literally `impE`
- [x] Implement `def topI : DerivationTree Gamma top` -- EFQ at `bot` gives `bot -> bot`, weaken to `Gamma`
- [x] Implement conjunction intro:
  - `noncomputable def andI : DerivationTree Gamma A -> DerivationTree Gamma B -> DerivationTree Gamma (A.and B)` -- uses `impI`, `assume`, `impE`, `hilbertWeakening`
- [x] Implement conjunction elim (computable, uses Peirce axiom directly):
  - `def andE1 : DerivationTree Gamma (A.and B) -> DerivationTree Gamma A` -- Peirce(A, B->bot) + efq_neg composition + MP
  - `def andE2 : DerivationTree Gamma (A.and B) -> DerivationTree Gamma B` -- Peirce(B, bot) + ImplyK composition + MP
- [x] Implement disjunction intro:
  - `noncomputable def orI1 : DerivationTree Gamma A -> DerivationTree Gamma (A.or B)` -- uses `impI`, `assume`, `impE`, `botE`
  - `def orI2 : DerivationTree Gamma B -> DerivationTree Gamma (A.or B)` -- ImplyK + MP (computable)
- [x] Implement disjunction elim:
  - `noncomputable def orE : DerivationTree Gamma (A.or B) -> DerivationTree (A :: Gamma) C -> DerivationTree (B :: Gamma) C -> DerivationTree Gamma C` -- uses `impI` twice, composition, `classical_merge` pattern (Peirce)
- [x] Implement `def dne : DerivationTree Gamma (neg (neg A)) -> DerivationTree Gamma A` -- Peirce(A,bot) + EFQ + B-combinator + MP (computable)
- [x] Implement iff rules:
  - `noncomputable def iffI` -- via `andI`
  - `def iffE1` -- via `andE1` (computable)
  - `def iffE2` -- via `andE2` (computable)
- [x] Add `Deriv`-level wrappers for all 13 rules (following `impIDeriv`/`impEDeriv` pattern)
- [x] Verify with `lake build Cslib.Logics.Propositional.NaturalDeduction.HilbertDerivedRules`

**Timing**: 2.5 hours

**Depends on**: 1

**Files to create**:
- `Cslib/Logics/Propositional/NaturalDeduction/HilbertDerivedRules.lean` - All Hilbert derived rules

**Verification**:
- `lake build Cslib.Logics.Propositional.NaturalDeduction.HilbertDerivedRules` succeeds with no `sorry`
- `noncomputable` annotations match the computability table from research:
  - Noncomputable: `negI`, `andI`, `orI1`, `orE`, `iffI`
  - Computable: `negE`, `topI`, `andE1`, `andE2`, `orI2`, `dne`, `iffE1`, `iffE2`
- `lean_verify` on key definitions confirms no unexpected axiom usage

---

### Phase 4: Integration and Full Build Verification [COMPLETED]

**Goal**: Ensure all new files integrate cleanly with the existing codebase and pass a full `lake build`.

**Tasks**:
- [x] Run `lake build` to verify no downstream breakage from `iff` notation or new imports
- [x] Verify that `Equivalence.lean` still builds (imports both `Basic.lean` and `FromHilbert.lean`)
- [x] Verify naming consistency: all rules follow `{connective}{I|E|E1|E2}` naming convention
- [x] Verify doc comments on all public definitions
- [x] Run `lean_verify` on a sample of definitions to confirm no `sorry` or vacuous definitions
- [x] If any issues found, fix and re-verify

**Timing**: 0.5 hours

**Depends on**: 2, 3

**Files to verify**:
- All files in `Cslib/Logics/Propositional/` directory tree

**Verification**:
- `lake build` succeeds with zero errors
- No `sorry` in any new file
- No vacuous definitions (`def X := True` pattern)

## Testing & Validation

- [ ] `lake build Cslib.Logics.Propositional.Defs` -- Phase 1 verification
- [ ] `lake build Cslib.Logics.Propositional.NaturalDeduction.DerivedRules` -- Phase 2 verification
- [ ] `lake build Cslib.Logics.Propositional.NaturalDeduction.HilbertDerivedRules` -- Phase 3 verification
- [ ] `lake build` -- Full project build (Phase 4)
- [ ] `lean_verify` spot checks on `andI`, `andE1`, `orE`, `dne` in both systems
- [ ] Confirm `noncomputable` annotations are correct for Hilbert rules (no missing annotations, no unnecessary ones)

## Artifacts & Outputs

- `specs/089_derived_connective_rules/plans/01_derived-connective-rules.md` (this file)
- `Cslib/Logics/Propositional/Defs.lean` -- modified (add `iff`)
- `Cslib/Logics/Propositional/NaturalDeduction/DerivedRules.lean` -- new file (ND rules)
- `Cslib/Logics/Propositional/NaturalDeduction/HilbertDerivedRules.lean` -- new file (Hilbert rules)

## Rollback/Contingency

- Phase 1 (`iff` definition) is a single `abbrev` + notation line -- trivially revertible with `git checkout`
- Phases 2 and 3 create new files only -- deletion reverts to previous state
- If `iff` notation conflicts arise, the notation can be scoped more narrowly or renamed to `Proposition.biconditional`
- If any individual rule proof is blocked (e.g., `orE` complexity), mark that rule with `sorry` and `[BLOCKED]` annotation, and continue with remaining rules
