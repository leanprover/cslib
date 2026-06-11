# Implementation Plan: Task #120

- **Task**: 120 - Parameterize Natural Deduction Equivalence
- **Status**: [NOT STARTED]
- **Effort**: 4 hours
- **Dependencies**: None
- **Research Inputs**: specs/120_parameterize_natural_deduction_equivalence/reports/01_nd-parameterization.md
- **Artifacts**: plans/01_nd-parameterization.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: true

## Overview

Refactor the three NaturalDeduction files (FromHilbert.lean, HilbertDerivedRules.lean, Equivalence.lean) to replace all hardcoded `PropositionalAxiom` references with generic `Axioms` parameters, following the explicit-parameter pattern established by `deductionTheorem` in DeductionTheorem.lean. Split HilbertDerivedRules.lean into an intuitionistic layer (K, S, EFQ) and a classical layer (K, S, EFQ, Peirce). Parameterize Equivalence.lean to prove a generic Hilbert-ND equivalence valid for any axiom set containing K, S, and EFQ, with intuitionistic and classical instantiated as corollaries. Clean up stale docstring in Derivation.lean.

### Research Integration

The research report (01_nd-parameterization.md) confirmed:
- All three files are leaf modules with zero external consumers, eliminating downstream breakage risk.
- The `deductionTheorem` pattern (explicit `h_implyK`/`h_implyS` parameters, local `letI` instance) is the established codebase convention.
- Rule-by-rule analysis maps each HilbertDerivedRules definition to its minimal axiom requirements: intuitionistic rules need K, S, EFQ; classical rules additionally need Peirce.
- The ND system's structural `botE` constructor makes EFQ a mandatory axiom for the `ndToHilbert` direction, confirming intuitionistic logic as the natural floor.
- Backward-compat aliases (`ClDerivationTree` etc.) were already removed; only a stale docstring reference remains.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This task advances the Propositional module's NaturalDeduction component by generalizing it from classical-only to subsystem-parameterized, matching the parameterization already done for DeductionTheorem.lean. This brings NaturalDeduction in line with the project's design principle of placing content at the most general level it can compile at.

## Goals & Non-Goals

**Goals**:
- Parameterize FromHilbert.lean over generic `Axioms` with explicit axiom parameters
- Split HilbertDerivedRules.lean into intuitionistic (K, S, EFQ) and classical (K, S, EFQ, Peirce) sections
- Parameterize Equivalence.lean with generic `AxiomTheory`, providing intuitionistic and classical corollaries
- Remove stale backward-compat alias docstring from Derivation.lean
- Achieve `lake build` with zero errors and zero sorries

**Non-Goals**:
- Minimal logic ND equivalence (ND has structural `botE`, so EFQ is inherent)
- Adding new type classes (using explicit parameters per established pattern)
- Modifying Basic.lean or DerivedRules.lean (already generic)
- Adding new axiom predicates or subsumption proofs

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Parameter threading verbosity causes proof breakage | M | M | Follow existing `deductionTheorem` pattern exactly; test each definition with `lean_goal` before moving on |
| `noncomputable` propagation issues | L | L | Already present in current code; parameterization does not change computability status |
| Universe polymorphism mismatch with `Axioms` parameter | M | L | Match existing `variable {Atom : Type*}` pattern; use `{Axioms : PL.Proposition Atom -> Prop}` |
| `subst_preserves_axiom` generalization breaks `hilbertSubstitution` | M | M | Keep original for `PropositionalAxiom` as-is; add `IntPropAxiom` and `MinPropAxiom` variants alongside |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3 | 1 |
| 3 | 4 | 2, 3 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Parameterize FromHilbert.lean [COMPLETED]

**Goal**: Replace all `PropositionalAxiom` references with generic `Axioms` and explicit axiom parameters, following the `deductionTheorem` pattern.

**Tasks**:
- [ ] Update the module docstring to reflect parameterization (remove "Fixed at `PropositionalAxiom` (classical)" language)
- [ ] Parameterize `impI`: Add `{Axioms : PL.Proposition Atom -> Prop}` and explicit parameters `(h_K : forall (phi psi : PL.Proposition Atom), Axioms (phi.imp (psi.imp phi)))` and `(h_S : forall (phi psi chi : PL.Proposition Atom), Axioms ((phi.imp (psi.imp chi)).imp ((phi.imp psi).imp (phi.imp chi))))`. Change `PropositionalAxiom` to `Axioms` in the type signature. Replace `.implyK phi psi` with `h_K phi psi` and `.implyS phi psi chi` with `h_S phi psi chi` in the call to `deductionTheorem`
- [ ] Parameterize `impE`: Add `{Axioms : PL.Proposition Atom -> Prop}` (no axiom parameters needed, only uses MP). Replace `PropositionalAxiom` with `Axioms` in the type signature
- [ ] Parameterize `botE`: Add `{Axioms : PL.Proposition Atom -> Prop}` and `(h_EFQ : forall (phi : PL.Proposition Atom), Axioms (Proposition.bot.imp phi))`. Replace `.efq A` with `h_EFQ A`. Replace `PropositionalAxiom` with `Axioms` in the type signature
- [ ] Parameterize `assume`: Add `{Axioms : PL.Proposition Atom -> Prop}`. No axiom parameters needed. Replace `PropositionalAxiom` with `Axioms`
- [ ] Parameterize `axiomRule`: Add `{Axioms : PL.Proposition Atom -> Prop}`. Change the hypothesis type from `PropositionalAxiom phi` to `Axioms phi`. Replace `PropositionalAxiom` with `Axioms` in the return type
- [ ] Parameterize `hilbertCut`: Add `{Axioms : PL.Proposition Atom -> Prop}`, `h_K`, and `h_S` parameters (same signatures as `impI`). Replace `.implyK phi psi` with `h_K phi psi` and `.implyS phi psi chi` with `h_S phi psi chi` in the `deductionTheorem` call. Replace `PropositionalAxiom` with `Axioms`
- [ ] Parameterize `hilbertWeakening`: Add `{Axioms : PL.Proposition Atom -> Prop}`. No axiom parameters needed. Replace `PropositionalAxiom` with `Axioms`
- [ ] Add `subst_preserves_intAxiom`: New theorem, same pattern as `subst_preserves_axiom` but for `IntPropAxiom` -- cases on `implyK`, `implyS`, `efq` (3 cases instead of 4)
- [ ] Add `subst_preserves_minAxiom`: New theorem, same pattern but for `MinPropAxiom` -- cases on `implyK`, `implyS` (2 cases)
- [ ] Keep `subst_preserves_axiom` unchanged (still handles `PropositionalAxiom` with all 4 cases)
- [ ] Parameterize `hilbertSubstitution`: Add `{Axioms : PL.Proposition Atom -> Prop}` and `(h_subst : forall {phi : PL.Proposition Atom}, Axioms phi -> forall (f : Atom -> PL.Proposition Atom'), Axioms (phi.subst f))`. Replace the call to `subst_preserves_axiom` with `h_subst`. Replace `PropositionalAxiom` with `Axioms`
- [ ] Parameterize all Deriv-level wrappers (`impIDeriv`, `impEDeriv`, `botEDeriv`, `hilbertCutDeriv`, `hilbertWeakeningDeriv`, `hilbertSubstitutionDeriv`): Add matching `Axioms` and axiom parameters, thread them to the underlying definitions
- [ ] Verify with `lake build Cslib.Logics.Propositional.NaturalDeduction.FromHilbert`

**Timing**: 1.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/NaturalDeduction/FromHilbert.lean` - Parameterize all definitions and theorems

**Verification**:
- `lake build Cslib.Logics.Propositional.NaturalDeduction.FromHilbert` succeeds
- No `sorry` in the file
- No remaining references to `PropositionalAxiom` constructors (`.implyK`, `.implyS`, `.efq`, `.peirce`) in the parameterized definitions (only in `subst_preserves_axiom` which stays classical)

---

### Phase 2: Split and Parameterize HilbertDerivedRules.lean [COMPLETED]

**Goal**: Organize rules into intuitionistic and classical sections with appropriate axiom parameters.

**Tasks**:
- [ ] Update the module docstring to reflect the intuitionistic/classical split
- [ ] Create `section Intuitionistic` with variables: `{Axioms : PL.Proposition Atom -> Prop}`, `(h_K : forall (phi psi : PL.Proposition Atom), Axioms (phi.imp (psi.imp phi)))`, `(h_S : forall (phi psi chi : PL.Proposition Atom), Axioms ((phi.imp (psi.imp chi)).imp ((phi.imp psi).imp (phi.imp chi))))`, `(h_EFQ : forall (phi : PL.Proposition Atom), Axioms (Proposition.bot.imp phi))`
- [ ] Move and parameterize `hilbertNegI` into the Intuitionistic section: replace `impI d` with `impI h_K h_S d`. Replace `PropositionalAxiom` with `Axioms`
- [ ] Move and parameterize `hilbertNegE` into the Intuitionistic section: replace `impE d1 d2` -- this just wraps `impE` which needs no axiom parameters. Replace `PropositionalAxiom` with `Axioms`
- [ ] Move and parameterize `hilbertTopI` into the Intuitionistic section: replace `.efq Proposition.bot` with `h_EFQ Proposition.bot`. Replace `PropositionalAxiom` with `Axioms`
- [ ] Move and parameterize `hilbertAndI` into the Intuitionistic section: the body calls `impI` (needs h_K, h_S), `impE` (no params), `assume`, `hilbertWeakening` (no params). Thread `h_K` and `h_S` to `impI`. Replace `PropositionalAxiom` with `Axioms`
- [ ] Move and parameterize `hilbertOrI1` into the Intuitionistic section: calls `impI` (needs h_K, h_S), `botE` (needs h_EFQ), `impE`, `assume`, `hilbertWeakening`. Thread all three axiom parameters. Replace `PropositionalAxiom` with `Axioms`
- [ ] Move and parameterize `hilbertOrI2` into the Intuitionistic section: replace `.implyK B (A.imp Proposition.bot)` with `h_K B (A.imp Proposition.bot)`. Note: only needs K, but grouped with other introduction rules. Replace `PropositionalAxiom` with `Axioms`
- [ ] Move and parameterize `hilbertIffI` into the Intuitionistic section: calls `hilbertAndI` which needs h_K, h_S. Thread parameters. Replace `PropositionalAxiom` with `Axioms`
- [ ] Add Deriv-level wrappers for all intuitionistic rules in the Intuitionistic section, each threading the axiom parameters
- [ ] Close `section Intuitionistic`
- [ ] Create `section Classical` with variables: same as Intuitionistic plus `(h_Peirce : forall (phi psi : PL.Proposition Atom), Axioms (((phi.imp psi).imp phi).imp phi))`
- [ ] Move and parameterize `hilbertDne` into the Classical section: replace `PropositionalAxiom.peirce A Proposition.bot` with `h_Peirce A Proposition.bot`, `.efq A` with `h_EFQ A`, `.implyK ...` with `h_K ...`, `.implyS ...` with `h_S ...`. Replace `PropositionalAxiom` with `Axioms`
- [ ] Move and parameterize `hilbertAndE1` into the Classical section: replace all `PropositionalAxiom.peirce`, `.efq`, `.implyK`, `.implyS` with the corresponding parameters. Replace `PropositionalAxiom` with `Axioms`
- [ ] Move and parameterize `hilbertAndE2` into the Classical section: replace all axiom constructor references. Note this calls `hilbertDne` which now takes the classical parameters. Replace `PropositionalAxiom` with `Axioms`
- [ ] Move and parameterize `hilbertOrE` into the Classical section: calls `impI` (h_K, h_S), `impE`, `botE` (h_EFQ), `hilbertDne` (needs all 4 params), `hilbertNegI` (h_K, h_S), `hilbertNegE`, `assume`, `hilbertWeakening`. Thread all parameters. Replace `PropositionalAxiom` with `Axioms`
- [ ] Move and parameterize `hilbertIffE1` into the Classical section: calls `hilbertAndE1`. Thread parameters. Replace `PropositionalAxiom` with `Axioms`
- [ ] Move and parameterize `hilbertIffE2` into the Classical section: calls `hilbertAndE2`. Thread parameters. Replace `PropositionalAxiom` with `Axioms`
- [ ] Add Deriv-level wrappers for all classical rules in the Classical section
- [ ] Close `section Classical`
- [ ] Verify with `lake build Cslib.Logics.Propositional.NaturalDeduction.HilbertDerivedRules`

**Timing**: 1.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/NaturalDeduction/HilbertDerivedRules.lean` - Split into sections, parameterize all definitions

**Verification**:
- `lake build Cslib.Logics.Propositional.NaturalDeduction.HilbertDerivedRules` succeeds
- No `sorry` in the file
- Intuitionistic rules have only `h_K`, `h_S`, `h_EFQ` parameters
- Classical rules have `h_K`, `h_S`, `h_EFQ`, `h_Peirce` parameters
- No remaining direct references to `PropositionalAxiom` constructors in parameterized definitions

---

### Phase 3: Parameterize Equivalence.lean [COMPLETED]

**Goal**: Generalize the Hilbert-ND equivalence to work for any axiom set containing K, S, and EFQ, with instantiated corollaries for intuitionistic and classical logic.

**Tasks**:
- [ ] Update the module docstring to reflect parameterization
- [ ] Define generic `AxiomTheory`: `def AxiomTheory {Atom : Type*} (Axioms : PL.Proposition Atom -> Prop) : Theory Atom := { phi | Axioms phi }`
- [ ] Add simp lemma `mem_axiomTheory`: `@[simp] theorem mem_axiomTheory {Axioms : PL.Proposition Atom -> Prop} {phi : PL.Proposition Atom} : phi in AxiomTheory Axioms <-> Axioms phi := Iff.rfl`
- [ ] Add backward-compat abbreviation: `abbrev HilbertAxiomTheory : Theory Atom := AxiomTheory (@PropositionalAxiom Atom)` (keep for any existing internal references)
- [ ] Update `mem_hilbertAxiomTheory` to reuse `mem_axiomTheory`: `theorem mem_hilbertAxiomTheory {phi : PL.Proposition Atom} : phi in (HilbertAxiomTheory : Theory Atom) <-> PropositionalAxiom phi := mem_axiomTheory`
- [ ] Parameterize `hilbertToND`: Replace `PropositionalAxiom` with `{Axioms : PL.Proposition Atom -> Prop}`. Replace `HilbertAxiomTheory` with `AxiomTheory Axioms`. Replace `mem_hilbertAxiomTheory` with `mem_axiomTheory`. No axiom parameters needed (this direction is purely structural)
- [ ] Parameterize `hilbert_to_nd_deriv`: Same replacements as `hilbertToND`
- [ ] Parameterize `ndToHilbert`: Add `{Axioms : PL.Proposition Atom -> Prop}`, `h_K`, `h_S`, and `h_EFQ` parameters (same types as in FromHilbert). Replace `HilbertAxiomTheory` with `AxiomTheory Axioms`. Replace `mem_hilbertAxiomTheory` with `mem_axiomTheory`. In the `.botE` case, replace `botE (ndToHilbert d)` with `botE h_EFQ (ndToHilbert h_K h_S h_EFQ d)` (since `botE` now needs `h_EFQ`). In the `.impI` case, replace the `deductionTheorem` call's `.implyK`/`.implyS` with `h_K`/`h_S`, and thread `h_K h_S h_EFQ` to recursive `ndToHilbert` calls
- [ ] Parameterize `nd_to_hilbert_deriv`: Add matching axiom parameters, thread to `ndToHilbert`
- [ ] Parameterize `hilbert_iff_nd`: Add `{Axioms : PL.Proposition Atom -> Prop}`, `h_K`, `h_S`, `h_EFQ` parameters. Replace `PropositionalAxiom` with `Axioms`, `HilbertAxiomTheory` with `AxiomTheory Axioms`. Thread axiom parameters to `hilbert_to_nd_deriv` and `nd_to_hilbert_deriv`
- [ ] Add intuitionistic corollary: `theorem hilbert_iff_nd_int {phi : PL.Proposition Atom} : Derivable IntPropAxiom phi <-> DerivableIn (AxiomTheory IntPropAxiom) ((empty : Ctx Atom) turnstile phi) := hilbert_iff_nd (fun phi psi => .implyK phi psi) (fun phi psi chi => .implyS phi psi chi) (fun phi => .efq phi)`
- [ ] Add classical corollary: `theorem hilbert_iff_nd_cl {phi : PL.Proposition Atom} : Derivable PropositionalAxiom phi <-> DerivableIn (AxiomTheory PropositionalAxiom) ((empty : Ctx Atom) turnstile phi) := hilbert_iff_nd (fun phi psi => .implyK phi psi) (fun phi psi chi => .implyS phi psi chi) (fun phi => .efq phi)`
- [ ] Verify with `lake build Cslib.Logics.Propositional.NaturalDeduction.Equivalence`

**Timing**: 0.75 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/NaturalDeduction/Equivalence.lean` - Parameterize theory, translations, and equivalence theorem

**Verification**:
- `lake build Cslib.Logics.Propositional.NaturalDeduction.Equivalence` succeeds
- No `sorry` in the file
- `hilbert_iff_nd_int` and `hilbert_iff_nd_cl` both type-check
- Generic `hilbert_iff_nd` accepts any `Axioms` with K, S, EFQ

---

### Phase 4: Docstring Cleanup and Final Verification [NOT STARTED]

**Goal**: Fix stale docstring in Derivation.lean and verify the entire project builds cleanly.

**Tasks**:
- [ ] Edit `Cslib/Logics/Propositional/ProofSystem/Derivation.lean` lines 27-29: Replace the stale backward-compat alias text. Change from: `Type aliases \`ClDerivationTree\`, \`ClDeriv\`, \`ClDerivable\`, and \`clPropDerivationSystem\` instantiate the parameterized types at \`PropositionalAxiom\` for backward compatibility.` to: `The \`Deriv\`, \`Derivable\`, and \`propDerivationSystem\` definitions are parameterized over an arbitrary axiom predicate \`Axioms\`.`
- [ ] Run `lake build` (full project) to verify zero errors
- [ ] Run `lean_verify` on key theorems: `Cslib.Logic.PL.hilbert_iff_nd`, `Cslib.Logic.PL.hilbert_iff_nd_int`, `Cslib.Logic.PL.hilbert_iff_nd_cl`
- [ ] Verify no `sorry` in any modified file: `grep -r "sorry" Cslib/Logics/Propositional/NaturalDeduction/`

**Timing**: 0.25 hours

**Depends on**: 2, 3

**Files to modify**:
- `Cslib/Logics/Propositional/ProofSystem/Derivation.lean` - Fix stale docstring (lines 27-29)

**Verification**:
- `lake build` succeeds with zero errors
- `grep -r "sorry" Cslib/Logics/Propositional/NaturalDeduction/` returns empty
- Key theorems pass `lean_verify` with no axiom violations

## Testing & Validation

- [ ] `lake build Cslib.Logics.Propositional.NaturalDeduction.FromHilbert` succeeds after Phase 1
- [ ] `lake build Cslib.Logics.Propositional.NaturalDeduction.HilbertDerivedRules` succeeds after Phase 2
- [ ] `lake build Cslib.Logics.Propositional.NaturalDeduction.Equivalence` succeeds after Phase 3
- [ ] `lake build` (full project) succeeds after Phase 4
- [ ] No `sorry` in any modified file
- [ ] `hilbert_iff_nd` works generically for any `Axioms` with K, S, EFQ
- [ ] `hilbert_iff_nd_int` instantiates at `IntPropAxiom`
- [ ] `hilbert_iff_nd_cl` instantiates at `PropositionalAxiom`
- [ ] No direct `PropositionalAxiom` constructor references in parameterized definitions (only in `subst_preserves_axiom` and corollary instantiations)

## Artifacts & Outputs

- `specs/120_parameterize_natural_deduction_equivalence/plans/01_nd-parameterization.md` (this file)
- Modified: `Cslib/Logics/Propositional/NaturalDeduction/FromHilbert.lean`
- Modified: `Cslib/Logics/Propositional/NaturalDeduction/HilbertDerivedRules.lean`
- Modified: `Cslib/Logics/Propositional/NaturalDeduction/Equivalence.lean`
- Modified: `Cslib/Logics/Propositional/ProofSystem/Derivation.lean` (docstring only)

## Rollback/Contingency

All modified files are leaf modules with no external consumers. If the parameterization causes issues:
1. `git checkout -- Cslib/Logics/Propositional/NaturalDeduction/` to revert all NaturalDeduction changes
2. `git checkout -- Cslib/Logics/Propositional/ProofSystem/Derivation.lean` to revert docstring change
3. No downstream files are affected since these are leaf modules
