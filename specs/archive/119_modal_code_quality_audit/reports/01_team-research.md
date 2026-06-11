# Research Report: Task #119

**Task**: Modal Code Quality Audit
**Date**: 2026-06-11
**Mode**: Team Research (4 teammates, standard mode)
**Completed**: 2026-06-11

---

## Summary

The Modal metalogic is mathematically clean (zero `sorry`, zero `axiom` introductions, all 15 logics correctly formalized) but carries substantial structural debt: approximately 2,000–2,500 lines of copy-pasted proof boilerplate across the 30 soundness and completeness files, 51 active linter warnings (all fixable), and a significant architectural gap where the semantic layer (`Cube.lean`) and the syntactic layer (`Metalogic/`) are developed in parallel without any connecting bridge theorems. The library is production-quality in correctness but not yet refactor-ready or Mathlib-submission-ready.

---

## Priority Findings

### Critical

**None.** No mathematical errors, no broken proofs, no `sorry`, no spurious axioms.

---

### High Priority

#### H1. h_cons Duplication: 10 completeness files, 30-line block each (~300 lines total)

The proof that `{¬φ}` is consistent when `φ` is not derivable is copy-pasted verbatim across every completeness file that does not contain axiom T:

`KCompleteness.lean`, `BCompleteness.lean`, `K4Completeness.lean`, `K5Completeness.lean`, `K45Completeness.lean`, `TBCompleteness.lean`, `D4Completeness.lean`, `D5Completeness.lean`, `D45Completeness.lean`, `DBCompleteness.lean`

The block uses only classical propositional axioms (K, S, EFQ, Peirce) and modal K. Teammates A and D both independently identified this as the single highest-impact deduplication target. Teammate D estimates ~600 lines eliminated; Teammate A estimates ~300 lines from the 30-line version. The discrepancy is because Teammate D's count includes surrounding `h_cons` scaffolding in some files. The fix is unambiguous: extract `neg_consistent_of_not_derivable` as a shared lemma in `Completeness.lean` or a new `Completeness/Boilerplate.lean`.

**Confidence**: Certain (both A and D verified by direct code inspection).

#### H2. Propositional Case Block: 13 soundness files, 5-case block each (~65 lines total)

Every soundness file's `*_axiom_sound` theorem begins with the same 5 sub-proofs for `implyK`, `implyS`, `efq`, `peirce`, `modalK`. These are identical across all 13 affected files. Teammate A identified this; Teammate D corroborates it as part of the broader redundancy analysis.

The fix requires a `k_axiom_sound_shared` helper that proves validity for any axiom set containing the K-sub-predicates. Each per-logic file then delegates the shared cases and handles only its unique axiom (T, 4, 5, B, D).

**Confidence**: Certain (Teammate A verified by direct comparison across all soundness files).

#### H3. MCS.lean Namespace Collision (Genuine Bug)

`Modal.SetConsistent` and `Modal.SetMaximalConsistent` are declared inside `namespace Cslib.Logic.Modal`, producing the double-qualified name `Cslib.Logic.Modal.Modal.SetConsistent`. The two declarations are accessible under the wrong path. This is the only finding that qualifies as a genuine naming bug (not merely style debt).

**Fix**: Declare the `abbrev` inside `namespace Cslib.Logic` (not `namespace Cslib.Logic.Modal`), or drop the `Modal.` prefix from the `abbrev` name.

**Confidence**: Certain (Teammate A reproduced the linter warning).

#### H4. Cube.lean–Metalogic Disconnect (Design Gap)

`Cube.lean` defines all 15 logics semantically (as sets of valid formulas over frame classes). `Metalogic/` defines all 15 logics syntactically (Hilbert systems with completeness proofs). There are no bridge theorems of the form:

```lean
theorem k45_axiomatization : ∀ φ, Derivable (@K45Axiom Atom) φ ↔ φ ∈ K45 World Atom
```

Teammates C and D both identified this independently. Teammate C called it "a significant incompleteness in the library" (two halves not connected). Teammate D noted that a new contributor could easily miss that `K45 World Atom` in `Cube.lean` and `Derivable (@K45Axiom Atom) φ` in the metalogic are the same thing only via the completeness bridge.

This is not a bug in either half — both are internally correct — but the library cannot be used as a unified system without these connections.

**Confidence**: Certain.

---

### Medium Priority

#### M1. 51 Active Linter Warnings (All Fixable)

Grouped by type (all from `lake build Cslib.Logics.Modal.Metalogic`):

| Category | Count | Files |
|----------|-------|-------|
| Unused variable `ψ` | 10+ | All major soundness files |
| Flexible `simp` (should be `simp only`) | 12 | `DeductionTheorem`, `MCS`, `Completeness`, several `*Completeness` files |
| `show` tactic misuse (prefer `unfold`/`simp only`) | 10 | `Basic.lean` |
| `simp_wf` does nothing | 2 | `DeductionTheorem.lean` lines 116, 183 |
| `push_neg` deprecated (prefer `push Not`) | 1 | `Basic.lean:115` |
| `Modal.Modal.*` namespace collision | 2 | `MCS.lean` lines 47, 52 |

The unused `ψ` warnings are trivially fixed (replace `fun ψ h_ax w => ...` with `fun _ h_ax w => ...`). The flexible `simp` warnings require using `simp?` at each site to produce `simp only [...]` lists.

**Confidence**: Certain (Teammate A reproduced all 51 from build output).

#### M2. Stale/Misleading Module Headers

Two header mismatches confirmed by multiple teammates:

- `Completeness.lean` header says "S5 Modal Logic" but the file contains `canonical_symm` and `canonical_eucl_from_5` used by B, K5, K45, KB5, TB, DB. This is misleading for any of the 14 non-S5 logic files that import it.
- `Soundness.lean` describes itself as "S5 Axiom Soundness" but now serves as the parameterized soundness module for all logics.
- Teammate D adds: the three truth lemma families (`truth_lemma`, `k_truth_lemma`, `truth_lemma_d`) and their routing rules are undocumented anywhere centrally.

**Confidence**: Certain (A and D both confirmed; C corroborates).

#### M3. `Relation.Serial` vs Lambda Inconsistency in Frame Conditions

D-series soundness files use `Relation.Serial m.r` while all other frame conditions (reflexivity, symmetry, transitivity, Euclideanness) are expressed as explicit universal quantifiers. This stylistic inconsistency creates friction when reading across files. A consistent choice should be made: either adopt `Relation.Serial` and similar Mathlib typeclasses throughout, or unfold all to explicit quantifiers.

Teammate A flagged this; Teammate C notes the same asymmetry exists between `Cube.lean` (uses `IsTrans`, `Relation.RightEuclidean`, `Std.Refl`, `Std.Symm`, `Relation.Serial`) and `Metalogic/` (uses inline predicates for everything except serial). This reinforces the need for a consistent choice documented across both layers.

**Confidence**: Certain.

#### M4. S5 Asymmetry: No Dedicated `S5Soundness.lean`

All 14 non-S5 logics have a dedicated `XSoundness.lean` file. S5 soundness wrappers (`s5_soundness`, `s5_soundness_derivable`) live inside `Soundness.lean` alongside the parameterized machinery. This means `Soundness.lean` is not purely parameterized infrastructure — it doubles as the S5 soundness file. Teammate B identified this; Teammate C corroborates (noting `HilbertS5` also lacks a `HasAxiom5` instance because S5 is axiomatized as KT4B, not KT5).

**Confidence**: High (Teammate B confirmed no `S5Soundness.lean` on disk).

#### M5. Universe Polymorphism Constraint Undocumented

Completeness theorems use `universe u; variable {Atom : Type u}` with worlds quantified at the same universe `u`. This is a silent limitation: models in a larger universe than the atom type cannot be used. Teammate C flagged this as a medium-risk undocumented constraint; Teammate B noted the `Type*` vs `universe u; Type u` asymmetry between soundness and completeness files is intentional but not commented.

**Confidence**: Medium-high (Teammate C analysis; Teammate B corroborates the asymmetry).

---

### Low Priority

#### L1. Instances.lean: `ModusPonens`/`Necessitation` Boilerplate (15 × identical)

Each of the 15 proof systems has an identical 8-line `ModusPonens` and `Necessitation` instance block differing only in the tag type. Total: ~240 lines of near-identical code in a 1532-line file. Not easily abstracted without Lean 4 macro/instance generation support. Teammate A flagged it as worth documenting even if not immediately fixable.

**Confidence**: Certain.

#### L2. Docstring Placement Anomaly in `Modal/Metalogic.lean`

The `/-! # Modal Metalogic Module ... -/` docstring appears after the import block rather than before `@[expose] public section`, violating the convention established in `Temporal/ProofSystem.lean`. Teammate B identified this as the only structural deviation from the codebase-wide convention.

**Fix**: Move the `/-! ... -/` block to immediately precede `@[expose] public section`.

**Confidence**: High (Teammate B confirmed by line comparison).

#### L3. Section Header Inconsistency ("Theorems" vs "Wrappers")

Some soundness files use `/-! ## X Soundness Theorems -/`; others use `/-! ## X Soundness Wrappers -/`. The "Wrappers" label is technically more accurate (these delegate to the parameterized `soundness`). Teammate A flagged this as cosmetic.

**Confidence**: Certain (cosmetic only).

#### L4. Cube.lean Inclusion Lattice Incomplete

`Cube.lean` proves 5 inclusion theorems (`k_subset_d`, `k_subset_b`, `k_subset_four`, `k_subset_five`, `d_subset_t`) out of ~40–50 non-trivial inclusion pairs in the full 15-node lattice. The docstring acknowledges this. Teammate D identified it as a documentation/completeness gap but notes the remaining inclusions can be derived from the existing 5 via transitivity of `⊆`.

**Confidence**: High.

#### L5. No Test Coverage for Modal Logic

`CslibTests/` has tests for HML, LambdaCalculus, CCS, but nothing for modal logic. The `Cube.lean` validity checks (`K.k_valid`, `T.t_valid`) serve as minimal sanity checks but are not executable examples or negative tests (e.g., "K ⊬ □p → p"). Teammate D identified this gap.

**Confidence**: Certain (absence confirmed).

---

## Quick Fixes (< 30 min each)

1. **Fix unused `ψ` warnings** in all soundness wrapper theorems: replace `fun ψ h_ax w => ...` with `fun _ h_ax w => ...`. Affects 10+ sites across ~8 soundness files. One-character change per site.

2. **Fix `MCS.lean` namespace collision**: Move `Modal.SetConsistent` and `Modal.SetMaximalConsistent` declarations out of `namespace Cslib.Logic.Modal`. Eliminates 2 `Modal.Modal.*` warnings.

3. **Remove dead `simp_wf` calls** in `DeductionTheorem.lean` at lines 116 and 183. Delete 2 lines.

4. **Replace `push_neg` with `push Not`** in `Basic.lean:115`. One-line fix.

5. **Fix docstring placement** in `Modal/Metalogic.lean`: move the `/-! ... -/` block to precede `@[expose] public section`. One cut-and-paste.

6. **Update `Completeness.lean` and `Soundness.lean` module headers** to reflect their actual scope (all 15 logics, not just S5). Two header edits.

7. **Standardize section headers** in soundness files: replace all `/-! ## X Soundness Theorems -/` with `/-! ## X Soundness Wrappers -/` (or vice versa, whichever is chosen as canonical). Pure find-and-replace.

---

## Refactoring Opportunities

### R1. Extract `neg_consistent_of_not_derivable` (Highest Impact)

Create a shared lemma in `Completeness.lean` (or a new `Metalogic/Completeness/Boilerplate.lean`):

```lean
/-- If `φ` is not derivable, then `{¬φ}` is consistent.
Requires only the classical propositional axioms K, S, EFQ, Peirce, and modal K. -/
theorem neg_consistent_of_not_derivable
    {Axioms : Proposition Atom → Prop}
    (h_implyK : ∀ φ ψ, Axioms (implyK φ ψ))
    (h_implyS : ∀ φ ψ χ, Axioms (implyS φ ψ χ))
    (h_efq : ∀ φ, Axioms (efq φ))
    (h_peirce : ∀ φ ψ, Axioms (peirce φ ψ))
    {φ : Proposition Atom}
    (h_not_deriv : ¬Derivable Axioms φ) :
    Modal.SetConsistent Axioms {Proposition.neg φ} := ...
```

Replacing the 30-line `h_cons` block in each of the 10 non-T completeness files with a single call.

**Estimated line reduction**: 300 lines (Teammate A estimate) to 600 lines (Teammate D estimate, including scaffolding).

### R2. Extract `k_axiom_sound_shared` for Propositional Cases

Create a shared lemma proving validity for the 5 shared axiom cases (`implyK`, `implyS`, `efq`, `peirce`, `modalK`) parameterized over any axiom set containing these predicates. Each per-logic `*_axiom_sound` then handles only its unique modal axioms and delegates the rest.

**Estimated line reduction**: ~65 lines (5 cases × 13 files).

### R3. Standardize Frame Condition Style

Pick one representation for all frame conditions across both `Metalogic/` soundness/completeness files:
- **Option A**: Explicit universal quantifiers for all (drop `Relation.Serial`, `IsTrans`, etc.)
- **Option B**: Mathlib typeclasses for all (adopt `Relation.Reflexive`, `Relation.Symmetric`, `Relation.Transitive`, `Relation.Euclidean`, `Relation.Serial`)

Option B is preferable for Mathlib alignment (Teammate D). This change would also help close the `Cube.lean`–`Metalogic/` notation gap identified in H4.

### R4. Centralize Truth Lemma Documentation

Add a `Metalogic/Overview.lean` (or a dedicated section in `Completeness.lean`) explaining:
- Why three truth lemma families exist (`truth_lemma`, `k_truth_lemma`, `truth_lemma_d`)
- Which logics use which, and why (the T/D/K semantic distinction)
- The canonical model reuse pattern
- The universe polymorphism constraint (same universe for `World` and `Atom`)

### R5. Create `S5Soundness.lean`

Move `s5_soundness` and `s5_soundness_derivable` from `Soundness.lean` into a new `S5Soundness.lean`, making `Soundness.lean` purely parameterized infrastructure. This makes all 15 logics fully symmetric.

### R6. Convert Flexible `simp` to `simp only`

Run `simp?` at each of the 12 flexible `simp` sites to produce the lemma list, then replace with `simp only [...]`. Use `#check @simp_rfl` as a reference. Files affected: `DeductionTheorem.lean`, `MCS.lean`, `Completeness.lean`, `KCompleteness.lean`, `TCompleteness.lean`, `DCompleteness.lean`, `S4Completeness.lean`, `K4Completeness.lean`, `D45Completeness.lean`.

---

## Architecture Recommendations

### A1. Bridge Theorems: Connect Cube.lean to Metalogic

Add a `Metalogic/Axiomatization.lean` file (or a section in `Cube.lean`) with theorems of the form:

```lean
theorem k_axiomatization : ∀ φ, Derivable (@KAxiom Atom) φ ↔ φ ∈ K World Atom
```

for each of the 15 logics. These follow directly from the existing soundness and completeness theorems combined. Without them, the library has two parallel correct halves that cannot be composed.

This is the single highest-leverage architectural addition: it would allow users to reason about the modal cube inclusions (`K ⊆ T`) at the proof-theoretic level and would complete the library's conceptual picture.

### A2. Unify Axiom Schemata via a Propositional Base

Define a `NormalModalBase` predicate capturing the 5 shared axioms:

```lean
inductive NormalModalBase : Proposition Atom → Prop where
  | implyK | implyS | efq | peirce | modalK
```

Then define each system as `NormalModalBase ∨ SpecificAxioms`. This eliminates the propositional-base repetition in all 15 `XAxiom` inductives. Teammate D estimates this would eliminate 70% of the verbosity in `Instances.lean`.

**Caution**: This refactor threads through canonical model construction (which currently receives the full `Axioms` predicate). Teammate D rates this as medium-confidence on feasibility without major proof rewrites. Attempt only after R1 and R2 are complete.

### A3. Add Test Coverage

Create `CslibTests/Modal.lean` with:
- At least one `#check` per logic demonstrating soundness and completeness types
- Example derivations: K derives `□(p → q) → (□p → □q)` but not `□p → p`
- Example non-derivations: K45 does not derive axiom T (requires a semantic argument, possible via the soundness theorem with a countermodel)

### A4. Complete Cube.lean Inclusion Lattice

Add the remaining ~35–45 inclusion theorems to `Cube.lean`. Given the 5 base inclusions already proved, these follow by transitivity and union monotonicity. A systematic approach: add a Hasse diagram comment and prove the inclusions layer by layer.

### A5. GL/Grz Preparedness (Strategic)

The current architecture scales to adding GL (Godel-Lob) and Grz (Grzegorczyk) without changes to `DerivationTree` or `CanonicalModel`. The main additions required:
- New `GLAxiom` and `GrzAxiom` inductives
- `canonical_noetherian` lemma (GL-specific canonical frame property using `WellFounded`)
- GL-specific truth lemma (GL lacks T, so `k_truth_lemma`-style)

**Note**: GL completeness is significantly harder than the cube logics (requires filtration or Sahlqvist correspondence rather than simple canonical model). Teammate D rates this as medium-confidence on the difficulty estimate.

The Priority A2 refactor (unifying axiom schemata) should be completed before adding GL/Grz to avoid multiplying the existing boilerplate by 2.

---

## Teammate Contributions

| Teammate | Angle | Status | Key Finding |
|----------|-------|--------|-------------|
| A | Implementation Quality | completed | 51 linter warnings, h_cons duplication in 10 files, MCS namespace collision bug |
| B | Cross-Logic Consistency | completed | Internal soundness structure excellent, S5 asymmetry (no S5Soundness.lean), docstring placement anomaly |
| C | Critic | completed | Zero sorry/axioms (clean), Cube.lean–Metalogic disconnect, S5 lacks HasAxiom5, canonical_serial API asymmetry |
| D | Horizons | completed | ~2,000–2,500 lines structural repetition, three truth lemma families undocumented, no test coverage, Mathlib readiness assessment |

---

## Conflicts Resolved

**Conflict 1: h_cons block size estimate (A vs D)**

Teammate A estimated ~300 lines of elimination (10 files × 30 lines). Teammate D estimated ~600 lines. Resolution: both are correct for different measurements. Teammate A counts only the `h_cons` block itself; Teammate D includes scaffolding and `have` bindings that bind the result. The true number is between 300 and 600 lines, depending on how aggressively the surrounding `have h_cons` scaffolding is absorbed into the helper. Both teammates agree this is the highest-priority deduplication target.

**Conflict 2: canonical_symm hypothesis minimality (C vs BRV)**

Teammate C noted that `canonical_symm` uses `h_K` (modal K axiom) but BRV's proof of symmetry uses only axiom B and propositional axioms. This could be read as suggesting `h_K` is non-minimal. Teammate C's own analysis resolves this: the Lean proof uses a by-contradiction argument (assume `box phi in T`, prove `phi in S` by contradiction) which differs from BRV's direct argument. Both arguments are valid; the Lean proof's hypothesis set is minimal for the chosen proof strategy. No actual conflict — only a difference in proof strategy between BRV and the Lean encoding.

**Conflict 3: `Relation.Serial` vs lambda — intentional or debt?**

Teammate A treated the `Relation.Serial` inconsistency as unintentional style debt. Teammate C noted it also appears in `Cube.lean` (which uses `Relation.RightEuclidean`, `IsTrans`, etc.) as a consistent pattern. Resolution: the `Cube.lean` usage is deliberate Mathlib alignment; the `Metalogic/` usage is partial. Standardizing `Metalogic/` to match `Cube.lean`'s Mathlib typeclass usage (Recommendation R3) would be the correct resolution, not discarding `Relation.Serial`.

**No other conflicts found.** Teammates A, B, C, and D are in strong agreement on the major findings. The mathematical correctness verdict (Teammate C: PASS on all checks) is not challenged by any other teammate.

---

## References

- Blackburn, de Rijke, Venema — *Modal Logic* (BRV). Referenced throughout `Metalogic/` docstrings.
- `Cslib/Logics/Modal/Metalogic/` — primary audit scope
- `Cslib/Logics/Modal/ProofSystem/Instances.lean` — instance boilerplate analysis
- `Cslib/Foundations/Logic/ProofSystem.lean` — bundled typeclass hierarchy
- `Cslib/Logics/Modal/Cube.lean` — semantic layer; disconnect with Metalogic identified
- `Cslib/Logics/Temporal/Metalogic/` and `Cslib/Logics/Bimodal/` — cross-logic consistency baseline (Teammate B)
- `specs/literature/advanced_modal_logic_2.md` — GL/Grz strategic context (Teammate D)
