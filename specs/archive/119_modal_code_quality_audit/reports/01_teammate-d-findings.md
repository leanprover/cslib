# Teammate D Findings: Modal Code Quality Audit (Horizons)

**Task**: 119 -- Modal code quality audit
**Teammate**: D (Horizons -- strategic / long-term maintainability perspective)
**Artifact**: 01

---

## Key Findings

### 1. Modal Cube Coverage: All 15 Logics Present

The standard 15-node modal cube is fully represented:

| Logic | Axioms | Soundness | Completeness | Notes |
|-------|--------|-----------|--------------|-------|
| K     | `KAxiom` | `KSoundness.lean` | `KCompleteness.lean` | K-specific truth lemma (no T) |
| T     | `TAxiom` | `TSoundness.lean` | `TCompleteness.lean` | Uses `truth_lemma` (has T) |
| D     | `DAxiom` | `DSoundness.lean` | `DCompleteness.lean` | D-specific truth lemma + `canonical_serial` |
| B (KB) | `BAxiom` | `BSoundness.lean` | `BCompleteness.lean` | Uses `k_truth_lemma` + `canonical_symm` |
| K4    | `K4Axiom` | `K4Soundness.lean` | `K4Completeness.lean` | Uses `k_truth_lemma` + `canonical_trans` |
| K5    | `K5Axiom` | `K5Soundness.lean` | `K5Completeness.lean` | Uses `canonical_eucl_from_5` |
| K45   | `K45Axiom` | `K45Soundness.lean` | `K45Completeness.lean` | |
| KB5   | `KB5Axiom` | `KB5Soundness.lean` | `KB5Completeness.lean` | |
| TB    | `TBAxiom` | `TBSoundness.lean` | `TBCompleteness.lean` | |
| DB    | `DBAxiom` | `DBSoundness.lean` | `DBCompleteness.lean` | |
| D4    | `D4Axiom` | `D4Soundness.lean` | `D4Completeness.lean` | |
| D5    | `D5Axiom` | `D5Soundness.lean` | `D5Completeness.lean` | |
| D45   | `D45Axiom` | `D45Soundness.lean` | `D45Completeness.lean` | |
| S4    | `S4Axiom` | `S4Soundness.lean` | `S4Completeness.lean` | |
| S5    | `ModalAxiom` | `Soundness.lean` | `Completeness.lean` | Original "main" system |

All 15 standard logics are present. No gaps in the modal cube.

### 2. Massive Code Duplication: The Central Architecture Problem

Every axiom inductive type (15 total) repeats the same 4-5 propositional axiom constructors verbatim: `implyK`, `implyS`, `efq`, `peirce`, and `modalK`. A representative from `Instances.lean`:

```lean
-- K: 5 constructors (4 prop + 1 modal)
-- T: 6 constructors (4 prop + 2 modal)
-- D: 6 constructors
-- S4: 7 constructors
-- S5: 8 constructors
-- ...and so on for all 15 systems
```

Every completeness file (15 total) also contains a near-identical ~40-line block proving `{neg phi}` is consistent, which boilerplate is required before the Lindenbaum invocation. The consistency block is copy-pasted across: `KCompleteness.lean`, `K4Completeness.lean`, `S4Completeness.lean`, `D45Completeness.lean`, and every other completeness file.

**Quantitative estimate**: The 5,333 total lines across the 15 metalogic files includes perhaps 2,000--2,500 lines of pure structural repetition.

### 3. Three Distinct Truth Lemma Families

The completeness architecture has fragmented into three truth lemma variants:

- `truth_lemma` (in `Completeness.lean`): Requires axiom T hypothesis -- used for T, TB, S4, S5.
- `k_truth_lemma` (in `KCompleteness.lean`): No axiom T -- used for K, K4, K5, K45, KB5, B.
- `truth_lemma_d` (in `DCompleteness.lean`): D-specific box witness -- used for D, D4, D5, D45, DB.

This three-way split is architecturally sound (reflecting genuine semantic differences) but undocumented. A new contributor reading `K4Completeness.lean` will not easily understand why `k_truth_lemma` rather than `truth_lemma` is used.

### 4. Per-Logic Axiom Schemata Have Excessive Redundancy

All 15 axiom inductive types in `Instances.lean` are self-contained, repeating the propositional base. The propositional axioms (`implyK`, `implyS`, `efq`, `peirce`) and the modal K axiom are present in every logic because DerivationTree is parameterized over a single axiom predicate. This prevents reuse.

A Lean 4 solution exists: define a `PropositionalAxioms` predicate as a sub-predicate, then define each modal axiom as `PropositionalAxioms ∨ ModalSpecificAxioms`. However this would require changing the canonical model construction to accept the composed form, which is non-trivial.

### 5. No Test Files for Modal

There is no `CslibTests/Modal.lean` or equivalent. The `CslibTests/` directory contains tests for HML, LambdaCalculus, CCS, etc., but nothing for modal logic.

The `Cube.lean` file includes a minimal validity section (`K.k_valid`, `T.t_valid`) which serves as a sanity check, but there are no executable examples, no #check proofs of individual theorems, and no test exercises showing that the axiom instances produce the right theorems.

### 6. Logic Ordering in Cube.lean is Incomplete

`Cube.lean` defines all 15 logics as sets and proves 5 inclusion theorems (`k_subset_d`, `k_subset_b`, `k_subset_four`, `k_subset_five`, `d_subset_t`). However the docstring acknowledges that "the other inclusions in the Modal Cube can be derived from the properties of `⊆` and `∪`" without actually proving them. The full 15-node inclusion lattice has roughly 40-50 non-trivial inclusion pairs; only 5 are proved.

### 7. Mathlib Alignment Assessment

The codebase aligns well with Mathlib conventions in several areas:

**Aligned**:
- Uses `Relation.Serial`, `Relation.RightEuclidean`, `Std.Refl`, `Std.Symm`, `IsTrans` from Mathlib -- these are the right typeclasses
- The `@[scoped grind =]` and `@[simp]` tagging follows Mathlib patterns
- The `noncomputable def CanonicalModel` with `Set`-based semantics is idiomatic
- The `@[expose] public section` pattern is a Cslib/IdrisDoc-style convention, not standard Mathlib -- but consistent within the project

**Divergences**:
- The `Proposition` type is a project-local definition; Mathlib has no modal logic formulas, so this is unavoidable
- The `DerivationTree` is `Type`-valued (not `Prop`), following a deliberate design choice inherited from BimodalLogic to allow computable height -- this matches Mathlib practice for constructive trees
- The parameterized `Axioms : Proposition Atom → Prop` approach is unconventional compared to Mathlib's typeclass-based approach for logic families

**Mathlib PR Potential**: The semantic layer (`Model`, `Satisfies`, frame conditions, `theory`, `TheoryEq`) is clean and generic enough to be Mathlib-worthy. The canonical model construction and Lindenbaum lemma are also strong candidates. The axiom schemata duplication would need to be resolved first.

### 8. Documentation Quality

Each file has a module-level docstring with `## Main Results`, references to Blackburn-de Rijke-Venema (BRV), and inline comments pointing to specific theorems (e.g., "BRV Theorem 4.23"). This is good. However:

- The connection between the three truth lemma families is not documented anywhere centrally
- The `Completeness.lean` header says "Completeness Theorem for S5 Modal Logic" but `truth_lemma` is actually a parameterized helper used by many other logics -- the header is misleading
- The relationship between `CanonicalWorld` / `CanonicalModel` (in `Completeness.lean`) and the completeness proofs for non-T logics (which reuse these definitions) is not clearly explained

---

## Strategic Recommendations

### Priority 1: Extract a Parameterized Consistency Boilerplate Helper

The ~40-line "show `{neg phi}` is consistent" block repeating across all 15 completeness files is the highest-impact single refactor. It should become:

```lean
theorem neg_consistent_of_not_derivable
    {Axioms : Proposition Atom → Prop}
    (h_implyK : ...) (h_implyS : ...) (h_efq : ...) (h_peirce : ...)
    {φ : Proposition Atom} (h_not_deriv : ¬Derivable Axioms φ) :
    Modal.SetConsistent Axioms {Proposition.neg φ}
```

This single extracted lemma would eliminate ~600 lines of duplication across the 15 completeness files.

### Priority 2: Unify the Axiom Schemata via a Propositional Base

The propositional base (4 axioms + modalK) should be factored:

```lean
-- Option A: Type-level sum
inductive ModalSystemAxiom (Base : Proposition Atom → Prop)
    (Extra : Proposition Atom → Prop) : Proposition Atom → Prop where
  | base (h : Base φ) : ModalSystemAxiom Base Extra φ
  | extra (h : Extra φ) : ModalSystemAxiom Base Extra φ

-- Or Option B: The normal logic axiom base
inductive NormalModalBase : Proposition Atom → Prop where
  | implyK | implyS | efq | peirce | modalK  -- the 5 shared axioms

-- then K45 = ModalSystem NormalModalBase [modalFour, modalFive]
```

This refactor is larger and would require updating all 15 completeness proofs, but eliminates 70% of the verbosity in `Instances.lean`.

### Priority 3: Centralize the Truth Lemma Documentation

Add a `Metalogic/Overview.lean` (or similar) that explains:
1. Why there are three truth lemma families and which to use for each logic
2. The canonical model reuse pattern (all 15 logics use `CanonicalWorld`/`CanonicalModel` from `Completeness.lean`)
3. The box witness pattern and why K requires a different construction than T-containing logics

### Priority 4: Add a Test File

Create `CslibTests/Modal.lean` with:
- Decidable instances or example derivations
- At least one `#check` per logic showing soundness and completeness types
- Small worked examples: e.g., K derives `□(p → q) → (□p → □q)` but not `□p → p`

---

## Long-term Architecture

### Scalability Assessment: GL, Grz, Provability Logics

The literature at `specs/literature/advanced_modal_logic_2.md` confirms that GL (Godel-Lob) and Grz (Grzegorczyk) are the primary "next" logics after the modal cube. Their frame conditions are:

- **GL**: Transitive + conversely well-founded (Noetherian) frames
- **Grz**: Reflexive + transitive + antisymmetric + Noetherian frames

Both require frame conditions not currently in the system:
- `Acc r` (well-foundedness of the converse) -- available in Mathlib as `WellFounded`
- The "no infinite ascending chain" property -- expressible but not currently used

The current architecture scales well to add these. GL would require:
1. A new `GLAxiom` inductive (the Lob axiom: `□(□φ → φ) → □φ`)
2. A `canonical_noetherian` lemma (GL-specific canonical frame property)
3. A GL-specific truth lemma (since GL lacks T, it would use `k_truth_lemma` or a GL variant)

The parameterized `DerivationTree` and `CanonicalModel` infrastructure would be reused unchanged. The main challenge is that GL completeness is significantly harder (requiring filtration or Salqvist-style argument), not a simple canonical model theorem.

### The Redundancy Cliff

The current architecture works well for 15 logics but would become unmanageable at 25-30. The GL/Grz addition would add 4 more files (GLAxiom in Instances, GLSoundness, GLCompleteness, GrzSoundness, GrzCompleteness) plus more rows in Instances.lean. Without the Priority 2 refactor above, each new logic costs ~100+ lines of near-identical axiom schema and instance boilerplate.

### Cube.lean: Semantic vs Syntactic Disconnect

The 15 logics in `Cube.lean` are defined semantically (as sets of valid formulas over frame classes), while the Hilbert systems in `Instances.lean` + `Metalogic/` are syntactic. The soundness and completeness theorems bridge these. However, Cube.lean's inclusion ordering (`K ⊆ T`, etc.) is proved semantically, and the corresponding syntactic versions (if `⊢_K φ` then `⊢_T φ`) are not proved anywhere. A new contributor could easily miss that the `K World Atom` in Cube.lean and the `Derivable (@KAxiom Atom) φ` in the metalogic are the same thing only via the completeness bridge.

Consider adding to `Cube.lean` a section:

```lean
/-- The axioms of K derive exactly the K-valid formulas (soundness + completeness). -/
theorem k_axiomatization : ∀ φ, Derivable (@KAxiom Atom) φ ↔ φ ∈ K World Atom
```

This would explicitly connect the two presentations.

### Mathlib PR Readiness

The modal logic formalization is closer to Mathlib readiness than the bimodal side. The main obstacles to a Mathlib PR are:

1. **Propositional axiom duplication** -- Mathlib maintainers would reject 15 near-identical inductive definitions. This must be resolved first.
2. **The 3-truth-lemma architecture** -- needs documentation and possibly consolidation into a single parameterized truth lemma with optional hypotheses.
3. **Module structure** -- Mathlib uses a flat `Mathlib.Logic.Modal.*` namespace; the project's `Cslib.Logic.Modal.*` is fine but would need renaming.
4. **Missing `Finset`-based subformula closure** -- Mathlib completeness proofs often need finite Lindenbaum lemmas for decidability; the current Lindenbaum is non-constructive. This is acceptable for now but limits Mathlib integration.

---

## Confidence Level

**High confidence** on:
- All 15 logics being present and covered
- The three truth lemma families and their usage patterns
- The duplication analysis (code-read, quantified)
- The test coverage gap (absence of CslibTests/Modal.lean confirmed)
- The Cube.lean ordering incompleteness (only 5 of ~40 inclusions proved)
- The Mathlib alignment assessment

**Medium confidence** on:
- The LOC estimate for duplication (2,000--2,500 lines out of 5,333) -- depends on what counts as "structural repetition"
- The GL/Grz feasibility estimate -- GL completeness has subtleties (it requires a different argument than the simple canonical model construction used here)
- The Mathlib PR timeline -- Mathlib maintainers' appetite for modal logic content is unknown

**Lower confidence** on:
- Whether the parameterized axiom refactor (Priority 2) is feasible without major proof rewrites -- the canonical model construction's explicit axiom hypotheses thread through many proofs
