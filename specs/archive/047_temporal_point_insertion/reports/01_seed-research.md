# Seed Research Report: Task 47 — Temporal Labeled Frame Types and Point Insertion

**Task**: 47 — Temporal labeled frame types and point insertion
**Date**: 2026-06-09
**Source**: Task 50 team research (teammates A, B, C, D)
**Purpose**: Pre-digested research to allow task 47 to skip or accelerate its research phase

---

## Overview

Task 47 ports the chronicle type definitions and point insertion proofs from the bimodal `BXCanonical/Chronicle/` to a new temporal-only module. The key mathematical content is Burgess Lemmas 2.6-2.8: given a chronicle with a defect (a failed C5a or C6a condition), we can insert a new point to eliminate the defect while preserving all chronicle conditions. The Xu 1988 C0-C6 formulation provides a cleaner Lean target than Burgess's original presentation.

**Central simplification vs bimodal**: The temporal version eliminates all C5b/C6b conditions for box (no □ modality). This removes roughly half of PointInsertion.lean's proof cases.

**Prerequisite dependency**: Task 47 depends on propositional combinators and temporal derived theorems created in Task 46 Phase 0. Do not start Task 47 until those files exist.

---

## 1. Literature Map: Burgess 1982, Lemmas 2.6-2.8 and Chronicle Conditions

### Chronicle Conditions (C0-C5a/b)

Burgess defines a chronicle as a partial function (f,g) on a finite subset of Q satisfying:

| Condition | Statement |
|---|---|
| C0 | f maps a finite subset of Q to MCSs |
| C0' | dom f is finite |
| C1 | g maps pairs (x,y) with x < y in dom f to DCSs |
| C2 | r(f(x), g(x,y), f(y)) for x < y (equivalently: r lower bound) |
| C2' | R(f(x), g(x,y), f(y)) for consecutive x,y (R-maximality at consecutive points) |
| C3 | g(x,z) = g(x,y) ∩ f(y) ∩ g(y,z) for x < y < z (intersection condition) |
| C4a | If ¬U(γ,δ) ∈ f(x) and γ ∈ f(y) with x < y, then ∃z with x < z < y and ¬δ ∈ f(z) |
| C5a | If U(ξ,η) ∈ f(x), then ∃y > x with ξ ∈ f(y) and η ∈ g(x,y) |
| C4b | Mirror image of C4a for Since |
| C5b | Mirror image of C5a for Since |

**Note**: In bimodal, there are additional C5b/C6b conditions for □-witnesses. These are **entirely absent** from the temporal version.

### Xu 1988 Reformulation (Definition 2.5)

Xu uses abstract T* (not necessarily Q) and an equivalent C0-C6 numbering:

| Xu Condition | Burgess Equivalent | Notes |
|---|---|---|
| C1 | C0 | dom f is finite |
| C2 | (implicit) | T* is a linear order |
| C3 | C3 | Intersection condition for g |
| C4 | C3 extended | g(t,t') ⊆ f(t'') for t < t'' < t' |
| C5a | Burgess C4a | Counterexample to ¬U |
| C6a | Burgess C5a | Witness for U |

**Recommendation**: Use Xu's C0-C6 labeling in Lean, as it separates frame conditions more explicitly and is cleaner for structural induction. Note that C6a (Xu) = C5a (Burgess) — "a C6a defect" means the Until-witness condition fails.

### Lemma 2.6 — Point Insertion for ¬δ (C4a defect elimination)

**Setting**: R(A,B,C) and δ ∉ B.

**Conclusion**: ∃B', D, B'' with ¬δ ∈ D and R(A,B',D), R(D,B'',C), B = B' ∩ D ∩ B''

**Proof strategy**:
1. Construct D₀ = {S(α,β) : α∈A, β∈B} ∪ B ∪ {¬δ} ∪ {U(γ,β) : γ∈C, β∈B}
2. Show consistency of D₀ using A4a and A5a crucially (δ ∉ B gives β₀ ∈ B, γ₀ ∈ C with ¬U(γ₀, β₀∧δ) ∈ A)
3. Extend D₀ to MCS D
4. Apply the Intersection Lemma (2.5) to establish B = B' ∩ D ∩ B''

**Axioms doing heavy lifting**: A4a (connect current to future), A5a (U self-reinforcing)

### Lemma 2.7 — Point Insertion for U-witness (C5a/C6a defect elimination)

**Setting**: R(A,B,C), U(ξ,η) ∈ A, η ∉ B.

**Conclusion**: ∃B', D, B'' with η ∈ B', ξ ∈ D, R(A,B',D), R(D,B'',C), B = B' ∩ D ∩ B''

**Proof strategy**: Uses A7a (linearity — three-way disjunction) to get three cases, rules out two, constructs the inserted point in the remaining case.

**Key feature**: This is the most technically demanding lemma — bimodal `PointInsertion.lean` is 3,556 lines largely because of this lemma and its mirror image.

### Lemma 2.8 — Point Insertion Variant

**Setting**: R(A,B,C), U(ξ,η) ∈ A, ¬(ξ ∨ (η∧U(ξ,η))) ∈ C.

**Conclusion**: Same conclusion as Lemma 2.7.

**Proof**: Slight modification of Lemma 2.7's proof using the additional hypothesis about C.

---

## 2. Infrastructure Audit: Per-File Transfer Analysis

### Chronicle/ChronicleTypes.lean (386 lines) → ~85% transfer rate

**What transfers directly**:
- `Chronicle` structure: `(dom : Finset Rat, f : Rat → Set Formula, g : Rat → Rat → Set Formula)`
- DCS definitions, `ClosedUnderDerivation`, `mcs_is_dcs`, `cud_modus_ponens`
- Chronicle conditions C0-C5 as predicates
- `IsChronicle` predicate

**What does NOT transfer**:
- `liftBase`, `mcs_to_base` (FrameClass conversion helpers) → remove
- `FrameClass` parameter → remove
- `ModalSaturation` import → remove (purely bimodal)

**Mechanical changes**:
1. Remove `FrameClass` parameter
2. Remove `liftBase`/`mcs_to_base` helpers
3. Remove `ModalSaturation` import
4. Import path rewrite

**Note on DCS**: The `SetDeductivelyClosed` type and `mcs_is_dcs` may already be created in Task 46 Phase 0. Check for existence before duplicating.

### Chronicle/PointInsertion.lean (3556 lines) → ~90% transfer rate

**What transfers directly**: All of Burgess Lemmas 2.4-2.7 proof content, `BurgessR3` and `BurgessR3Maximal` definitions, seed consistency proofs, the point insertion construction.

**What does NOT transfer**:
- References to bimodal `Theorems.TemporalDerived` and `Theorems.Propositional.Core` → replace with Task 46 Phase 0 versions
- `FrameClass` parameter → remove throughout
- References to bimodal-specific theorems about □ → remove (should be zero such references in the proof content)

**Key dependency on Task 46 Phase 0**: PointInsertion.lean uses:
- `temp_k_dist_derived` → from `Temporal/Theorems/TemporalDerived.lean` (Task 46 Phase 0)
- `past_necessitation`, `past_k_dist` → from `Temporal/Theorems/TemporalDerived.lean` (Task 46 Phase 0)
- `double_negation`, propositional combinators → from `Temporal/Theorems/Propositional/Core.lean` (Task 46 Phase 0)

**Do NOT start Task 47 until Task 46 Phase 0 is complete.**

---

## 3. Key Proof Strategy Notes

### Point Insertion is the Heart of the Construction

The 3-lemma chain (2.6, 2.7, 2.8) is the central construction of the entire chronicle proof. The counterexample elimination (Task 48) and truth lemma (Task 49) are downstream applications.

**For 2.6**: Consistency of D₀ is the hard part. The proof constructs a candidate set and shows it is consistent using:
- The r-relation properties (established in Task 46)
- A4a (connecting current time to future)
- A5a (U is self-reinforcing)

**For 2.7**: The linearity axiom A7a is central. It gives a three-way disjunction: either (i) η ∈ B, (ii) there exist B', D, B'' satisfying the conclusion immediately, or (iii) a contradiction. The proof rules out (i) by hypothesis (η ∉ B) and (iii) by the r-relation consistency, leaving (ii).

### BurgessR3 and BurgessR3Maximal

The bimodal PointInsertion.lean defines `BurgessR3` as a ternary relation and `BurgessR3Maximal` as its maximality. These are used as intermediate steps in the point insertion proofs. The temporal versions should have identical definitions (the R3 relation is purely about temporal witnesses).

### Mirror Images for S

Each lemma has a mirror image for the Since direction:
- 2.6 → C4b defect elimination
- 2.7/2.8 → C5b/C6b defect elimination (Since witnesses)

**Key simplification**: In bimodal, there are ADDITIONAL mirror cases for box-witnesses. These are entirely absent in temporal. This means the temporal PointInsertion.lean is significantly shorter than bimodal's 3,556 lines despite 90% transfer rate.

---

## 4. Naming Conventions

Following Teammate D's recommendation for Task 41 alignment:

| Bimodal Name | Temporal Name | Notes |
|---|---|---|
| `ChronicleTypes.Chronicle` | `ChronicleTypes.Chronicle` | Keep identical |
| `IsChronicle` | `IsChronicle` | Keep identical |
| `ClosedUnderDerivation` | `ClosedUnderDerivation` | Keep identical |
| `BurgessR3` | `BurgessR3` | Keep identical |
| `BurgessR3Maximal` | `BurgessR3Maximal` | Keep identical |
| `insert_point_c4a` | `insert_point_c4a` | Keep identical |
| `insert_point_c5a` | `insert_point_c5a` | Keep identical |

Use **Xu condition numbering** in Lean definitions (C5a/C6a) since they map more directly to what the proofs establish. Note in comments that C6a (Xu) = C5a (Burgess) for cross-reference.

---

## 5. Implementation Strategy

### Recommended Phase Sequence for Task 47

1. **Phase 1**: Create `Chronicle/ChronicleTypes.lean` (~150-250 lines)
   - Chronicle structure with dom, f, g fields
   - Conditions C0-C5 as `Prop`-valued predicates
   - `SetDeductivelyClosed` if not yet in Task 46 (or import from Task 46)
   - `mcs_is_dcs`, `cud_modus_ponens`

2. **Phase 2**: Create `Chronicle/PointInsertion.lean` (~1,200-2,000 lines)
   - Port in order: Lemma 2.4 (witness existence) → Lemma 2.5 (intersection) → Lemma 2.6 (¬δ insertion) → Lemma 2.7 (U-witness insertion) → Lemma 2.8 (variant) → Since mirrors
   - Each step builds on the previous
   - Verify axiom instantiations compile before proceeding

### Incremental Verification Strategy

After each lemma port:
1. Run `lake build` or check with `lean_diagnostic_messages`
2. Confirm no sorry stubs needed
3. Verify the temporal axiom being invoked exists in the temporal system

---

## 6. Risks and Warnings

### Risk 1: Missing Propositional Combinators

PointInsertion.lean calls propositional combinators from `Theorems.Propositional.Core` that may not exist in the temporal module after Task 46 Phase 0. Check before starting Task 47:
- `temporal_pairing`
- `temporal_lce_imp`, `temporal_rce_imp`
- `temporal_double_negation`
- `temporal_contraposition`

### Risk 2: A7a (Linearity) Instantiation

Lemma 2.7 requires the linearity axiom A7a: `U(α,β) → S(α,β) ∨ (β ∧ U(α,β)) ∨ U(α ∧ S(α,β), β)`. Verify the temporal axiom system includes this in the form needed (check `Temporal/ProofSystem/Axioms.lean`).

### Risk 3: Bimodal Sorry Stubs for Open Guard

The bimodal `PointInsertion.lean` has sorry stubs for "open guard semantics". Check the comment context — if these are in the main proof path (not optional lemmas), temporal adaptation must find an alternative. The temporal system may not have "open guard" complications at all.

### Risk 4: Consistency Set Construction

For Lemma 2.6, the proof must show that the constructed D₀ is consistent (no contradiction derivable from it). This depends on:
- A4a instantiation at MCS level
- A5a instantiation at MCS level
- The r-relation properties (R(A,B,C) properties from Task 46)

If the temporal instantiations of A4a/A5a at MCS level are not proved in Task 46, Task 47 must either add them or accept sorry stubs.

---

## 7. Abstraction Notes

### Tier 3 (Defer to Task 41)

Point insertion is explicitly categorized as Tier 3 (copy-modify now, abstract later). The proof is deeply interleaved with formula manipulation and MCS reasoning. Creating an abstract version prematurely would produce fragile typeclass hierarchy.

For Task 41 preparation: use identical structure and names. The two concrete implementations (bimodal and temporal) will serve as the specification for what any abstraction must provide.

### FrameClass Note

Task 47 does NOT use `FrameClass` (unlike bimodal which needs it for the derivation system parameter). The temporal chronicle has a single proof system. This simplification is significant and is where the ~15% non-transfer in ChronicleTypes.lean comes from.

---

## 8. Relevant Codebase Paths

### Source Files (bimodal — adapt from these)
```
Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/
├── ChronicleTypes.lean              (386 lines — primary source for Phase 1)
└── PointInsertion.lean              (3556 lines — primary source for Phase 2)
```

### Prerequisite Files (must exist before Task 47 starts — created in Task 46)
```
Cslib/Logics/Temporal/
├── Metalogic/TemporalContent.lean   (g_content, h_content — from Task 46 Phase 0a)
├── Theorems/Propositional/Core.lean (propositional combinators — from Task 46 Phase 0b)
└── Theorems/TemporalDerived.lean    (temp_k_dist, past_nec etc. — from Task 46 Phase 0c)
```

### Target Files (temporal — create these)
```
Cslib/Logics/Temporal/Metalogic/Chronicle/
├── ChronicleTypes.lean              (new — Phase 1, ~150-250 lines)
└── PointInsertion.lean              (new — Phase 2, ~1200-2000 lines)
```

---

## References

- Burgess 1982, Section 2, Lemmas 2.6-2.8 and chronicle conditions
- Xu 1988, Definition 2.5, Theorem 2.8 (cleaner C0-C6 formulation)
- `specs/050_burgess_prior_art_seed_research/reports/01_team-research.md`
- `specs/050_burgess_prior_art_seed_research/reports/01_teammate-a-findings.md` (full Lemma 2.6-2.8 analysis)
- `specs/050_burgess_prior_art_seed_research/reports/01_teammate-b-findings.md` (per-file transfer rates)
- `specs/050_burgess_prior_art_seed_research/reports/01_teammate-c-findings.md` (risks and gaps)
