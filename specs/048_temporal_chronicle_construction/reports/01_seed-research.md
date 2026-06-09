# Seed Research Report: Task 48 — Temporal Counterexample Elimination and Chronicle Construction

**Task**: 48 — Temporal counterexample elimination and chronicle construction
**Date**: 2026-06-09
**Source**: Task 50 team research (teammates A, B, C, D)
**Purpose**: Pre-digested research to allow task 48 to skip or accelerate its research phase

---

## Overview

Task 48 ports the counterexample elimination and omega-chain chronicle construction from the bimodal `BXCanonical/Chronicle/` to a new temporal-only module. These two files (`CounterexampleElimination.lean`, `ChronicleConstruction.lean`) have the highest transfer rate of any Chronicle file — both are ~95% purely temporal with zero box/modal references. The main work is mechanical: import path rewrite, remove FrameClass parameter, use temporal formula type.

The key mathematical content is Burgess Lemmas 2.9-2.10 (counterexample elimination by induction) and the omega-step construction (start with a single MCS, enumerate all defects, iteratively apply point insertion from Task 47, take the union).

**Critical prerequisite**: The `[Denumerable (Formula Atom)]` instance is required for the omega-chain enumeration. Verify this instance exists for `Temporal.Formula Atom` before starting.

---

## 1. Literature Map: Burgess 1982, Lemmas 2.9-2.10 and the Omega Construction

### Lemma 2.9 — Counterexample Elimination for C4a (¬U-defects)

**Setting**: A chronicle (f,g) ∈ ℱ and a C4a counterexample: ¬U(γ,δ) ∈ f(x) and γ ∈ f(y) with x < y, but there is no z with x < z < y and ¬δ ∈ f(z).

**Claim**: ∃ an extension (f',g') where this counterexample is eliminated (while no new C4a/C5a counterexamples are introduced at already-covered points).

**Proof by induction** on n = |{z ∈ dom f : x < z < y}|:

- **Base n=0**: By C2', R(f(x), g(x,y), f(y)). Apply Lemma 2.6 (point insertion for ¬δ) to get B', D, B''. Set z = (x+y)/2, f'(z) = D, g'(x,z) = B', g'(z,y) = B'', and C3 determines g'(x,y).
- **Inductive step n=m+1**: Let x' be the immediate successor of x in dom f.
  - If ¬U(γ,δ) ∈ f(x'): Reduce to case n=m by replacing x with x'.
  - If U(γ,δ) ∈ f(x'): Must have δ ∈ f(x') (from C5a applied to x'); let γ' = δ∧U(γ,δ), reduce to n=0 case.

**Lean target**: `eliminate_C4a_counterexample : C4aCounterexample ch → ∃ ch', Extends ch ch' ∧ ¬C4aCounterexample_at ch' (same x, y, γ, δ)`

### Lemma 2.10 — Counterexample Elimination for C5a (U-witness defects)

**Setting**: A chronicle (f,g) ∈ ℱ and a C5a counterexample: U(ξ,η) ∈ f(x) but there is no y > x with ξ ∈ f(y) and η ∈ g(x,y).

**Claim**: ∃ an extension (f',g') eliminating this counterexample.

**Proof by induction** on n = |{z ∈ dom f : z > x}|:

- **Base n=0**: Apply Lemma 2.4 (witness existence from Task 46) to A=f(x). Get B,C with R(A,B,C) and ξ ∈ C, η ∈ B. Set y = x+1, f'(y) = C, g'(x,y) = B.
- **Inductive step n=m+1**: Let x' immediately succeed x in dom f.
  - Case (i): η∧U(ξ,η) ∈ f(x') and η ∈ g(x,x') — reduce to n=m (the witness is now further out but still exists).
  - Case (ii): ξ ∈ f(x') and η ∈ g(x,x') — impossible (would not be a counterexample).
  - Otherwise: hypotheses of Lemma 2.7 or 2.8 hold — apply point insertion between x and x'.

**Lean target**: `eliminate_C5a_counterexample : C5aCounterexample ch → ∃ ch', Extends ch ch' ∧ ¬C5aCounterexample_at ch' (same x, ξ, η)`

### The Omega Construction

The full chronicle is assembled by iterating the single-step elimination:

1. **Start**: Let A₀ be an MCS containing the consistent formula φ we want to satisfy. Define (f₀, g₀) with dom f₀ = {0} and f₀(0) = A₀.
2. **Enumerate**: List all potential counterexamples to C4a, C4b, C5a, C5b using a Denumerable enumeration of formula pairs and domain element pairs.
3. **Iterate**: At stage n, if the n-th potential counterexample is actual in (fₙ, gₙ), apply the appropriate elimination lemma to get (fₙ₊₁, gₙ₊₁). Otherwise, set (fₙ₊₁, gₙ₊₁) = (fₙ, gₙ).
4. **Take Union**: X = ⋃ dom fₙ, f = ⋃ fₙ, g = ⋃ gₙ.
5. **Verify**: The union chronicle (X, <, f, g) satisfies all conditions C0-C5 and their mirror images.

**Key property**: The union is well-defined because each (fₙ₊₁, gₙ₊₁) extends (fₙ, gₙ) — the domain only grows, and f/g values agree on the domain of fₙ.

### Mirror Images

Each C4a/C5a lemma has a mirror image for Since (C4b/C5b). The bimodal code also handles box-witness defects (C5b/C6b in bimodal notation for modal witnesses) — these are **entirely absent** in the temporal version.

---

## 2. Infrastructure Audit: Per-File Transfer Analysis

### Chronicle/CounterexampleElimination.lean (3529 lines) → ~95% transfer rate

**What transfers directly**:
- `C5Counterexample` and `C5'Counterexample` structures (chronicle + counterexample data)
- `eliminate_C5_counterexample` (C5a/C4a elimination with induction)
- `eliminate_C5'_counterexample` (mirror for Since)
- `PotentialCounterexample` sum type (all counterexample types)
- Uniform elimination interface: given any potential counterexample, produce an extended chronicle
- All proof content uses only temporal operators (U, S, F, P, G, H)

**What does NOT transfer**: NONE in proof content.

**Mechanical changes only**:
1. Import path rewrite: `Cslib.Logics.Bimodal.X` → `Cslib.Logics.Temporal.X`
2. Remove `FrameClass` parameter everywhere
3. Swap formula type references

**Abstraction potential**: HIGH — the counterexample structures and elimination procedures are entirely logic-agnostic once the chronicle types are parameterized.

### Chronicle/ChronicleConstruction.lean (1531 lines) → ~95% transfer rate

**What transfers directly**:
- `singleton_chronicle`: Creates the initial single-point chronicle from an MCS
- `omega_chain`: The n-th stage of the construction
- `limit_chronicle`: The directed union
- `limit_satisfies_c0` through `limit_satisfies_c5`: Proofs that the limit satisfies all conditions
- `NoMinOrder` and `NoMaxOrder` instances for the limit domain (the chronicle grows unboundedly in both directions)

**The Denumerable requirement** (see Section 3): `ChronicleConstruction.lean` uses `[Denumerable (Formula Atom)]` to enumerate all formulas for the defect enumeration. This must exist for `Temporal.Formula Atom`.

**What does NOT transfer**: NONE in proof content.

**Mechanical changes only**: Import path rewrite, FrameClass removal.

**Abstraction potential**: HIGH — the omega-chain construction is completely logic-agnostic.

---

## 3. Critical Prerequisite: [Denumerable (Formula Atom)]

### Why It's Needed

The omega-chain construction enumerates defects using a `Denumerable` instance to get a surjective sequence of all potential counterexamples. `Denumerable α` requires `α` to be countably infinite with a computable encoding.

### Status for Temporal Formula

The bimodal `Formula Atom` has this instance (established in an earlier task). Check whether the temporal `Formula Atom` has it:

```bash
grep -r "Denumerable.*Formula" Cslib/Logics/Temporal/ --include="*.lean"
```

If not found, the temporal `Formula Atom` Denumerable instance must be created before Task 48 can be completed. This is likely a 20-50 line addition. It's almost certainly derivable from `Denumerable Atom` (using standard Lean mathlib encodings for inductive types).

### Reference

The bimodal version is likely in `Cslib/Logics/Bimodal/Formula.lean` or nearby. Check:

```bash
grep -r "Denumerable.*Formula" Cslib/Logics/Bimodal/ --include="*.lean"
```

---

## 4. Verification of Bimodal Sorry Stubs

The bimodal `RRelation.lean` and `PointInsertion.lean` have sorry stubs for "open guard semantics (Task 113 upstream)". Check whether these sorry stubs appear in `CounterexampleElimination.lean` or `ChronicleConstruction.lean`:

```bash
grep -n "sorry" Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/CounterexampleElimination.lean
grep -n "sorry" Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleConstruction.lean
```

Given that these files have zero box/modal references, it is likely the sorry stubs (if any) are either:
- In non-critical branches (open guard being a bimodal-specific concept)
- Entirely absent from these files

If sorrys exist in CounterexampleElimination.lean, evaluate whether the open guard concept is relevant to temporal (it likely isn't).

---

## 5. Key Simplifications vs Bimodal

### Fewer Defect Types

The bimodal omega construction enumerates defects of type:
- C4a counterexample (¬U, temporal)
- C4b counterexample (¬S, temporal)
- C5a counterexample (U-witness, temporal)
- C5b counterexample (S-witness, temporal)
- C5b-modal counterexample (□-witness, BIMODAL-ONLY)
- C6b-modal counterexample (◇-witness, BIMODAL-ONLY)

The temporal construction enumerates only C4a, C4b, C5a, C5b — the modal defect types are absent entirely.

**Impact**: The `PotentialCounterexample` sum type has 4 cases instead of 6 (or however many the bimodal has). The omega enumeration is correspondingly simpler.

### No Modal Accessibility Construction

The bimodal `ChronicleConstruction.lean` also handles propagation of modal accessibility (`bx_modal_equiv` equivalence classes) through the limit. This is entirely absent from the temporal version. The temporal limit is just a linear order with f and g functions.

---

## 6. Naming Conventions

Following Teammate D's recommendation:

| Bimodal Name | Temporal Name | Notes |
|---|---|---|
| `C5Counterexample` | `C5Counterexample` | Keep identical (avoid archaeology in Task 41) |
| `C5'Counterexample` | `C5'Counterexample` | Keep identical |
| `eliminate_C5_counterexample` | `eliminate_C5_counterexample` | Keep identical |
| `PotentialCounterexample` | `PotentialCounterexample` | Keep identical |
| `singleton_chronicle` | `singleton_chronicle` | Keep identical |
| `omega_chain` | `omega_chain` | Keep identical |
| `limit_chronicle` | `limit_chronicle` | Keep identical |
| `chronicle_defect` | `chronicle_defect` | Keep identical |

---

## 7. Implementation Strategy

### Recommended Phase Sequence for Task 48

1. **Phase 1**: Verify/create `[Denumerable (Formula Atom)]` instance for temporal formula.
2. **Phase 2**: Create `Chronicle/CounterexampleElimination.lean` (~1,200-2,000 lines)
   - Port `C5Counterexample`, `C5'Counterexample` structure definitions
   - Port elimination functions (induction proofs calling Task 47 point insertion)
   - Port `PotentialCounterexample` sum type and uniform elimination
3. **Phase 3**: Create `Chronicle/ChronicleConstruction.lean` (~600-900 lines)
   - Port `singleton_chronicle`
   - Port `omega_chain` (uses Denumerable enumeration)
   - Port `limit_chronicle` and the limit satisfaction proofs

### Incremental Approach

Task 48 depends on all of Task 46 (r-relation + prerequisites) and Task 47 (chronicle types + point insertion). Ensure those tasks compile cleanly before starting.

After completing CounterexampleElimination.lean, run a full lake build to verify the module compiles against Tasks 46 and 47 before proceeding to ChronicleConstruction.lean.

---

## 8. Risks and Warnings

### Risk 1: [Denumerable (Formula Atom)] Instance Missing

If this instance does not exist for temporal formulas, it must be created. This is likely straightforward but could block progress if overlooked. **Check first before starting any other work in Task 48.**

### Risk 2: Sorry Stubs in Bimodal Source

If the bimodal `CounterexampleElimination.lean` contains sorry stubs related to open guard semantics, evaluate whether to:
- (a) Create temporal versions without the sorry (if the open guard issue doesn't apply to temporal)
- (b) Accept the sorry and add a corresponding comment (if the issue also affects temporal)

The temporal logic likely doesn't have "open guard semantics" — this is a bimodal concern. Option (a) is strongly preferred.

### Risk 3: Enumeration Completeness

The omega construction must enumerate ALL potential counterexamples, including ones that arise from newly inserted points. The bimodal implementation handles this with a careful two-step: enumerate all positions, then at each position all formulas. Verify the enumeration strategy from `ChronicleConstruction.lean` handles this correctly before porting.

### Risk 4: Directed Limit Well-Definedness

The proof that `limit_chronicle` is well-defined (f and g values agree on the overlap of domains at different stages) relies on the `Extends` predicate being a partial order. Verify the bimodal formulation and carry it over without change.

---

## 9. Abstraction Notes

Both CounterexampleElimination.lean and ChronicleConstruction.lean are labeled as HIGH abstraction candidates by Teammate B. They are "completely logic-agnostic" in structure. However:

- **Task 41 defers abstraction**: These files are Tier 2 (design now, implement in Task 41).
- **For Task 48**: Use identical names and identical structure. The two concrete implementations serve as the specification.
- **FrameClass removal**: Unlike Tasks 46-47, these files don't even have a FrameClass concept — the temporal versions should be even cleaner.

---

## 10. Relevant Codebase Paths

### Source Files (bimodal — adapt from these)
```
Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/
├── CounterexampleElimination.lean   (3529 lines — primary source, Phase 2)
└── ChronicleConstruction.lean       (1531 lines — primary source, Phase 3)
```

### Prerequisite Files (must exist before Task 48 starts)
```
Cslib/Logics/Temporal/Metalogic/Chronicle/
├── ChronicleTypes.lean              (from Task 47)
├── PointInsertion.lean              (from Task 47)
├── Frame.lean                       (from Task 46)
├── RRelation.lean                   (from Task 46)
├── CanonicalChain.lean              (from Task 46)
└── OrderedSeedConsistency.lean      (from Task 46)
```

### Target Files (temporal — create these)
```
Cslib/Logics/Temporal/Metalogic/Chronicle/
├── CounterexampleElimination.lean   (new — Phase 2, ~1200-2000 lines)
└── ChronicleConstruction.lean       (new — Phase 3, ~600-900 lines)
```

---

## References

- Burgess 1982, Section 2, Lemmas 2.9-2.10 and the omega construction
- Xu 1988, Theorem 2.8 (stage-by-stage construction over abstract T*)
- `specs/050_burgess_prior_art_seed_research/reports/01_team-research.md`
- `specs/050_burgess_prior_art_seed_research/reports/01_teammate-a-findings.md` (Lemmas 2.9-2.10 analysis)
- `specs/050_burgess_prior_art_seed_research/reports/01_teammate-b-findings.md` (per-file transfer rates)
- `specs/050_burgess_prior_art_seed_research/reports/01_teammate-c-findings.md` (Denumerable requirement, sorry stubs)
