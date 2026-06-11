# Research Report: Completeness Theorem Blockers and Task Decomposition

## Executive Summary

Three blockers prevent closing the single `sorry` in `Cslib/Logics/Temporal/Metalogic/Completeness.lean` (line 416). After analyzing the Burgess 1982 completeness proof, the bimodal completeness infrastructure (14,944 lines across 19 files in `BXCanonical/`), and Mathlib's `LinearExtension`, this report concludes that **temporal completeness is a major undertaking that should be expanded into multiple separate tasks**. The bimodal completeness took ~15K lines for a similar (but more complex) logic; the temporal analog will require an estimated 2,000-4,000 lines of new code across several modules.

The recommended approach is the **Burgess/Xu point-insertion method** (the same method formalized in the bimodal Chronicle construction), adapted for the standalone temporal setting. Task 31 should be marked EXPANDED with 4-5 sub-tasks.

---

## 1. Literature Analysis

### 1.1 Burgess 1982: Canonical Construction for Since/Until

**Source**: `/home/benjamin/Projects/BimodalLogic/literature/Burgess_1982_Axioms_for_tense_logic_Since_and_Until.md`

Burgess's completeness proof for the BX axiom system (A1a-A7a plus mirrors) proceeds as follows:

**Step Map**:
1. **R-relation definition** (Lemma 2.3): Define `r(A, beta, C)` iff `U(gamma, beta) in A` for all `gamma in C`. Equivalently, `S(alpha, beta) in C` for all `alpha in A`. This connects pairs of MCS via a "guard" formula beta.
2. **R-maximality** (Lemma 2.3): `R(A, B, C)` means B is maximal DCS such that `r(A, B, C)`. B represents the complete description of what holds throughout the interval [A, C].
3. **Witness existence** (Lemma 2.4): If `U(gamma, beta) in A`, then there exist B, C with `R(A, B, C)`, `gamma in C`, `beta in B`. This is the Until-witness lemma.
4. **Point insertion** (Lemmas 2.6, 2.7): Given a finite frame with counterexamples to conditions C5a (guard interpolation) or C6a (Until witness existence), insert new points to eliminate them while preserving all existing structure.
5. **Omega-step construction** (Theorem 2.8): Start with singleton frame `{t0}` labeled with MCS containing `neg phi`. Enumerate all counterexamples to C5a/C6a/C5b/C6b and iteratively insert points to eliminate them. The union of all stages gives a frame satisfying all conditions.
6. **Truth lemma** (Theorem 2.8): By induction on formula complexity, show `f(t) satisfies beta` iff `beta in f(t)`, where f labels frame points with MCS and g labels edges with DCS guards.

**Key insight**: The construction builds a **finite approximation sequence** of labeled frames, not a chain indexed by Z. Each step inserts a single point to fix one defect. The limit is a countable (possibly infinite) frame.

**Conditions on the limit frame**:
- C1: Irreflexive (no `t < t`)
- C3: `r(f(t), g(t,t'), f(t'))` for all `t < t'` -- MCS are R-related via the guard DCS
- C4: Guard DCS `g(t,t')` is contained in `f(t'')` for all `t'' between t and t'`
- C5a: If `not U(gamma, beta) in f(t)` and `gamma in f(t')`, there exists `t''` between with `not beta in f(t'')`
- C6a: If `U(gamma, beta) in f(t)`, there exists `t'` after t with `gamma in f(t')` and `beta in g(t,t')`

### 1.2 Xu 1988: Extension to Non-Linear Frames

**Source**: `/home/benjamin/Projects/BimodalLogic/literature/Xu_1988_On_some_US_tense_logics.md`

Xu extends Burgess's method to arbitrary (possibly non-linear) frames. The key technical contribution is the same point-insertion technique (Definition 2.5, Lemmas 2.6-2.7), showing it works for the minimal US-tense logic without linearity. For linear orders, axiom A7a (BX7, `linear_until`) is added, matching Burgess's system.

### 1.3 Blackburn/de Rijke/Venema 2002, Section 7.2

**Source**: `/home/benjamin/Projects/BimodalLogic/literature/Blackburn_deRijke_Venema_2002_Modal_Logic_s7.2_since_until.md`

Presents the BX axiom system as system **B** (Definition 7.13) with axioms (A1a)-(A7a) and mirrors. Proves completeness of B via Theorem 7.15 (`Sigma |-_B phi iff Sigma |=_B phi`). The method follows Burgess but the paper focuses on expressive completeness and Stavi connectives rather than detailed canonical model construction.

### 1.4 Reynolds 1992: Without Irreflexivity

**Source**: `/home/benjamin/Projects/BimodalLogic/literature/Reynolds_1992_Axiomatization_Until_Since_without_IRR.md`

Shows how to axiomatize Until/Since without assuming irreflexivity of the underlying relation.

---

## 2. Bimodal Completeness Infrastructure Analysis

The bimodal completeness proof at `Cslib/Logics/Bimodal/Metalogic/BXCanonical/` is 14,944 lines across 19 files. It implements Burgess's method for the bimodal temporal logic (which extends temporal logic with an S5 box modality).

### 2.1 Module Inventory

| Module | Lines | Purpose | Temporal Analog Needed? |
|--------|-------|---------|------------------------|
| **Frame.lean** | 464 | BXPoint, bx_le, G/H forward/backward, modal witness, eventuality resolution | Yes -- CanonicalPoint, temporal ordering, witnesses |
| **TruthLemma.lean** | 223 | MCS truth properties for atom/bot/imp/box/G/H/Until/Since | Yes -- truth lemma (no box case) |
| **CanonicalChain.lean** | 95 | BX12/BX6 at MCS level, delegation bridges | Yes -- axiom-level MCS lemmas |
| **CanonicalModel.lean** | 771 | Z-chain construction, FMCS, box stability | Partially -- Z-chain without box |
| **OrderedSeedConsistency.lean** | 151 | Ordered seed consistency for point insertion | Yes -- same concept |
| **Chronicle/ChronicleTypes.lean** | 386 | Chronicle data types | Yes -- labeled frame types |
| **Chronicle/RRelation.lean** | 1695 | R-relation (Burgess's r(A,B,C)) | Yes -- central to Burgess method |
| **Chronicle/PointInsertion.lean** | 3556 | Insert points to fix C5/C6 defects | Yes -- the core construction |
| **Chronicle/CounterexampleElimination.lean** | 3529 | Enumerate and eliminate all counterexamples | Yes -- omega-step construction |
| **Chronicle/ChronicleConstruction.lean** | 1531 | Build the full chronicle | Yes -- assemble the limit |
| **Chronicle/ChronicleToCountermodelBasic.lean** | 1170 | Extract countermodel from chronicle | Yes -- build TemporalModel |
| **Chronicle/ChronicleToCountermodel.lean** | 229 | Final countermodel assembly | Yes -- close completeness |
| **Completeness/Dense.lean** | 134 | Dense completeness theorem | No -- temporal is just Base |
| **Filtration/DefectChain.lean** | 100 | Defect chain for filtration | Maybe -- depends on approach |
| **Quasimodel/** | 873 | Subformula closure, Hintikka points | No -- bimodal-specific |

### 2.2 What Can Be Directly Reused

The temporal logic shares the same Until/Since/G/H operators as the bimodal logic's temporal fragment. The key differences:

1. **No box modality**: The bimodal logic has an S5 box operator. All box-related machinery (modal witness, box stability, BFMCS families) is unnecessary.
2. **Same axioms**: BX1-BX13 (and mirrors) are identical between bimodal and temporal.
3. **Same R-relation**: The `r(A, beta, C)` relation from Burgess is the foundation of both.
4. **Same point-insertion**: The defect elimination for C5a/C6a is purely temporal.
5. **Simpler model**: Temporal model is just `(D, <, V)` vs bimodal `(D, <, Box, V)`.

**Adaptation strategy**: Fork the Chronicle construction from bimodal, strip out all box/modal components, and adapt to temporal Formula/MCS types.

### 2.3 Estimated Scope

Removing box-related code (~30% of bimodal infrastructure) and bimodal-specific modules (Quasimodel, Dense, Filtration), the temporal completeness needs approximately:

| Component | Bimodal Lines | Temporal Estimate | Notes |
|-----------|--------------|-------------------|-------|
| Frame/Point definitions | 464 | 300 | Simpler without box |
| Truth lemma | 223 | 200 | Same minus box case |
| R-relation | 1695 | 1200 | Same logic, simpler types |
| Point insertion | 3556 | 2500 | Same logic, simpler types |
| Counterexample elimination | 3529 | 2500 | Same logic, simpler types |
| Chronicle construction | 1531 | 1000 | Simpler without dense case |
| Countermodel extraction | 1399 | 800 | Much simpler (just LinearOrder) |
| Chain construction (FMCS) | 771 | 400 | No box stability needed |
| Axiom MCS lemmas | 95 + 151 | 200 | Direct adaptation |
| **Total** | **~13,400** | **~9,100** | |

This is a substantial project. Even with aggressive simplification (e.g., using the Z-chain approach for a simpler countermodel instead of the full Chronicle), the minimum viable completeness proof is estimated at 2,000-4,000 lines.

---

## 3. Blocker Analysis

### Blocker 1: LinearOrder on the Countermodel Domain

**Problem**: The completeness theorem needs a linear order model that falsifies the non-derivable formula.

**Resolution**: Two approaches, both viable:

**Approach A -- Z-Chain (simpler, ~500 lines)**:
Build a chain `chain : Z -> MCS` indexed by integers, following `CanonicalModel.lean`. The linear order is `Int.instLinearOrder`. Requires `[Denumerable (Formula Atom)]`. The bimodal code at lines 250-380 of CanonicalModel.lean provides a complete template.

*Limitation*: The truth lemma for Until/Since on Z is not straightforward because Z is discrete. The guard condition in `U(phi, psi)` is vacuous when the witness is at `n+1` (no integers between n and n+1). The forward truth lemma (`(phi U psi) in chain(n) -> semantic Until on Z`) may fail because the syntactic Until in the MCS encodes strict linear order semantics, not discrete semantics.

**Approach B -- Burgess Point-Insertion (robust, ~3000-4000 lines)**:
Build a countable frame using the Burgess method (as formalized in the bimodal Chronicle). The frame is NOT indexed by Z -- it's a countable set with an irreflexive total order built by the construction itself. The truth lemma holds by construction (conditions C3-C6 ensure it).

*Advantage*: The truth lemma is guaranteed by the construction, avoiding the discrete-order problem of Approach A.
*Cost*: Much more code, but follows an established template.

**Recommendation**: If the Z-chain approach can handle the Until/Since truth lemma (which requires careful analysis), use it. Otherwise, use the Burgess approach.

### Blocker 2: Truth Lemma for Until/Since

**For the Z-chain** (Approach A):

The forward direction (`(phi U psi) in chain(n) -> exists m > n, phi in chain(m) /\ forall k in (n,m), psi in chain(k)`) is delicate on Z because the discrete topology means the guard psi only needs to hold at finitely many intermediate integers.

The key argument uses:
- BX10 (`until_F`): `(phi U psi) -> F(phi)` gives a witness
- BX5 (`self_accum_until`): strengthens the event to carry the Until forward
- BX7 (`linear_until`): ensures Until witnesses are consistently ordered
- Induction on the distance to the witness

**For the Burgess approach** (Approach B):

The truth lemma is built into the construction. Conditions C5a and C6a ensure that:
- C6a: Every `U(gamma, beta)` in `f(t)` has a witness `t'` with `gamma in f(t')` and `beta in g(t,t')`
- C5a: Every `not U(gamma, beta)` in `f(t)` with `gamma in f(t')` has an interpolant `t''` with `not beta in f(t'')`
- C4: Guards are contained in all intermediate MCS

These conditions directly yield the truth lemma for Until. The bimodal formalization at `Chronicle/RRelation.lean` (1695 lines) and `Chronicle/PointInsertion.lean` (3556 lines) implements this.

### Blocker 3: Universe Adjustment

Both approaches resolve this:
- Z-chain: Domain is `Int : Type` (universe 0), matching `h_valid`'s `D : Type`.
- Burgess: Domain is a countable set built from `T* = Nat`, also `Type`.

The `Atom` type needs `[Countable Atom] [Infinite Atom]` for `Denumerable (Formula Atom)`.

---

## 4. Task Decomposition Proposal

Task 31 should be marked **EXPANDED** and broken into the following sub-tasks. Each sub-task references specific literature and bimodal modules.

### Sub-Task A: R-Relation and Witness Infrastructure

**Scope**: Define the Burgess R-relation `r(A, beta, C)` and prove its key properties (Lemma 2.3, 2.4 from Burgess 1982) for temporal MCS.

**Literature**: Burgess 1982 Section 2, Lemmas 2.2-2.4
**Bimodal template**: `Chronicle/RRelation.lean` (1695 lines)
**Temporal estimate**: 800-1200 lines
**Dependencies**: Existing MCS infrastructure in `Metalogic/MCS.lean`

**Deliverables**:
- `r_relation(A, beta, C)` definition
- `R_maximal(A, B, C)` definition
- Lemma: `r(A, beta, C) iff S(alpha, beta) in C for all alpha in A` (Burgess 2.3)
- Until witness lemma: `U(gamma, beta) in A -> exists B, C with R(A,B,C), gamma in C, beta in B` (Burgess 2.4)
- Consistency criterion: `U(gamma, delta) in A -> gamma is consistent` (Burgess 2.2)

### Sub-Task B: Labeled Frame Types and Point Insertion

**Scope**: Define the labeled frame type (Burgess's K-elements) and prove that counterexamples to C5a/C6a can be eliminated by point insertion (Burgess Lemmas 2.6, 2.7).

**Literature**: Burgess 1982 Section 2, Definition 2.5, Lemmas 2.6-2.7; Xu 1988 Section 2
**Bimodal template**: `Chronicle/ChronicleTypes.lean` (386 lines), `Chronicle/PointInsertion.lean` (3556 lines)
**Temporal estimate**: 1500-2500 lines
**Dependencies**: Sub-Task A

**Deliverables**:
- `TemporalChronicle` type: `(T : Finset, lt : T -> T -> Prop, f : T -> MCS, g : edges -> DCS)`
- Conditions C1-C4 as structure fields or predicates
- Point insertion for C5a defects (Burgess Lemma 2.6)
- Point insertion for C6a defects (Burgess Lemma 2.7)
- Mirror versions for C5b/C6b

### Sub-Task C: Counterexample Elimination and Chronicle Construction

**Scope**: Build the omega-step construction that enumerates all defects and iteratively inserts points (Burgess Theorem 2.8, construction part).

**Literature**: Burgess 1982 Theorem 2.8; Xu 1988 Theorem 2.8
**Bimodal template**: `Chronicle/CounterexampleElimination.lean` (3529 lines), `Chronicle/ChronicleConstruction.lean` (1531 lines)
**Temporal estimate**: 1500-2500 lines
**Dependencies**: Sub-Task B

**Deliverables**:
- Defect enumeration strategy
- Single-step extension (fix one defect)
- Omega-chain construction (union of all stages)
- Proof that limit satisfies C1-C6

### Sub-Task D: Truth Lemma and Completeness Assembly

**Scope**: Prove the truth lemma on the constructed frame and close the completeness theorem.

**Literature**: Burgess 1982 Theorem 2.8 (truth lemma part); Blackburn et al. 2002 Theorem 7.15
**Bimodal template**: `TruthLemma.lean` (223 lines), `Chronicle/ChronicleToCountermodel*.lean` (1399 lines), `Completeness/Dense.lean` (134 lines)
**Temporal estimate**: 500-1000 lines
**Dependencies**: Sub-Task C

**Deliverables**:
- Truth lemma by induction on formula complexity (5 cases: atom, bot, imp, untl, snce)
- Extract `TemporalModel` from labeled frame
- Prove the frame is a serial linear order (NoMaxOrder, NoMinOrder, Nontrivial)
- Close `completeness` theorem (contrapositive + truth lemma + model extraction)

### Alternative: Simplified Z-Chain Approach

If the full Burgess construction is deemed too large, a smaller but riskier alternative:

### Sub-Task A': Z-Chain Infrastructure

**Scope**: Build Z-indexed chain of MCS with schedule-based defect resolution.
**Bimodal template**: `CanonicalModel.lean` lines 183-380
**Temporal estimate**: 200-300 lines
**Dependencies**: Existing `exists_future_successor` / `exists_past_predecessor`

### Sub-Task B': Until/Since Truth Lemma on Z

**Scope**: Prove the truth lemma for Until/Since on the discrete Z-chain.
**Risk**: HIGH -- the discrete topology creates complications for the guard condition.
**Temporal estimate**: 300-500 lines (if it works)

### Sub-Task C': Close Completeness

**Scope**: Assemble model and close sorry.
**Temporal estimate**: 50-100 lines

---

## 5. Recommendations

1. **Expand task 31**: The completeness theorem is too large for a single task phase. Mark EXPANDED and create sub-tasks.

2. **Choose approach early**: The Burgess point-insertion method (Sub-Tasks A-D) is the established approach with a complete bimodal template. The Z-chain approach (Sub-Tasks A'-C') is faster but carries risk on the Until/Since truth lemma.

3. **Research each sub-task**: Each sub-task should begin with focused research on the specific literature sections and bimodal modules listed, then implement following the template.

4. **Dependencies**: Sub-tasks are sequential (A -> B -> C -> D). No parallelism is possible since each builds on the previous.

5. **Estimated total**: 4,000-7,000 lines for Burgess approach; 550-900 lines for Z-chain approach.

---

## References

### Literature
- Burgess 1982: `/home/benjamin/Projects/BimodalLogic/literature/Burgess_1982_Axioms_for_tense_logic_Since_and_Until.md`
- Xu 1988: `/home/benjamin/Projects/BimodalLogic/literature/Xu_1988_On_some_US_tense_logics.md`
- Blackburn/de Rijke/Venema 2002 s7.2: `/home/benjamin/Projects/BimodalLogic/literature/Blackburn_deRijke_Venema_2002_Modal_Logic_s7.2_since_until.md`
- Reynolds 1992: `/home/benjamin/Projects/BimodalLogic/literature/Reynolds_1992_Axiomatization_Until_Since_without_IRR.md`

### Bimodal Codebase
- Frame & ordering: `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Frame.lean`
- Truth lemma: `Cslib/Logics/Bimodal/Metalogic/BXCanonical/TruthLemma.lean`
- Z-chain construction: `Cslib/Logics/Bimodal/Metalogic/BXCanonical/CanonicalModel.lean`
- R-relation: `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/RRelation.lean`
- Point insertion: `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/PointInsertion.lean`
- Counterexample elimination: `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/CounterexampleElimination.lean`
- Chronicle types: `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleTypes.lean`

### Current Temporal Codebase
- Completeness (with sorry): `Cslib/Logics/Temporal/Metalogic/Completeness.lean`
- MCS infrastructure: `Cslib/Logics/Temporal/Metalogic/MCS.lean`
- Axioms: `Cslib/Logics/Temporal/ProofSystem/Axioms.lean`
- Semantics: `Cslib/Logics/Temporal/Semantics/Satisfies.lean`
