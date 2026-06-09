# Teammate A Findings: Burgess Literature Analysis for Tasks 46-49

**Task**: 50 — Burgess prior art and seed research
**Date**: 2026-06-09
**Focus**: Primary literature analysis mapping Burgess 1982 content to sub-tasks
**Confidence**: High (all primary sources fully read)

---

## Key Findings

1. **Burgess 1982 is self-contained and complete**: The entire completeness proof for S,U-tense logic over arbitrary linear orders fits in Section 2 (Lemmas 2.1-2.11), roughly 5 pages. The proof strategy is a stepwise chronicle construction on rational numbers.

2. **The temporal-only case is strictly simpler than bimodal**: Burgess 1982 has no box modality. The axiom set J₀ has 7 axiom pairs (A1a-A7a plus mirror images) and temporal generalization. The bimodal BX case adds BX axioms for □ interaction. This means every bimodal BXCanonical proof has □-related cases that can be deleted for the temporal adaptation.

3. **Xu 1988 generalizes to non-linear frames**: Xu's construction uses an abstract set T* (not rationals) and a weaker C1 condition (just antisymmetry, no linearity). For cslib's temporal case (linear orders), this means the Burgess original is the tighter reference, but Xu's formulation (C0-C6) is cleaner for Lean formalization since it separates frame conditions more explicitly.

4. **BdRV Theorem 7.15 is exactly the base completeness result**: BdRV's axiom system **B** = Burgess's J₀. Theorem 7.15 states B is complete for all linear flows of time. The BdRV text then uses this as a building block for well-ordering completeness (BW, BN), which is out of scope for tasks 46-49.

5. **The chronicle construction has 4 distinct layers**: (i) R-relation and witness lemmas (2.2-2.4, 2.5-2.8), (ii) chronicle type definition (C0-C5 conditions), (iii) counterexample elimination (Lemmas 2.9-2.10), (iv) truth lemma (Claim 2.11). These map cleanly to tasks 46, 47, 48, 49.

---

## Task 46 Literature Map: R-relation and Witness Infrastructure (Burgess 2.2-2.4)

### Mathematical Definitions

**Consistency Criterion (Lemma 2.2)**: If A is an MCS and U(γ,δ) ∈ A, then γ is consistent.
- Proof uses: TG (temporal generalization), Replacement Lemma 2.1, axiom A2a.
- Mirror image: If A is MCS and S(γ,δ) ∈ A, then γ is consistent.

**The r-relation (Lemma 2.3)**: For MCSs A, C and formula β, define r(A, β, C) as:
- (a) ∀γ ∈ C: U(γ, β) ∈ A  ⟺  (b) ∀α ∈ A: S(α, β) ∈ C
- Proof of (a)⟹(b): Assume (a), suppose α ∈ A with ¬S(α,β) ∈ C. By (a), U(¬S(α,β), β) ∈ A. By A3a, U(¬S(α,β) ∧ S(α,β), β) ∈ A, contradicting 2.2.

**Extensions of r**:
- r(A, B, C): B is a DCS and r(A, β, C) holds for all β ∈ B
- R(A, B, C): B is maximal w.r.t. the property r(A, —, C)
- Key property of R: if R(A,B,C) and δ ∉ B, then ∃β ∈ B, γ ∈ C: U(γ, β∧δ) ∉ A

**Witness Existence (Lemma 2.4)**: If A is MCS and U(γ,β) ∈ A, then ∃B,C with β ∈ B, γ ∈ C, and R(A,B,C).
- Proof constructs C₀ = {γ} ∪ {S(α,β) : α ∈ A}, shows consistency using A3a and 2.2
- Then extends C₀ to MCS C, and takes B maximal with β ∈ B and r(A,B,C)

**Intersection Lemma (Lemma 2.5)**: If R(A,B,C), r(A,B',D), r(D,B'',C) and B ⊆ B' ∩ D ∩ B'', then B = B' ∩ D ∩ B''.
- Uses A6a for the key step: U(δ∧U(γ,δ), δ) ∈ A implies U(γ,δ) ∈ A

### Axioms Involved
- A1a, A2a (monotonicity of U in both arguments)
- A3a (interaction of U and S — the "bridging" axiom)
- A5a (U is self-reinforcing: U(p,q) → U(p, q∧U(p,q)))
- A6a (transitivity: U(q∧U(p,q), q) → U(p,q))
- TG (temporal generalization)

### Differences from Bimodal Case
- **No □-cases**: Burgess has no box modality, so the bimodal RRelation.lean's handling of □-witnesses (BX12/BX6 axioms) is entirely absent.
- **Simpler MCS**: Temporal MCS only need closure under S,U axioms, not the additional BX modal axioms.
- **OrderedSeedConsistency**: In bimodal, this handles ordered seeds for both temporal and modal eventualities. For temporal-only, only temporal seeds (U/S witnesses) are needed.

### Confidence: HIGH

---

## Task 47 Literature Map: Labeled Frame Types and Point Insertion (Burgess 2.5-2.8)

### Mathematical Definitions

**Point Insertion for ¬δ (Lemma 2.6)**: Given R(A,B,C) and δ ∉ B:
- ∃B', D, B'' with ¬δ ∈ D and R(A,B',D), R(D,B'',C), B = B' ∩ D ∩ B''
- Proof constructs D₀ = {S(α,β) : α∈A, β∈B} ∪ B ∪ {¬δ} ∪ {U(γ,β) : γ∈C, β∈B}
- Shows consistency of D₀ using A4a and A5a crucially
- Key: uses the fact that δ ∉ B to find β₀ ∈ B, γ₀ ∈ C with ¬U(γ₀, β₀∧δ) ∈ A

**Point Insertion for U-witness (Lemma 2.7)**: Given R(A,B,C), U(ξ,η) ∈ A, η ∉ B:
- ∃B', D, B'' with η ∈ B', ξ ∈ D, R(A,B',D), R(D,B'',C), B = B' ∩ D ∩ B''
- Proof uses A7a (linearity axiom) crucially to get three disjuncts, rules out two
- This is the most technically demanding lemma — bimodal PointInsertion.lean is 3556 lines

**Point Insertion variant (Lemma 2.8)**: Given R(A,B,C), U(ξ,η) ∈ A, ¬(ξ ∨ (η∧U(ξ,η))) ∈ C:
- Same conclusion as 2.7
- Slight modification of 2.7's proof using the additional hypothesis about C

**Chronicle Conditions (from the text following 2.8)**:
- **(C0)**: f maps a finite subset of Q to MCSs
- **(C0')**: dom f is finite
- **(C1)**: g maps pairs (x,y) with x < y in dom f to DCSs
- **(C2)**: r(f(x), g(x,y), f(y)) for x < y
- **(C2')**: R(f(x), g(x,y), f(y)) for consecutive x,y
- **(C3)**: g(x,z) = g(x,y) ∩ f(y) ∩ g(y,z) for x < y < z
- **(C4a)**: If ¬U(γ,δ) ∈ f(x) and γ ∈ f(y) with x < y, then ∃z with x < z < y and ¬δ ∈ f(z)
- **(C5a)**: If U(ξ,η) ∈ f(x), then ∃y > x with ξ ∈ f(y) and η ∈ g(x,y)
- Plus mirror images C4b, C5b

**Xu's Formulation (Definition 2.5)**: Uses abstract T* instead of Q, conditions C0-C6:
- C5a ≡ Burgess C4a (counterexample to ¬U)
- C6a ≡ Burgess C5a (witness for U)
- C4 adds: g(t,t') ⊆ f(t'') for t < t'' < t' (interval content inclusion)
- Note: Xu drops linearity (C1 only requires antisymmetry), but for our purposes linearity holds

### Key Proof Strategy
The point insertion lemmas (2.6-2.8) are the heart of the construction. Each inserts a single new point between two existing points (or after all existing points), maintaining all chronicle conditions. The proof of consistency of the constructed set D₀ is where the axioms A4a-A7a do their heavy lifting.

### Differences from Bimodal
- **No C5b/C6b for □**: Bimodal has additional conditions for box-witness elimination. Temporal only has C4a/C5a and their S-mirror images.
- **Simpler point insertion**: Each insertion in Burgess handles one defect type. Bimodal PointInsertion.lean handles both temporal and modal defects in interleaved fashion.
- **ChronicleTypes simplification**: The bimodal Chronicle type includes fields for modal accessibility. Temporal Chronicle only needs the linear order and the g function.

### Confidence: HIGH

---

## Task 48 Literature Map: Counterexample Elimination and Chronicle Construction (Burgess 2.8)

### Mathematical Content

**Counterexample Lemma for C4a (Burgess 2.9)**:
Given (f,g) ∈ ℱ and a counterexample x,y,γ,δ to C4a, there exists an extension (f',g') where this is no longer a counterexample.

Proof by induction on n = |{z ∈ dom f : x < z < y}|:
- **Base n=0**: By C2', R(f(x), g(x,y), f(y)). Apply Lemma 2.6 to get B', D, B''. Set z = (x+y)/2, f'(z) = D, g'(x,z) = B', g'(z,y) = B'', and C3 determines other values.
- **Step n=m+1**: Let x' be the immediate successor of x in dom f.
  - If ¬U(γ,δ) ∈ f(x'): reduce to case n=m by replacing x with x'
  - If U(γ,δ) ∈ f(x'): must have δ ∈ f(x'), let γ' = δ∧U(γ,δ), reduce to n=0 case

**Counterexample Lemma for C5a (Burgess 2.10)**:
Given (f,g) ∈ ℱ and a counterexample x,ξ,η to C5a, there exists an extension (f',g') eliminating it.

Proof by induction on n = |{z ∈ dom f : z > x}|:
- **Base n=0**: Apply Lemma 2.4 to A=f(x). Set y = x+1, f'(y) = C, g'(x,y) = B.
- **Step n=m+1**: Let x' immediately succeed x.
  - Case (i): η∧U(ξ,η) ∈ f(x') and η ∈ g(x,x') — reduce to n=m
  - Case (ii): ξ ∈ f(x') and η ∈ g(x,x') — impossible (would not be counterexample)
  - Otherwise: hypotheses of 2.7 or 2.8 hold — insert point between x and x'

**The omega construction**:
1. Start with (f₀, g₀): dom f₀ = {0}, f₀(0) = A₀ (MCS containing the consistent formula)
2. Enumerate all counterexamples to C4a, C4b, C5a, C5b
3. Repeatedly apply 2.9, 2.10 and their mirror images
4. Take X = ⋃ dom fₙ, f = ⋃ fₙ, g = ⋃ gₙ
5. Result satisfies C0-C5 (and mirror images)

### Xu's Version
Xu 1988 Theorem 2.8 follows the same structure but:
- Works over T* (abstract countable set) instead of Q
- Conditions C5a/C6a (Xu's numbering) replace Burgess's C4a/C5a
- The construction is more explicitly stage-by-stage

### Key Implementation Considerations
- **Enumeration of defects**: Must enumerate all potential (x, formula) counterexamples. In bimodal CounterexampleElimination.lean (3529 lines), this uses a careful staging mechanism.
- **Finiteness at each stage**: Each stage adds finitely many points, but the enumeration must cover all defects that arise at new points too.
- **Directed limit**: The union ⋃ fₙ is well-defined because each fₙ extends fₙ₋₁.

### Differences from Bimodal
- **No modal defects**: Bimodal has additional defect types for □-witnesses. Temporal only handles U/S defects.
- **Simpler enumeration**: With fewer defect types, the enumeration is more straightforward.
- **ChronicleConstruction simplification**: Bimodal assembly handles modal accessibility in the limit. Temporal only has the linear order and g-function.

### Confidence: HIGH

---

## Task 49 Literature Map: Truth Lemma and Completeness Assembly (Burgess 2.8/2.11)

### Mathematical Content

**Truth Lemma (Burgess Claim 2.11)**: For the chronicle (X, <, f, g) with valuation V defined by:
```
x ∈ V(α) iff α ∈ f(x)    (for atoms α = pᵢ)
```
this equivalence holds for ALL formulas α.

**Proof by induction on complexity**:
- **Atoms**: by definition
- **Negation**: by MCS property (α ∈ f(x) iff ¬α ∉ f(x))
- **Conjunction**: by MCS closure under ∧
- **U(β,γ)**: The critical case.
  - If U(β,γ) ∈ f(x): By C5a, ∃y > x with γ ∈ f(y) and β ∈ g(x,y). For any z with x < z < y, by C3, g(x,y) ⊆ f(z), so β ∈ f(z). By IH, y ∈ V(γ) and z ∈ V(β), giving x ∈ V(U(β,γ)).
  - If ¬U(β,γ) ∈ f(x): For any y > x with γ ∈ f(y) (IH: y ∈ V(γ)), by C4a ∃z with x < z < y and ¬β ∈ f(z) (IH: z ∉ V(β)). So x ∉ V(U(β,γ)).
- **S(β,γ)**: Mirror image of U case.

**Completeness conclusion**: Since α₀ ∈ f(0) = A₀, the truth lemma gives 0 ∈ V(α₀), so α₀ is satisfiable.

### BdRV Approach (Theorem 7.15)
BdRV states the completeness of **B** for linear flows directly as Theorem 7.15, crediting Burgess. The proof is exactly the Burgess construction. BdRV then uses 7.15 as a lemma for well-ordering completeness (Theorem 7.19), which goes beyond our scope.

### Key Implementation Considerations
- **The truth lemma is relatively short**: Burgess's Claim 2.11 proof is ~20 lines. Bimodal TruthLemma.lean is 223 lines.
- **Countermodel extraction**: The chronicle frame (X, <) with valuation V IS the countermodel. No separate extraction step is needed (unlike bimodal which must handle modal accessibility).
- **Closing the sorry**: The Temporal/Metalogic/Completeness.lean file presumably has a sorry for the completeness theorem. Task 49 fills this by combining the chronicle construction with the truth lemma.

### Differences from Bimodal
- **No box case in truth lemma**: Bimodal truth lemma must handle □φ: "□φ ∈ f(x) iff for all y accessible from x, φ ∈ f(y)". Temporal has no □.
- **Simpler countermodel**: No modal accessibility relation to construct. The countermodel is just (X, <, V).
- **ChronicleToCountermodel simplification**: Bimodal needs ChronicleToCountermodelBasic (1170 lines) + ChronicleToCountermodel (229 lines) to extract a model with both temporal order and modal accessibility. Temporal only needs the linear order.
- **CanonicalModel not needed**: Bimodal CanonicalModel.lean (771 lines) handles Z-chain MCS propagation for G/H truth. For temporal, G/H truth follows directly from the chronicle's C4/C5 conditions.

### Confidence: HIGH

---

## Cross-Cutting Observations

### Axiom Correspondence
| Burgess J₀ | BdRV **B** | Role in Proof |
|---|---|---|
| A1a | (A1a) | U monotone in first arg |
| A2a | (A2a) | U monotone in second arg |
| A3a | (A3a) | Bridge U↔S (key for r-relation) |
| A4a | (A4a) | Connect current to future witness |
| A5a | (A5a) | U self-reinforcing |
| A6a | (A6a) | Transitivity of temporal order |
| A7a | (A7a) | Linearity (three-way disjunction) |
| Mirror images | (Aib) | Dual properties for S |
| TG | (TG) | Temporal generalization rule |

### Simplification Estimate (Temporal vs Bimodal)
| Component | Bimodal Lines | Temporal Estimate | Reduction |
|---|---|---|---|
| RRelation | 1695 | 600-900 | ~50% |
| Frame | 464 | 200-300 | ~50% |
| CanonicalChain | 95 | 50-70 | ~30% |
| OrderedSeedConsistency | 151 | 80-100 | ~40% |
| ChronicleTypes | 386 | 150-250 | ~50% |
| PointInsertion | 3556 | 1200-2000 | ~50% |
| CounterexampleElimination | 3529 | 1200-2000 | ~50% |
| ChronicleConstruction | 1531 | 600-900 | ~50% |
| TruthLemma | 223 | 100-150 | ~50% |
| ChronicleToCountermodel | 1399 | 300-500 | ~70% |
| CanonicalModel | 771 | 0 (not needed) | 100% |
| **Total** | **13,800** | **4,480-7,170** | **~55%** |

The ~50% reduction comes primarily from eliminating all □-related cases. The countermodel extraction sees the biggest reduction (~70%) because temporal needs no modal accessibility construction.

### Supplementary Sources Summary
- **Burgess 1984** (Basic Tense Logic): General modal logic survey, not directly relevant to the S,U construction. No additional proof techniques.
- **Venema 2001** (Temporal Logic Survey): Good overview of frame conditions, axiom correspondences, and the Kamp theorem context. No new proof content beyond Burgess 1982.
- **GHR 1994 Ch.9**: Focuses on expressive completeness of temporal connectives (Kamp's theorem context). The truth-table framework is useful background but doesn't add to the completeness proof strategy.
