# Teammate A Findings: Primary Approach — Infrastructure Analysis and Design

**Task**: 99 — Complete modal cube Hilbert proof systems
**Date**: 2026-06-11
**Angle**: Existing infrastructure analysis and optimal design for 10 remaining systems
**Confidence**: High

## Key Findings

### 1. Existing Architecture (What We Have)

The codebase has a clean, layered architecture for modal proof systems:

**Layer 1: Abstract Typeclasses** (`ProofSystem.lean`)
- Individual axiom classes: `HasAxiomK`, `HasAxiomT`, `HasAxiom4`, `HasAxiomB`, `HasAxiom5`, `HasAxiomD` — **all six exist**
- Bundled classes: `ModalHilbert` (K), `ModalTHilbert` (K+T), `ModalDHilbert` (K+D), `ModalS4Hilbert` (K+T+4), `ModalS5Hilbert` (K+T+4+B)
- **Missing bundled classes**: No classes for B-only, 4-only, 5-only, or compound systems like K45, DB, TB, KB5, D4, D5, D45

**Layer 2: Axiom Predicates** (`Instances.lean`)
- Each system has a standalone inductive type: `KAxiom`, `TAxiom`, `DAxiom`, `S4Axiom`, `ModalAxiom` (= S5)
- Every predicate duplicates the 4 propositional axiom constructors (implyK, implyS, efq, peirce) plus K distribution
- **Pattern**: Each system = propositional core + modal K + system-specific modal axioms

**Layer 3: Tag Types** (`ProofSystem.lean`)
- Opaque types: `HilbertK`, `HilbertT`, `HilbertD`, `HilbertS4`, `HilbertS5`
- **Missing**: `HilbertB`, `HilbertFour`, `HilbertFive`, `HilbertK45`, `HilbertD4`, `HilbertD5`, `HilbertD45`, `HilbertDB`, `HilbertTB`, `HilbertKB5`

**Layer 4: Soundness** (`Soundness.lean`, `KSoundness.lean`, etc.)
- **Parameterized theorem** `soundness` takes `h_ax_sound` callback — fully reusable
- Per-system: `k_axiom_sound`, `t_axiom_sound`, `d_axiom_sound`, `s4_axiom_sound`, `axiom_sound` (S5)
- Each just cases on the axiom predicate and proves each constructor valid on the frame class
- **Key insight**: The propositional cases are identical across ALL systems

**Layer 5: Completeness** (`Completeness.lean`, `KCompleteness.lean`, etc.)
- **Parameterized canonical model**: `CanonicalWorld Axioms`, `CanonicalModel Axioms` — fully reusable
- **Parameterized frame property lemmas** (take explicit axiom hypotheses):
  - `canonical_refl` (uses h_T)
  - `canonical_trans` (uses h_4)
  - `canonical_eucl` (uses h_T, h_4, h_B, h_K) — derives Euclideanness from B+T+4
  - `canonical_serial` (uses h_D, h_K, h_efq) — in DCompleteness.lean
  - **Missing**: `canonical_symm` (symmetry from B alone, needed for KB, TB, DB, KB5)
  - **Missing**: `canonical_eucl_direct` (Euclideanness from 5 directly, needed for K45, D5, D45, KB5)
- **Two truth lemma variants**:
  - `truth_lemma` — requires h_T (used by T, S4, S5 completeness)
  - `k_truth_lemma` — no h_T, uses `k_mcs_box_witness` (used by K completeness)
  - `truth_lemma_d` — no h_T, uses `mcs_box_witness_d` with axiom D (used by D completeness)
  - **Pattern**: Systems without axiom T need their own truth lemma variant for the box case

### 2. Critical Observations

**Observation A: Two Types of Truth Lemmas**
The box case of the truth lemma requires showing that the set `{ψ | □ψ ∈ S} ∪ {¬φ}` is consistent (the "Existence Lemma" / "Box Witness"). This uses either:
- Axiom T: via `derive_box_from_inconsistency` (filters out ¬φ, derives □φ ∈ S from box context using T-closure)
- Axiom D: via `derive_box_from_inconsistency_d` (in the "all elements have box versions" case, derives ⊥ ∈ S via D+NEC)
- No T/D: via `k_derive_box_from_inconsistency` (uses EFQ to derive φ from ⊥, then box-lifts)

Systems WITH axiom T: T, S4, S5, TB → can reuse `truth_lemma`
Systems WITH axiom D but not T: D, D4, D5, D45, DB → can reuse `truth_lemma_d`
Systems with NEITHER T nor D: K, B, Four, Five, K45, KB5 → must use `k_truth_lemma`

**Observation B: Canonical Symmetry is Missing**
The existing `canonical_eucl` derives Euclideanness from T+4+B (S5-specific). For systems like KB, TB, DB that need symmetry, we need a direct `canonical_symm` proof from axiom B alone. Per Blackburn Theorem 4.28 clause 2: "it suffices to show that the canonical model for KB is symmetric." The proof uses: if R^C(w,v) and □φ ∈ v, then by B: φ → □◇φ, and since φ ∈ v → □◇φ ∈ v, and R^C(w,v) gives ◇φ ∈ w, thus by Lemma 4.19 (MCS property), ¬□¬φ ∈ w, which means if ψ ∈ v then □ψ ∈ v → ψ ∈ w works via the standard argument.

**Observation C: Direct Euclideanness from Axiom 5**
The existing `canonical_eucl` derives Euclideanness indirectly via T+4+B. For systems with axiom 5 but not T+B (like K45, D5), we need `canonical_eucl_from_five` that proves Euclideanness directly from axiom 5: ◇φ → □◇φ. If R^C(w,v) and R^C(w,u) and □φ ∈ v, then since R^C(w,v) gives ◇φ ∈ w (from a lemma about ¬□¬φ), and then axiom 5 gives □◇φ ∈ w, so R^C(w,u) gives ◇φ ∈ u, i.e., ¬□¬φ ∈ u, meaning φ ∈ u. Actually, this needs careful handling — the proof involves `mcs_diamond_box` from axiom 5.

### 3. Design for Each New System

For each system, I specify: axiom predicate, tag type, bundled class, frame conditions, truth lemma variant, new canonical frame properties needed.

| System | Axioms (beyond K) | Frame Conditions | Truth Lemma | New Canonical Properties |
|--------|-------------------|------------------|-------------|-------------------------|
| B (KB) | B | Symmetric | k_truth_lemma | canonical_symm |
| Four (K4) | 4 | Transitive | k_truth_lemma | (canonical_trans exists) |
| Five (K5) | 5 | Euclidean | k_truth_lemma | canonical_eucl_from_five |
| K45 | 4, 5 | Trans + Eucl | k_truth_lemma | canonical_eucl_from_five |
| D4 (KD4) | D, 4 | Serial + Trans | truth_lemma_d | (both exist) |
| D5 (KD5) | D, 5 | Serial + Eucl | truth_lemma_d | canonical_eucl_from_five |
| D45 (KD45) | D, 4, 5 | Ser + Trans + Eucl | truth_lemma_d | canonical_eucl_from_five |
| DB (KDB) | D, B | Serial + Symm | truth_lemma_d | canonical_symm |
| TB (KTB) | T, B | Refl + Symm | truth_lemma | canonical_symm |
| KB5 | B, 5 | Symm + Eucl | k_truth_lemma | canonical_symm, canonical_eucl_from_five |

### 4. New Infrastructure Needed (Shared Lemmas)

**A. `canonical_symm`** — The canonical relation is symmetric when axiom B is present.
- Signature: takes h_implyK, h_implyS, h_B, h_K hypotheses
- Proof sketch (Blackburn Thm 4.28 cl.2): Given R^C(S,T) and □φ ∈ T, show φ ∈ S. By contrapositive: if φ ∉ S then ¬φ ∈ S (MCS); by axiom B on ¬φ: ¬φ → □◇¬φ gives □◇¬φ ∈ S; R^C(S,T) gives ◇¬φ ∈ T; ◇¬φ = ¬□¬(¬φ) = ¬□φ via double negation; but □φ ∈ T, contradiction.
- Used by: B, DB, TB, KB5 (4 systems)

**B. `canonical_eucl_from_five`** — The canonical relation is Euclidean when axiom 5 is present.
- Signature: takes h_implyK, h_implyS, h_efq, h_peirce, h_K, h_5 hypotheses
- Proof sketch: Given R^C(S,T) and R^C(S,U) and □φ ∈ T, show φ ∈ U. We need a helper `mcs_diamond_box_five` that from ◇φ ∈ S derives □◇φ ∈ S using axiom 5. Then: □φ ∈ T, assume φ ∉ U, then ¬φ ∈ U (MCS). Need to show □φ ∈ T → φ ∈ U. This requires showing that if □φ ∉ T we get a successor with ¬φ, but since R^C(S,T) we need a more subtle argument.
- Actually, the standard proof is: R^C(S,T) and R^C(S,U). For □φ ∈ T, need φ ∈ U. Since R^C(S,T), for any ψ, □ψ ∈ S → ψ ∈ T. We need the reverse: from T back to S. The key is that axiom 5 gives: if ◇ψ ∈ S then □◇ψ ∈ S. So for any □φ ∈ T, if we can show ◇φ ∈ S, then □◇φ ∈ S (by 5), so ◇φ ∈ U (by R^C(S,U)). Actually this shows ¬□¬φ ∈ U, not φ ∈ U. The Euclidean proof for canonical models directly is: R^C(S,T) and R^C(S,U), need R^C(T,U). For □φ ∈ T, need φ ∈ U. Assume □φ ∉ S. Then ¬□φ ∈ S. Actually the proof structure may need `mcs_diamond_box_five`: ◇φ ∈ S → □◇φ ∈ S. From □φ ∈ T, by the K distribution property and box-lifting, get □□φ ∈ S if we could... This needs careful work.
- Used by: Five, K45, D5, D45, KB5 (5 systems)

**C. `mcs_diamond_box_five`** — If ◇φ ∈ S then □◇φ ∈ S (using axiom 5).
- Simple MCS modus ponens: ◇φ ∈ S, axiom 5 gives ◇φ → □◇φ, MP gives □◇φ ∈ S.
- This is just `mcs_mp_axiom` applied with h_5.

### 5. Dependency Ordering (Waves)

**Wave 0: Shared Infrastructure** (2 new canonical frame property lemmas)
- `canonical_symm` (from axiom B)
- `canonical_eucl_from_five` (from axiom 5)
- New MCS helper: `mcs_diamond_box_five` (trivial via `mcs_mp_axiom`)
- New bundled classes in `ProofSystem.lean`
- New tag types in `ProofSystem.lean`

**Wave 1: Single-axiom extensions of K** (3 systems, independent of each other)
- **B (KB)**: KAxiom + modalB → symmetric frames → uses k_truth_lemma + canonical_symm
- **Four (K4)**: KAxiom + modal4 → transitive frames → uses k_truth_lemma + canonical_trans
- **Five (K5)**: KAxiom + modal5 → Euclidean frames → uses k_truth_lemma + canonical_eucl_from_five

**Wave 2: Two-axiom extensions of K** (3 systems)
- **K45**: KAxiom + modal4 + modal5 → trans + Eucl → uses k_truth_lemma + canonical_trans + canonical_eucl_from_five
- **TB (KTB)**: TAxiom + modalB → refl + symm → uses truth_lemma + canonical_refl + canonical_symm
- **KB5**: KAxiom + modalB + modal5 → symm + Eucl → uses k_truth_lemma + canonical_symm + canonical_eucl_from_five

**Wave 3: Extensions of D** (4 systems)
- **D4 (KD4)**: DAxiom + modal4 → serial + trans → uses truth_lemma_d + canonical_serial + canonical_trans
- **D5 (KD5)**: DAxiom + modal5 → serial + Eucl → uses truth_lemma_d + canonical_serial + canonical_eucl_from_five
- **D45 (KD45)**: DAxiom + modal4 + modal5 → ser + trans + Eucl → uses truth_lemma_d + canonical_serial + canonical_trans + canonical_eucl_from_five
- **DB (KDB)**: DAxiom + modalB → serial + symm → uses truth_lemma_d + canonical_serial + canonical_symm

### 6. Soundness Proof Pattern (Uniform)

All 10 soundness proofs follow an identical pattern:
1. Define `XAxiom` inductive type with the system's axioms
2. Prove `x_axiom_sound` by case analysis on each constructor
3. Wrap with `x_soundness` and `x_soundness_derivable` using the parameterized `soundness` theorem

The propositional cases (implyK, implyS, efq, peirce) and modalK are literally identical across all systems — only the modal-specific cases differ. This suggests extracting a shared `propositional_axiom_sound` helper, but the current pattern of duplicating these 5 cases is consistent and low-risk.

### 7. Completeness Proof Pattern (Two Variants)

**Variant A** (systems with axiom T: TB): Reuses `truth_lemma` from `Completeness.lean`.
- Completeness = contrapositive + Lindenbaum + truth_lemma + canonical frame properties

**Variant B** (systems with axiom D but not T: D4, D5, D45, DB): Reuses `truth_lemma_d` from `DCompleteness.lean`.
- Same structure as Variant A but with D-specific box witness

**Variant C** (systems with neither T nor D: B, Four, Five, K45, KB5): Reuses `k_truth_lemma` from `KCompleteness.lean`.
- Same structure but with K-specific box witness (no T or D needed)

All three variants share the identical contrapositive setup (showing {¬φ} is consistent, Lindenbaum extension, final contradiction). The differences are only in:
1. Which truth lemma is used
2. Which canonical frame property lemmas are invoked

## Recommended Approach

### Design Principle: Follow Existing Patterns Exactly

The existing 5 systems establish a clear, consistent pattern. Each new system should:
1. **Axiom predicate**: New inductive type with propositional core + K + system-specific modal axioms
2. **Tag type**: New opaque type in `ProofSystem.lean`
3. **Bundled class**: New class extending `ModalHilbert` with appropriate `HasAxiom*` classes
4. **Instances**: Register all typeclass instances (InferenceSystem, ModusPonens, Necessitation, HasAxiom*, bundled)
5. **Soundness**: New file `XSoundness.lean` with `x_axiom_sound`, `x_soundness`, `x_soundness_derivable`
6. **Completeness**: New file `XCompleteness.lean` with `x_completeness`

### File Organization

New files needed:
- `Cslib/Logics/Modal/Metalogic/BSoundness.lean`
- `Cslib/Logics/Modal/Metalogic/BCompleteness.lean`
- `Cslib/Logics/Modal/Metalogic/FourSoundness.lean`
- `Cslib/Logics/Modal/Metalogic/FourCompleteness.lean`
- `Cslib/Logics/Modal/Metalogic/FiveSoundness.lean`
- `Cslib/Logics/Modal/Metalogic/FiveCompleteness.lean`
- `Cslib/Logics/Modal/Metalogic/K45Soundness.lean`
- `Cslib/Logics/Modal/Metalogic/K45Completeness.lean`
- `Cslib/Logics/Modal/Metalogic/D4Soundness.lean`
- `Cslib/Logics/Modal/Metalogic/D4Completeness.lean`
- `Cslib/Logics/Modal/Metalogic/D5Soundness.lean`
- `Cslib/Logics/Modal/Metalogic/D5Completeness.lean`
- `Cslib/Logics/Modal/Metalogic/D45Soundness.lean`
- `Cslib/Logics/Modal/Metalogic/D45Completeness.lean`
- `Cslib/Logics/Modal/Metalogic/DBSoundness.lean`
- `Cslib/Logics/Modal/Metalogic/DBCompleteness.lean`
- `Cslib/Logics/Modal/Metalogic/TBSoundness.lean`
- `Cslib/Logics/Modal/Metalogic/TBCompleteness.lean`
- `Cslib/Logics/Modal/Metalogic/KB5Soundness.lean`
- `Cslib/Logics/Modal/Metalogic/KB5Completeness.lean`

Modified files:
- `Cslib/Foundations/Logic/ProofSystem.lean` — new bundled classes and tag types
- `Cslib/Logics/Modal/ProofSystem/Instances.lean` — new axiom predicates and instance registrations
- `Cslib/Logics/Modal/Metalogic/Completeness.lean` — add `canonical_symm`
- `Cslib/Logics/Modal/Metalogic/MCS.lean` or new shared file — add `canonical_eucl_from_five`
- `Cslib/Logics/Modal/Metalogic.lean` — add imports for new modules

## Evidence/Examples

### Example: B (KB) System Design

```lean
-- Axiom predicate (in Instances.lean)
inductive BAxiom : Proposition Atom → Prop where
  | implyK (φ ψ) : BAxiom (φ.imp (ψ.imp φ))
  | implyS (φ ψ χ) : BAxiom ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ)))
  | efq (φ) : BAxiom (Proposition.bot.imp φ)
  | peirce (φ ψ) : BAxiom (((φ.imp ψ).imp φ).imp φ)
  | modalK (φ ψ) : BAxiom ((□(φ.imp ψ)).imp ((□φ).imp (□ψ)))
  | modalB (φ) : BAxiom (φ.imp (□(◇φ)))

-- Soundness (BSoundness.lean)
theorem b_axiom_sound (h_ax : BAxiom φ) (m : Model World Atom)
    (h_symm : ∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁)
    (w : World) : Satisfies m w φ

-- Completeness (BCompleteness.lean) — uses canonical_symm + k_truth_lemma
theorem b_completeness (φ : Proposition Atom)
    (h_valid : ∀ World m, (∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁) → ∀ w, Satisfies m w φ) :
    Derivable (@BAxiom Atom) φ
```

### Example: canonical_symm (New Infrastructure)

```lean
-- In Completeness.lean or new CanonicalProperties.lean
theorem canonical_symm
    {Axioms : Proposition Atom → Prop}
    (h_implyK : ...)
    (h_implyS : ...)
    (h_efq : ...)
    (h_peirce : ...)
    (h_K : ...)
    (h_B : ∀ φ, Axioms (φ.imp (□(◇φ))))
    (S T : CanonicalWorld Axioms) :
    (CanonicalModel Axioms).r S T →
    (CanonicalModel Axioms).r T S
-- Proof: Given R^C(S,T), for any □φ ∈ T, show φ ∈ S.
-- By B: ¬φ → □◇¬φ. If φ ∉ S, then ¬φ ∈ S, so □◇¬φ ∈ S.
-- R^C(S,T) gives ◇¬φ ∈ T, i.e., ¬□φ ∈ T (since ◇¬φ = ¬□¬¬φ and with DNE ¬□φ).
-- Wait — ◇¬φ = ¬□¬(¬φ) = ¬□φ only when we identify ¬¬φ with φ (classical).
-- More carefully: ◇(¬φ) = (□((¬φ) → ⊥)) → ⊥ = (□(φ)) → ⊥ (since (φ → ⊥) → ⊥ at prop level).
-- Actually ¬φ = φ → ⊥, so ◇(¬φ) = (□((φ → ⊥) → ⊥)) → ⊥.
-- The B axiom gives ¬φ → □(◇(¬φ)), so with MCS closure we get □(◇(¬φ)) ∈ S.
-- R^C(S,T) gives ◇(¬φ) ∈ T, i.e., (□(¬¬φ)) → ⊥ ∈ T.
-- But □φ ∈ T. We need to derive □¬¬φ from □φ via necessitation of DNE.
-- Derive ¬¬φ from φ via propositional logic, NEC gives □(φ → ¬¬φ), K gives □φ → □¬¬φ.
-- So □¬¬φ ∈ T. Then MP with (□¬¬φ → ⊥) gives ⊥ ∈ T. Contradiction with MCS.
```

## Confidence Level

- **Infrastructure analysis**: **High** — I've read every relevant file thoroughly
- **Soundness design**: **High** — straightforward pattern replication
- **Completeness design**: **High** for systems using T or D truth lemmas, **Medium-High** for systems needing canonical_symm and canonical_eucl_from_five (the proofs need careful handling of diamond/negation encoding)
- **Dependency ordering**: **High** — based on clear dependency structure
- **File organization**: **High** — follows established patterns exactly
