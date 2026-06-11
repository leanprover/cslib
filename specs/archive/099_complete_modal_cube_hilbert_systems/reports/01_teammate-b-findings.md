# Teammate B Findings: Alternative Approaches and Prior Art

**Task**: #99 — Complete modal cube Hilbert proof systems
**Date**: 2026-06-10
**Angle**: Alternative patterns, prior art, code reuse strategies
**Confidence Level**: High

---

## Key Findings

### 1. The Existing Architecture Is Already Highly Parameterized

The current codebase has a deeply elegant design:

- **Parameterized `soundness` theorem** (`Soundness.lean:85`): Takes an `h_ax_sound` callback, enabling any axiom predicate to plug in its own validity proof. This is the key reuse mechanism for soundness.
- **Parameterized canonical model** (`Completeness.lean:57`): `CanonicalModel Axioms` works for *any* `Axioms : Proposition Atom → Prop`.
- **Parameterized frame property lemmas** (`Completeness.lean:65-141`): `canonical_refl`, `canonical_trans`, `canonical_eucl` each take explicit axiom hypotheses rather than depending on a specific axiom type.
- **Parameterized MCS infrastructure** (`MCS.lean`): All helpers (`mcs_box_closure`, `mcs_box_box`, `mcs_box_diamond`, etc.) take explicit `h_T`, `h_4`, `h_B` parameters.

This means the existing infrastructure is **already Pattern C** (see below) at the level of theorems — frame properties compose because each one takes only the axiom hypotheses it needs.

### 2. Patterns Evaluated

#### Pattern A: Separate Inductive Axiom Predicate Per Logic (Current Approach)
- **Used by**: K (5 constructors), T (6), D (6), S4 (7), S5 (8 via `ModalAxiom`)
- **Pros**: Clear, explicit, no indirection; each axiom predicate is self-contained; easy to case-split
- **Cons**: Massive code duplication across 10 new systems (each needs ~150 lines of boilerplate instance registration); propositional axioms repeated in every predicate

#### Pattern B: Single Parameterized Axiom Predicate `CubeAxiom (props : AxiomSet)`
```lean
structure AxiomSet where
  hasT : Bool := false
  hasB : Bool := false
  hasFour : Bool := false
  hasFive : Bool := false
  hasD : Bool := false

inductive CubeAxiom (cfg : AxiomSet) : Proposition Atom → Prop where
  | implyK ... | implyS ... | efq ... | peirce ... | modalK ...
  | modalT (h : cfg.hasT = true) ...
  | modalB (h : cfg.hasB = true) ...
  | modalFour (h : cfg.hasFour = true) ...
  | modalFive (h : cfg.hasFive = true) ...
  | modalD (h : cfg.hasD = true) ...
```
- **Pros**: One inductive type covers all 15 logics; soundness/completeness can be parameterized over `cfg`
- **Cons**: `h : cfg.hasX = true` proofs pollute case-splits; requires reworking existing KAxiom/TAxiom etc. (breaking change); `DerivationTree` doesn't naturally accommodate conditional constructors

**Verdict**: Elegant in principle but incompatible with the existing `DerivationTree` infrastructure and would require a massive refactor. **Not recommended.**

#### Pattern C: Axiom Predicates as Unions/Disjunctions (Compositional)
```lean
-- Define atomic modal axiom predicates
inductive PropAxioms : Proposition Atom → Prop where ...  -- implyK, implyS, efq, peirce
inductive AxiomK_only : Proposition Atom → Prop where ...  -- modalK
inductive AxiomT_only : Proposition Atom → Prop where ...  -- modalT
inductive AxiomB_only : Proposition Atom → Prop where ...  -- modalB  
inductive Axiom4_only : Proposition Atom → Prop where ...  -- modalFour
inductive Axiom5_only : Proposition Atom → Prop where ...  -- modalFive
inductive AxiomD_only : Proposition Atom → Prop where ...  -- modalD

-- Compose via disjunction
def KBAxiom (φ : Proposition Atom) : Prop := KAxiom φ ∨ AxiomB_only φ
def K4Axiom (φ : Proposition Atom) : Prop := KAxiom φ ∨ Axiom4_only φ
def K45Axiom (φ : Proposition Atom) : Prop := KAxiom φ ∨ Axiom4_only φ ∨ Axiom5_only φ
```
- **Pros**: Maximizes reuse; no code duplication for propositional axioms; soundness proofs compose via `Or.elim`
- **Cons**: Pattern matching on disjunctions is awkward for case-splits in soundness proofs; `DerivationTree` works with a single predicate so this is compatible; but proofs become more indirect

**Verdict**: Partially attractive but introduces proof friction. The existing approach of having each axiom predicate be a standalone inductive type is actually cleaner for the `cases` tactic.

#### Pattern D: Enhanced Typeclass Approach (Recommended Hybrid)

The typeclass hierarchy (`ProofSystem.lean:297-325`) already defines `ModalHilbert`, `ModalTHilbert`, `ModalDHilbert`, `ModalS4Hilbert`, `ModalS5Hilbert`. This can be extended naturally:

```lean
-- New bundled classes (extend existing hierarchy)
class ModalBHilbert ... extends ModalHilbert S, HasAxiomB S
class Modal4Hilbert ... extends ModalHilbert S, HasAxiom4 S  
class Modal5Hilbert ... extends ModalHilbert S, HasAxiom5 S
class ModalK45Hilbert ... extends Modal4Hilbert S, HasAxiom5 S
class ModalD4Hilbert ... extends ModalDHilbert S, HasAxiom4 S
class ModalD5Hilbert ... extends ModalDHilbert S, HasAxiom5 S
class ModalD45Hilbert ... extends ModalD4Hilbert S, HasAxiom5 S
class ModalDBHilbert ... extends ModalDHilbert S, HasAxiomB S
class ModalTBHilbert ... extends ModalTHilbert S, HasAxiomB S
class ModalKB5Hilbert ... extends ModalBHilbert S, HasAxiom5 S
```

Combined with **Pattern A** (standalone inductive axiom predicates per logic, as already done), plus the existing parameterized theorems.

**Verdict**: This is the natural extension of the existing architecture. **Recommended.**

### 3. The Two Distinct Completeness Proof Strategies

The codebase already uses two different completeness strategies:

1. **Truth lemma with axiom T** (`truth_lemma` in `Completeness.lean`): Requires `h_T` for the box witness. Used by T, S4, S5.
2. **K-style truth lemma without axiom T** (`k_truth_lemma` in `KCompleteness.lean`): Uses `k_mcs_box_witness` which works without reflexivity. Used by K.
3. **D-style truth lemma** (`truth_lemma_d` in `DCompleteness.lean`): Uses `mcs_box_witness_d` which works with axiom D (seriality) instead of T. Used by D.

For the 10 new logics, each falls into one of these categories:
- **Has axiom T** (reflexive): TB → use `truth_lemma`
- **Has axiom D but not T** (serial, not reflexive): D4, D5, D45, DB → use `truth_lemma_d`
- **Has neither T nor D** (no seriality guarantee): B, Four, Five, K45, KB5 → use `k_truth_lemma`

### 4. Blackburn's Canonicity Framework (Chapter 4)

Blackburn's key insight (Definition 4.30, Theorem 4.29) is that canonical properties **compose**: 

> "The proof of Theorem 4.27 shows that the canonical frame of any normal logic containing the 4 axiom is transitive, while the proof of the first clause of Theorem 4.28 shows that the canonical frame of any normal logic containing the T axiom is reflexive. As S4 contains both axioms, its canonical frame has both properties."

This is exactly how the existing codebase works — and it means the 10 new completeness proofs can be assembled compositionally from the existing `canonical_refl`, `canonical_trans`, `canonical_eucl`, `canonical_serial` lemmas, plus new ones:

- `canonical_symm` (from axiom B) — **needed, exists implicitly in `canonical_eucl` proof but not standalone**
- `canonical_eucl_from_5` (from axiom 5 directly) — **needed, distinct from existing `canonical_eucl` which uses T+4+B**
- `canonical_serial` (from axiom D) — **already exists in `DCompleteness.lean`**

### 5. The Missing Canonical Frame Property: Direct Euclideanness from Axiom 5

The existing `canonical_eucl` (`Completeness.lean:95-141`) proves Euclideanness using axioms T, 4, B, K — the **S5 approach**. But for logics containing axiom 5 without T (K45, D5, D45, KB5), we need a **direct proof of canonical Euclideanness from axiom 5 alone**.

Axiom 5 is: `◇φ → □◇φ` (equivalently `¬□φ → □¬□φ`).

The canonical Euclideanness proof from 5: Given `R(S,T)` and `R(S,U)`, show `R(T,U)`. Suppose `□φ ∈ T`. Then `φ ∈ U` would follow if we can show `□φ ∈ S` (since `R(S,U)`). But we don't have that directly. Instead: if `□φ ∉ S`, then by axiom 5, `□(¬□φ) ∈ S` (since `¬□φ ∈ S`), so `¬□φ ∈ T` (via `R(S,T)`). But `□φ ∈ T` — contradiction. So `□φ ∈ S`, hence `φ ∈ U`. ∎

This proof only uses axiom 5 and K (for the MCS properties). It's the key new lemma needed.

### 6. The Missing Canonical Frame Property: Symmetry from Axiom B Alone

The existing code uses `mcs_box_diamond` (axiom B: `φ → □◇φ`) in `canonical_eucl` but there's no standalone `canonical_symm`. For KB, TB, DB, we need:

**`canonical_symm`**: Given `R(S,T)`, show `R(T,S)`. Suppose `□φ ∈ T`. We need `φ ∈ S`. By axiom B in S: if `φ ∉ S` then `¬φ ∈ S`, so `□◇¬φ ∈ S`, so `◇¬φ ∈ T` (via `R(S,T)`). That means there exists U with `R(T,U)` and `¬φ ∈ U`... 

Actually the simpler Blackburn proof (Theorem 4.28, clause 2): Suppose `R(S,T)` and `□φ ∈ T`. Need `φ ∈ S`. By `R(S,T)`, if `□ψ ∈ S` then `ψ ∈ T`. Suppose for contradiction `φ ∉ S`, so `¬φ ∈ S`. By axiom B: `¬φ → □◇¬φ`, so `□◇¬φ ∈ S`, so `◇¬φ ∈ T`. But `◇¬φ = ¬□¬¬φ = ¬□φ` (in classical logic). And `□φ ∈ T` — contradiction with MCS.

Wait, `◇¬φ` is `(□(¬φ → ⊥)) → ⊥`. This is `¬□φ` when `φ` is negated... Let me be more careful. In this encoding, `◇ψ = (□(ψ → ⊥)) → ⊥`. So `□◇¬φ ∈ S` means `□((□(¬φ → ⊥)) → ⊥) ∈ S`. Via R(S,T): `(□(¬φ → ⊥)) → ⊥ ∈ T`, i.e., `◇¬φ ∈ T`. 

Now `□φ ∈ T`. We need `◇¬φ` and `□φ` to contradict in T. `◇¬φ` says "there exists an accessible world where ¬φ holds", but `□φ` says "φ holds at all accessible worlds." So `□φ` implies `□¬(¬φ → ⊥)` ... this is getting complex. The proof will need careful syntactic manipulation via `mcs_box_mp`.

### 7. Prior Art: FormalizedFormalLogic and Benzmüller

- **FormalizedFormalLogic/Foundation** (Lean 4): Has a comprehensive modal logic library with parameterized completeness. Their `Summary.lean` documents proven completeness results. They use a structure similar to ours but with a different encoding. Worth examining their axiom 5 handling.

- **Benzmüller et al.** (Isabelle/HOL, 2015): "Systematic Verification of the Modal Logic Cube" uses shallow embedding of modal logic into HOL, proving inclusion relations between cube logics automatically via Sledgehammer. Not directly applicable to our object-level Hilbert proofs but validates the mathematical relationships.

- **Bruno Bentzen** (2024): Henkin-style completeness for S5 in Lean 4. Uses a similar canonical model approach but in a different encoding.

---

## Recommended Approach

**Hybrid: Pattern A (individual axiom predicates) + Pattern D (typeclass hierarchy) + compositional canonical frame properties.**

### Architecture

1. **Keep Pattern A**: Define one inductive axiom predicate per logic (10 new predicates). Each includes the full list of its axioms as constructors. This matches the existing style and works cleanly with `DerivationTree` and `cases` tactics.

2. **Extend Pattern D**: Add `ModalBHilbert`, `Modal4Hilbert`, `Modal5Hilbert`, etc. to the typeclass hierarchy. This enables typeclass-driven reasoning and API-level composability.

3. **Factor out new canonical frame lemmas**:
   - `canonical_symm` (from axiom B only — requires K, implyK, implyS, B)
   - `canonical_eucl_from_5` (from axiom 5 only — requires K, implyK, implyS, 5)
   - Keep existing `canonical_refl`, `canonical_trans`, `canonical_serial`

4. **Three truth lemma variants** cover all 10 logics:
   - `truth_lemma` (needs T) → TB
   - `truth_lemma_d` (needs D, works without T) → D4, D5, D45, DB
   - `k_truth_lemma` (needs nothing beyond K) → B, Four, Five, K45, KB5

5. **Completeness proofs compose** by:
   - Instantiating the appropriate truth lemma
   - Composing the relevant canonical frame properties
   - Following the `by_contra → lindenbaum → truth_lemma → frame_property → contradiction` pattern

### Dependency Waves

**Wave 1** (single new axiom, reuse existing truth lemma):
- **Four** (K + axiom 4): Use `k_truth_lemma` + `canonical_trans`
- **B** (K + axiom B): Use `k_truth_lemma` + new `canonical_symm`
- **Five** (K + axiom 5): Use `k_truth_lemma` + new `canonical_eucl_from_5`

**Wave 2** (compound, depend on Wave 1 infrastructure):
- **K45** (K + 4 + 5): Use `k_truth_lemma` + `canonical_trans` + `canonical_eucl_from_5`
- **D4** (D + 4): Use `truth_lemma_d` + `canonical_serial` + `canonical_trans`
- **D5** (D + 5): Use `truth_lemma_d` + `canonical_serial` + `canonical_eucl_from_5`
- **DB** (D + B): Use `truth_lemma_d` + `canonical_serial` + `canonical_symm`
- **TB** (T + B): Use `truth_lemma` + `canonical_refl` + `canonical_symm`
- **KB5** (K + B + 5): Use `k_truth_lemma` + `canonical_symm` + `canonical_eucl_from_5`

**Wave 3** (triple compound):
- **D45** (D + 4 + 5): Use `truth_lemma_d` + `canonical_serial` + `canonical_trans` + `canonical_eucl_from_5`

### Key New Infrastructure Needed

1. **`canonical_symm`** — Standalone proof that axiom B forces canonical symmetry
2. **`canonical_eucl_from_5`** — Direct proof that axiom 5 forces canonical Euclideanness (without T or 4)
3. **`mcs_five_eucl`** — MCS helper: if `¬□φ ∈ S` then `□¬□φ ∈ S` (from axiom 5)

These three lemmas, placed in `MCS.lean` or a new `CanonicalFrameProperties.lean`, unblock all 10 completeness proofs.

---

## Evidence/Examples

### Example: How KB5 Completeness Would Look

```lean
theorem kb5_completeness (φ : Proposition Atom)
    (h_valid : ∀ (World : Type u) (m : Model World Atom),
      (∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁) →                    -- symmetric
      (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃) →    -- Euclidean
      ∀ w, Satisfies m w φ) :
    Derivable (@KB5Axiom Atom) φ := by
  by_contra h_not_deriv
  have h_cons := ... -- standard consistency proof
  obtain ⟨M, hM_sup, hM_mcs⟩ := modal_lindenbaum h_cons
  let w : CanonicalWorld (@KB5Axiom Atom) := ⟨M, hM_mcs⟩
  exact mcs_not_mem_of_neg ... hM_mcs (hM_sup ...) 
    ((k_truth_lemma ... w φ).mp
      (h_valid ...
        (canonical_symm ...)        -- from axiom B
        (canonical_eucl_from_5 ...) -- from axiom 5
        w))
```

### Example: How Soundness Composes

```lean
theorem kb5_axiom_sound {World : Type*} {φ : Proposition Atom}
    (h_ax : KB5Axiom φ) (m : Model World Atom)
    (h_symm : ∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁)
    (h_eucl : ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃)
    (w : World) : Satisfies m w φ := by
  cases h_ax with
  | implyK .. => ...   -- identical across all systems
  | implyS .. => ...
  | efq .. => ...
  | peirce .. => ...
  | modalK .. => ...
  | modalB .. => ...   -- uses h_symm
  | modalFive .. => ... -- uses h_eucl
```

---

## Gaps and Risks

1. **`canonical_symm` from B alone is non-trivial**: The proof requires careful syntactic manipulation involving `◇` (which is sugar for `(□(φ → ⊥)) → ⊥`). The existing `canonical_eucl` proof already does similar work but with T+4+B combined. Extracting a standalone B-only version may reveal the need for additional MCS helper lemmas.

2. **Axiom 5 encoding**: The axiom `◇φ → □◇φ` in this encoding is `((□(φ → ⊥)) → ⊥) → □((□(φ → ⊥)) → ⊥)`. Working with doubly-nested box/negation patterns is syntactically heavy.

3. **The "consistency proof" boilerplate** (the `by_contra` + standard derivation of `φ` from `¬φ ⊢ ⊥`) is copy-pasted across K, T, D, S4, S5 completeness proofs (~35 lines each). Consider factoring this into a lemma `consistency_from_non_derivability`.

---

## Sources

- [Systematic Verification of the Modal Logic Cube in Isabelle/HOL](https://arxiv.org/abs/1507.08717)
- [FormalizedFormalLogic/Foundation (Lean 4)](https://github.com/iehality/lean4-logic)
- [A Henkin-style completeness proof for the modal logic S5](https://philarchive.org/archive/BENAHC-2)
- [FormalizedFormalLogic/NonClassicalModalLogic](https://github.com/FormalizedFormalLogic/NonClassicalModalLogic)
- [A Modular Framework for Proof-Search via Formalised Modal Completeness in HOL Light](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.CSL.2026.18)
- Blackburn, de Rijke, Venema — *Modal Logic* (2002), Chapter 4, Theorems 4.27–4.30
