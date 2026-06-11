# Teammate C (Critic) Findings: Task 99

**Task**: Complete modal cube Hilbert proof systems (B, Four, Five, K45, D4, D5, D45, DB, TB, KB5)
**Date**: 2026-06-10
**Confidence Level**: High

## Key Findings — Gaps and Risks

### 1. CRITICAL: `canonical_eucl` Does Not Prove Euclideanness from Axiom 5

The existing `canonical_eucl` (Completeness.lean:94-141) proves the canonical relation is Euclidean using axioms **T, 4, B, and K together**. This is the S5-specific derivation of Euclideanness (reflexive + transitive + symmetric → Euclidean).

**However**, for logics like K45, D5, D45, KB5 — which contain axiom 5 (`◇φ → □◇φ`) without necessarily having T, 4, or B — we need a **completely new proof**: `canonical_eucl_from_5` that proves the canonical relation is Euclidean directly from the 5 axiom.

The standard proof (Blackburn Thm 4.28/Exercise 4.3.1): Given `SRₓT` and `SRₓU`, to show `TRₓU`, take any `□φ ∈ T`. We need `φ ∈ U`. By contrapositive, assume `φ ∉ U`, then `¬φ ∈ U` (MCS), so `□¬φ ∉ S` (since `SRₓU` and consistency), but from `□φ ∈ T` and `SRₓT` we'd need... Actually the correct standard argument is:

- Assume `SRₓT`, `SRₓU`, and `□φ ∈ T`.
- We want `φ ∈ U`.
- Since `□φ ∈ T` and `SRₓT`, by axiom 5 in T: `◇φ ∈ T → □◇φ ∈ T`. But we need the contrapositive direction involving `¬◇φ = □¬φ`.
- Actually: from `□φ ∈ T`, axiom 4 in K45 gives `□□φ ∈ T`... Wait, K45 has axiom 5 but not axiom 4!

**This is precisely the subtlety**: The standard proof that "axiom 5 is canonical for Euclideanness" works differently. The correct argument is:
- Assume `SRₓT`, `SRₓU`, and `□φ ∈ T`. Need `φ ∈ U`.
- Since `□φ ∈ T`, then `¬◇¬φ ∈ T` (i.e., `(□(φ→⊥))→⊥ ∉ T` is false, meaning `□¬φ ∉ T`).
- Actually: `□φ ∈ T` means `◇¬φ ∉ T` (by MCS). By axiom 5: `◇ψ → □◇ψ`, contrapositive: `¬□◇ψ → ¬◇ψ`. Since `◇¬φ ∉ T`, we get... Hmm, this direction doesn't help directly.

The **real** standard proof (from any textbook treating K5 separately):
- Assume `wRv` and `wRu`. Take `□φ ∈ v`. Need `φ ∈ u`.
- From `□φ ∈ v`: `φ ∈ v` is NOT guaranteed (no axiom T).
- Use axiom 5 at world `w`: from `◇φ ∈ w` (since `wRv` and `□φ ∈ v` gives... wait no.)

**This needs careful research**. The correct Blackburn proof for Euclideanness of the canonical frame from axiom 5 is:
- Suppose `wRv` and `wRu` in the canonical frame. We need `vRu`.
- Take any `□φ ∈ v`. We need `φ ∈ u`.
- Since `□φ ∈ v`, then `□φ ∈ v` means... From axiom 5 (`◇ψ → □◇ψ`), equivalently `¬□ψ → □¬□ψ` (contrapositive of 5 rephrased). So: if `¬□φ ∉ v` (which we know, since `□φ ∈ v`), this doesn't directly help.

Let me re-examine. The correct proof:
- `wRv` means `∀ψ, □ψ ∈ w → ψ ∈ v`.
- `wRu` means `∀ψ, □ψ ∈ w → ψ ∈ u`.
- Need to show `vRu`, i.e., `∀ψ, □ψ ∈ v → ψ ∈ u`.
- Take `□φ ∈ v`. By contrapositive: assume `φ ∉ u`, then `¬φ ∈ u`. Since `wRu`: if `□¬φ ∈ w` then `¬φ ∈ u`. But we can't get `□¬φ ∈ w` easily.
- **Key step using axiom 5**: From `□φ ∈ v`, we have `¬◇¬φ ∈ v`, i.e. `¬(□(¬φ→⊥)→⊥) ∈ v`... This is getting complex.

The actual standard textbook argument uses the **contrapositive of axiom 5** applied at world `w`:
- Axiom 5: `◇ψ → □◇ψ` for all ψ.
- Contrapositive: `¬□◇ψ → ¬◇ψ`, i.e., `◇¬◇ψ → □¬ψ` (using `¬◇ = □¬`).
- Equivalently: `◇□ψ → □ψ` (substituting `¬ψ` for `ψ` and rearranging).

So axiom 5 gives us: **`◇□ψ → □ψ`** (the "5-dual" principle).

Now: Given `wRv`, `□φ ∈ v`. Then `◇□φ ∈ w` (since w sees v and v has □φ — wait, that's not right either. `wRv` gives: `□ψ ∈ w → ψ ∈ v`, not the reverse.)

**This is the key difficulty**: The canonical relation `wRv ↔ ∀ψ, □ψ ∈ w → ψ ∈ v` means we can transfer from w's boxes INTO v, not from v's boxes into w.

The correct standard proof (Hughes & Cresswell, or Chellas):
- Assume `wRv`, `wRu`, `□φ ∈ v`. Show `φ ∈ u`.
- From `□φ ∈ v`: By contrapositive suppose `φ ∉ u`, so `¬φ ∈ u` (MCS). Since `wRu`: we'd need `□¬φ ∈ w` to conclude `¬φ ∈ u`, but we already have `¬φ ∈ u`.
- Actually the proof goes: Suppose `vR̸u`, i.e., ∃ψ with `□ψ ∈ v` but `ψ ∉ u`. Since `ψ ∉ u`, `¬ψ ∈ u`. Since `wRu`, if `□¬ψ ∈ w`, then `¬ψ ∈ u` — but we have that already.
- The REAL argument: Assume `□φ ∈ v` and `φ ∉ u`. Then `¬φ ∈ u` (MCS). Since `wRu`, `□(¬φ) ∉ w` or `¬φ ∈ u` — we have the latter. But we need a contradiction.
- From `□φ ∈ v`: Suppose `□φ ∉ w`. Then `¬□φ ∈ w`, i.e., `◇¬φ ∈ w`. By axiom 5: `◇¬φ → □◇¬φ ∈ w`, so `□◇¬φ ∈ w`. Since `wRv`: `◇¬φ ∈ v`. But `□φ ∈ v` means `¬◇¬φ ∈ v` — contradiction!
- Therefore `□φ ∈ w`. Since `wRu`: `φ ∈ u`. ✓

**So the correct proof strategy for `canonical_eucl_from_5` is**:
1. Assume `wRv`, `wRu`, `□φ ∈ v`.
2. Suppose for contradiction `□φ ∉ w`.
3. Then `◇¬φ ∈ w` (by MCS + definition of ◇).
4. By axiom 5 in w: `□◇¬φ ∈ w`.
5. Since `wRv`: `◇¬φ ∈ v`.
6. But `□φ ∈ v` means `¬◇¬φ ∈ v` — contradiction.
7. So `□φ ∈ w`. Since `wRu`: `φ ∈ u`. ✓

**Risk level: HIGH**. This is a non-trivial new proof that does NOT exist in the codebase. All logics with axiom 5 (K45, D5, D45, KB5) depend on this.

### 2. CRITICAL: Canonical Symmetry from Axiom B (Without Axiom T)

The codebase defines `B` in Cube.lean as `logic {m | Std.Symm m.r}` — the logic of ALL symmetric frames (not reflexive+symmetric). This is **KB** in standard nomenclature.

For KB completeness, we need `canonical_symm`: the canonical relation is symmetric when axiom B is present. The Blackburn proof (Thm 4.28 clause 2):
- Assume `wRv`. Need `vRw`.
- Take any `□φ ∈ v`. Need `φ ∈ w`.
- From `□φ ∈ v` and axiom B at w: `φ ∈ w → □◇φ ∈ w`. Hmm, that's in the wrong direction.
- Actually: We need: if `□φ ∈ v`, then `φ ∈ w`.
- By contrapositive: if `φ ∉ w`, then `□φ ∉ v`.
- Suppose `φ ∉ w`. Then `¬φ ∈ w` (MCS). By axiom B at w: `¬φ → □◇¬φ`, so `□◇¬φ ∈ w`. Since `wRv`: `◇¬φ ∈ v`. But `◇¬φ ∈ v` means `□φ ∉ v` (since `◇¬φ = ¬□φ` only when `¬φ = φ→⊥` and `◇ψ = □(ψ→⊥)→⊥`... this needs careful encoding).

Actually the standard argument is simpler: Assume `wRv`, take `□φ ∈ v`. Then w must contain φ? No — that's `vRw`. The correct proof:
- `wRv` means: `∀ψ, □ψ ∈ w → ψ ∈ v`.
- Need `vRw`: `∀ψ, □ψ ∈ v → ψ ∈ w`.
- Take `□φ ∈ v`. Need `φ ∈ w`.
- By axiom B at w: `φ → □◇φ` is in w (it's an axiom schema, so every MCS contains it).
- Contrapositive: suppose `φ ∉ w`, then `¬φ ∈ w`.
- From axiom B with ¬φ: `¬φ → □◇(¬φ) ∈ w`, so `□◇(¬φ) ∈ w`.
- Since `wRv`: `◇(¬φ) ∈ v`.
- `◇(¬φ) ∈ v` = `(□((¬φ)→⊥))→⊥ ∈ v` = `(□(φ))→⊥ ∈ v` ... Wait: `◇ψ = (□(ψ→⊥))→⊥`, so `◇(¬φ) = (□((φ→⊥)→⊥))→⊥ = (□¬¬φ)→⊥`.

Hmm, this is where the encoding matters. In the codebase, `diamond φ = (box (φ.imp bot)).imp bot` (NOT `¬□¬φ` unless you unfold carefully with double negation).

So `◇(¬φ) = (□(¬φ → ⊥)) → ⊥ = (□¬¬φ) → ⊥`. And `□φ ∈ v` does NOT directly contradict `◇(¬φ) ∈ v` without a double negation step.

**Risk**: The diamond encoding as `(□(φ→⊥))→⊥` makes the B axiom proof more complex than the standard textbook presentation that uses `◇φ = ¬□¬φ` directly. The codebase avoids primitive negation/diamond, so all proofs go through the `imp`/`bot` encoding. This adds derivation steps.

**The existing `canonical_eucl` proof already handles this encoding** (see lines 127-141 of Completeness.lean which constructs DNE derivation trees explicitly). A new `canonical_symm` will need similar derivation tree gymnastics.

**Risk level: MEDIUM-HIGH**. The proof exists in the mathematical literature but encoding it with the `imp`/`bot` representation requires careful derivation tree manipulation (as seen in the existing proofs).

### 3. MEDIUM: Truth Lemma Variants — Three Different Box Witnesses

The codebase has THREE different truth lemma variants:
1. **`truth_lemma`** (Completeness.lean): Uses `mcs_box_witness` which requires **axiom T** (for the "neg phi not in L" case).
2. **`k_truth_lemma`** (KCompleteness.lean): Uses `k_mcs_box_witness` which requires **axiom K + EFQ + Peirce** (no T, uses EFQ fallback).
3. **`truth_lemma_d`** (DCompleteness.lean): Uses `mcs_box_witness_d` which requires **axiom D** (uses seriality argument for "neg phi not in L" case).

**For the 10 remaining logics**, which truth lemma applies?

| Logic | Has T? | Has D? | Truth Lemma to Use |
|-------|--------|--------|-------------------|
| B (symmetric only) | NO | NO | `k_truth_lemma` |
| Four (transitive only) | NO | NO | `k_truth_lemma` |
| Five (Euclidean only) | NO | NO | `k_truth_lemma` |
| K45 | NO | NO | `k_truth_lemma` |
| D4 | NO | YES | `truth_lemma_d` |
| D5 | NO | YES | `truth_lemma_d` |
| D45 | NO | YES | `truth_lemma_d` |
| DB | NO | YES | `truth_lemma_d` |
| TB | YES | YES* | `truth_lemma` |
| KB5 | NO | NO | `k_truth_lemma` |

*TB has T, which implies D.

**Key insight**: The truth lemma primarily needs the **box witness** (Existence Lemma). The frame property proofs are separate. So most new logics just reuse one of the existing truth lemmas and add new canonical frame property proofs.

**Risk level: LOW**. The existing infrastructure covers all cases. No new truth lemmas needed.

### 4. MEDIUM: The `canonical_eucl` Proof Uses T+4+B → Euclidean, but We Need 5 → Euclidean

As detailed in Finding #1, the existing `canonical_eucl` cannot be reused for K45, D5, D45, KB5. A new `canonical_eucl_from_5` is needed that works from axiom 5 alone.

Additionally, there's a mathematical subtlety: **In the presence of both B and 5 (logic KB5), is the canonical relation both symmetric AND Euclidean?** Yes — B gives symmetry, 5 gives Euclideanness. These compose independently. But it's important to verify they don't interfere.

**Risk level: MEDIUM**. The new proof (`canonical_eucl_from_5`) is the main new mathematical content.

### 5. LOW-MEDIUM: Missing Tag Types and Bundled Classes

The ProofSystem.lean defines tag types for K, T, D, S4, S5 only. For the 10 new logics, we need:

**Missing tag types** (10):
- `Modal.HilbertB`, `Modal.HilbertFour`, `Modal.HilbertFive`
- `Modal.HilbertK45`, `Modal.HilbertD4`, `Modal.HilbertD5`
- `Modal.HilbertD45`, `Modal.HilbertDB`, `Modal.HilbertTB`, `Modal.HilbertKB5`

**Missing bundled classes** (potentially needed):
- `ModalBHilbert` (K + B)
- `ModalFourHilbert` (K + 4)
- `ModalFiveHilbert` (K + 5)
- `ModalK45Hilbert` (K + 4 + 5)
- `ModalD4Hilbert` (K + D + 4)
- `ModalD5Hilbert` (K + D + 5)
- `ModalD45Hilbert` (K + D + 4 + 5)
- `ModalDBHilbert` (K + D + B)
- `ModalTBHilbert` (K + T + B)
- `ModalKB5Hilbert` (K + B + 5)

Note: `HasAxiom5` and `HasAxiomB` already exist in ProofSystem.lean (lines 138-143). The foundational individual axiom typeclasses are complete.

**Risk level: LOW**. This is mechanical — define opaque types, register instances.

### 6. LOW: The "Logic B" Naming vs Standard Convention

In `Cube.lean`, `B` is defined as `logic {m | Std.Symm m.r}` — the logic of all symmetric frames. In standard modal logic texts, "B" typically means **KTB** (K + T axiom + B axiom = reflexive + symmetric frames).

The codebase's `B` is actually **KB** in standard notation. And the codebase's `TB` is the standard "logic B" (= KTB).

This naming is internally consistent (it matches the `Cube.lean` definitions) but could cause confusion when referencing the literature. All tasks should use the codebase naming consistently.

**Risk level: LOW**. Just a documentation concern; the math is correct.

### 7. MEDIUM: Axiom Predicates Need to Include Axiom 5

Looking at the existing axiom predicates:
- `KAxiom`: propositional + K
- `TAxiom`: propositional + K + T
- `DAxiom`: propositional + K + D
- `S4Axiom`: propositional + K + T + 4
- `ModalAxiom` (S5): propositional + K + T + 4 + B

None of the existing axiom predicates include axiom 5 as a separate constructor. The `ModalAxiom` (S5) omits it because in S5, axiom 5 is derivable from T + 4 + B.

For K45, D5, D45, KB5, we need new axiom predicates with a `modal5` / `modalFive` constructor encoding `◇φ → □◇φ`. This constructor needs to express axiom 5 in the `imp`/`bot`/`box` encoding:

```
| modalFive (φ : Proposition Atom) :
    FiveAxiom (Proposition.imp
      (Proposition.imp (Proposition.box (Proposition.imp φ Proposition.bot)) Proposition.bot)
      (Proposition.box (Proposition.imp (Proposition.box (Proposition.imp φ Proposition.bot)) Proposition.bot)))
```

This matches the existing `Axioms.Axiom5` definition in `Axioms.lean` (line 112-115).

**Risk level: LOW-MEDIUM**. Straightforward but must be done carefully to match the polymorphic `Axioms.Axiom5` definition.

### 8. LOW: Soundness Proofs Are Straightforward

Soundness for each new system amounts to showing each axiom is valid on the appropriate frame class. The existing `Satisfies.b`, `Satisfies.four`, `Satisfies.five`, `Satisfies.d` (in Basic.lean) already prove the semantic validity of each individual axiom. Compound soundness just combines these.

The parameterized `soundness` theorem takes a callback — each new soundness proof just does case analysis on the axiom predicate and dispatches to the appropriate `Satisfies.*` lemma.

**Risk level: LOW**. Mechanical.

### 9. MEDIUM: Code Duplication in Completeness Proofs

The current completeness proofs (K, T, D, S4, S5) each contain a ~30-line copy of the "contrapositive setup" (lines proving `{¬φ}` is consistent from the assumption that `φ` is not derivable). This is identical across all five proofs.

For 10 more logics, this will create massive duplication. A shared `completeness_contrapositive` helper that takes the axiom predicate and produces the consistent set `{¬φ}` would eliminate ~300 lines of redundancy.

**Risk level: LOW** (correctness-wise) but **HIGH for maintenance**. Strongly recommend factoring this out first.

### 10. LOW: Dependency Ordering of New Frame Property Lemmas

The new canonical frame property lemmas needed:
1. `canonical_symm` — from axiom B (needed by: B, DB, TB, KB5)
2. `canonical_eucl_from_5` — from axiom 5 (needed by: Five, K45, D5, D45, KB5)

These are **independent** of each other and of the existing `canonical_refl`, `canonical_trans`, `canonical_serial`. The proof structure allows full parallelism in Wave 1.

## Recommended Approach

### Wave 0 (Infrastructure — Do First):
1. **Factor out `completeness_contrapositive`** helper to eliminate ~30 lines of duplication per logic.
2. **Prove `canonical_symm`** (from axiom B alone).
3. **Prove `canonical_eucl_from_5`** (from axiom 5 alone). THIS IS THE HARD PART.

### Wave 1 (Single-Axiom Extensions):
4. **B** (KB): KAxiom + modalB → symmetry → k_truth_lemma
5. **Four** (K4): KAxiom + modal4 → transitivity → k_truth_lemma  
6. **Five** (K5): KAxiom + modal5 → Euclidean (via new lemma) → k_truth_lemma

### Wave 2 (Two-Axiom Compound Systems):
7. **K45**: KAxiom + modal4 + modal5 → transitive + Euclidean → k_truth_lemma
8. **D4**: DAxiom + modal4 → serial + transitive → truth_lemma_d
9. **D5**: DAxiom + modal5 → serial + Euclidean → truth_lemma_d
10. **DB**: DAxiom + modalB → serial + symmetric → truth_lemma_d
11. **TB**: TAxiom + modalB → reflexive + symmetric → truth_lemma
12. **KB5**: KAxiom + modalB + modal5 → symmetric + Euclidean → k_truth_lemma

### Wave 3 (Three-Axiom Compound):
13. **D45**: DAxiom + modal4 + modal5 → serial + transitive + Euclidean → truth_lemma_d

## Evidence/Examples

- `canonical_eucl` (Completeness.lean:94): requires T, 4, B, K — NOT usable for K5/K45
- `k_truth_lemma` (KCompleteness.lean:168): requires only K, EFQ, Peirce — usable for B/Four/Five/K45/KB5
- `truth_lemma_d` (DCompleteness.lean:269): requires K, D, EFQ, Peirce — usable for D4/D5/D45/DB
- `truth_lemma` (Completeness.lean:147): requires K, T, EFQ, Peirce — usable for TB
- `Axioms.Axiom5` (Axioms.lean:112): Already defined as `◇φ → □◇φ` in correct encoding
- `HasAxiom5` (ProofSystem.lean:142): Already exists as a typeclass
- `HasAxiomB` (ProofSystem.lean:138): Already exists as a typeclass
- `Satisfies.five` (Basic.lean:329): Semantic validity of axiom 5 already proven
- `Satisfies.b` (Basic.lean:276): Semantic validity of axiom B already proven

## Summary of Risk Assessment

| Risk | Severity | Mitigation |
|------|----------|------------|
| No `canonical_eucl_from_5` | HIGH | Must prove from scratch; core dependency for 4+ logics |
| No `canonical_symm` | MEDIUM-HIGH | Standard proof but requires derivation tree manipulation |
| Diamond encoding complexity | MEDIUM | Existing proofs show the pattern; follow `canonical_eucl` style |
| Code duplication explosion | MEDIUM | Factor out contrapositive helper FIRST |
| Missing axiom 5 in predicates | LOW-MEDIUM | Mechanical; follow existing pattern |
| Missing tag types/classes | LOW | Mechanical |
| Soundness proofs | LOW | Combine existing `Satisfies.*` lemmas |
