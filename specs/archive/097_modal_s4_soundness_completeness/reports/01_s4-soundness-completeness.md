# Research Report: S4 Soundness and Completeness

**Task**: 97 -- Establish soundness and completeness for modal logic S4
**Status**: Researched
**Date**: 2026-06-10
**Session**: sess_1781140623_7b07f0

## Literature Proof Structure

**Sources**:
- Hebert, "Completeness in Modal Logic" (U. Chicago REU, 2020) -- Full S4 completeness via canonical models
- Platzer, "Completeness and Canonical Models" (CMU 15-816 Lecture 20, 2010) -- Framework and strong completeness
- Sergot, "Canonical models for normal logics" (Imperial College 499, 2008) -- Detailed S4 reflexivity/transitivity proofs

**Strategy**: Canonical model construction with frame property verification

### Step Map

1. **S4 Axiom Soundness** -- Each S4Axiom schema valid on reflexive + transitive frames
   - Source: Standard (Chellas 5.1, Sergot Thm 2)
   - Lean target: `s4_axiom_sound` in Soundness/S4.lean
   - Reuses pattern from `axiom_sound` in Soundness.lean

2. **S4 Soundness Theorem** -- If Gamma |-_{S4} phi then phi valid on reflexive+transitive frames
   - Source: Follows from Step 1 + parameterized `soundness` theorem
   - Lean target: `s4_soundness`, `s4_soundness_derivable` in Soundness/S4.lean
   - Direct instantiation of existing `soundness` with `s4_axiom_sound`

3. **Canonical Reflexivity** -- Canonical frame for S4 is reflexive (from axiom T)
   - Source: Sergot p.11, Hebert Lemma 4.5
   - Lean target: reuse `canonical_refl` from Completeness.lean (already parameterized)
   - Proof: Box(A) in S, axiom T gives Box(A)->A, MCS closure gives A in S

4. **Canonical Transitivity** -- Canonical frame for S4 is transitive (from axiom 4)
   - Source: Sergot p.11, Hebert Lemma 4.5
   - Lean target: reuse `canonical_trans` from Completeness.lean (already parameterized)
   - Proof: Box(A) in S, axiom 4 gives Box(Box(A)) in S, then accessibility chain

5. **Truth Lemma** -- Satisfies(M^S4, S, phi) iff phi in S for all MCS S
   - Source: Sergot Thm 6, Hebert Lemma 3.9, Platzer Thm 8
   - Lean target: reuse `truth_lemma` from Completeness.lean (already parameterized)
   - Requires: implyK, implyS, efq, peirce, K, T axiom hypotheses

6. **S4 Completeness** -- If phi valid over all reflexive+transitive frames then S4-derivable
   - Source: Hebert Thm 4.6, Sergot Example (S4), Platzer Thm 13
   - Lean target: `s4_completeness` in Completeness/S4.lean
   - Proof: contrapositive, {neg(phi)} consistent, Lindenbaum, canonical model is reflexive+transitive, Truth Lemma, contradiction

### Dependencies

- Step 2 depends on Step 1
- Steps 3 and 4 are independent (can be proven in parallel)
- Step 5 depends on Steps 3 and 4 only at the completeness theorem level
- Step 6 depends on Steps 3, 4, 5

### Potential Formalization Challenges

- **Step 1**: Trivial adaptation -- only 7 cases instead of 8, no Euclidean frame condition needed
- **Step 6**: The completeness proof is structurally identical to S5 completeness, but with 2 frame conditions instead of 3. The contrapositive argument is the same.

## Existing Infrastructure Analysis

### What Already Exists (Fully Parameterized)

The codebase has a remarkably well-parameterized infrastructure. All core theorems accept an `Axioms : Proposition Atom -> Prop` parameter and explicit axiom hypotheses:

| Theorem | File | Parameters |
|---------|------|------------|
| `canonical_refl` | Completeness.lean:65 | h_implyK, h_implyS, h_T |
| `canonical_trans` | Completeness.lean:78 | h_implyK, h_implyS, h_4 |
| `canonical_eucl` | Completeness.lean:95 | h_implyK, h_implyS, h_T, h_4, h_B, h_K |
| `truth_lemma` | Completeness.lean:147 | h_implyK, h_implyS, h_efq, h_peirce, h_K, h_T |
| `soundness` | Soundness.lean:85 | h_ax_sound callback |
| `axiom_sound` | Soundness.lean:46 | h_refl, h_trans, h_eucl |
| `mcs_box_closure` | MCS.lean:139 | h_implyK, h_implyS, h_T |
| `mcs_box_box` | MCS.lean:151 | h_implyK, h_implyS, h_4 |
| `mcs_box_witness` | MCS.lean:360 | h_implyK, h_implyS, h_efq, h_peirce, h_K, h_T |
| `modal_lindenbaum` | MCS.lean:59 | (no axiom params needed) |

### S4Axiom Inductive Type

Already defined in `Instances.lean:130-153`:
```
inductive S4Axiom : Proposition Atom -> Prop where
  | implyK   | implyS   | efq   | peirce
  | modalK   | modalT   | modalFour
```

This has 7 constructors (same as S5's ModalAxiom minus modalB).

### Instance Registration

Already registered in `Instances.lean:343-415`:
- `InferenceSystem Modal.HilbertS4`
- `ModusPonens`, `Necessitation`, all axiom instances
- `ModalHilbert`, `ModalTHilbert`, `ModalS4Hilbert`

## Proof Architecture for New Files

### File 1: Metalogic/Soundness/S4.lean (~70 lines)

**Imports**: `Cslib.Logics.Modal.Metalogic.Soundness` (for `soundness`, `axiom_sound`)

**New Theorems**:

1. `s4_axiom_sound` -- Each S4Axiom valid on reflexive+transitive frames
   - Pattern match on 7 S4Axiom cases
   - Propositional cases (implyK, implyS, efq, peirce): identical to S5
   - modalK: identical to S5
   - modalT: use h_refl, identical to S5
   - modalFour: use h_trans, identical to S5
   - Estimated: ~30 lines

2. `s4_soundness` -- S4 soundness from context
   - Instantiate `soundness` with `s4_axiom_sound` callback
   - Estimated: ~8 lines

3. `s4_soundness_derivable` -- S4 soundness from empty context
   - Instantiate `soundness_derivable` with `s4_axiom_sound` callback
   - Estimated: ~8 lines

### File 2: Metalogic/Completeness/S4.lean (~220 lines)

**Imports**: `Cslib.Logics.Modal.Metalogic.Completeness` (brings in MCS, Soundness, etc.)

**New Theorems**:

1. `s4_completeness` -- Main completeness theorem
   - Type signature:
     ```
     theorem s4_completeness (phi : Proposition Atom)
         (h_valid : forall (World : Type u) (m : Model World Atom),
           (forall w, m.r w w) ->
           (forall w1 w2 w3, m.r w1 w2 -> m.r w2 w3 -> m.r w1 w3) ->
           forall w, Satisfies m w phi) :
         Derivable (@S4Axiom Atom) phi
     ```
   - Proof structure: identical to `completeness` in Completeness.lean but:
     - Uses `S4Axiom` instead of `ModalAxiom`
     - h_valid takes 2 frame conditions (refl, trans) not 3 (refl, trans, eucl)
     - `canonical_refl` instantiated with S4Axiom.implyK, S4Axiom.implyS, S4Axiom.modalT
     - `canonical_trans` instantiated with S4Axiom.implyK, S4Axiom.implyS, S4Axiom.modalFour
     - NO `canonical_eucl` needed (this is the key simplification vs S5)
     - `truth_lemma` instantiated with S4Axiom constructors
   - Estimated: ~100 lines (the proof is mechanical instantiation)

### Module Updates

The module file `Metalogic.lean` needs updating to import the new files:
```
public import Cslib.Logics.Modal.Metalogic.Soundness.S4
public import Cslib.Logics.Modal.Metalogic.Completeness.S4
```

**IMPORTANT**: Since `Soundness.lean` and `Completeness.lean` are currently flat files, creating `Soundness/S4.lean` and `Completeness/S4.lean` as subdirectory files means:
- Either rename `Soundness.lean` -> `Soundness/S5.lean` (or `Soundness/Basic.lean`) and create a new `Soundness.lean` aggregator
- Or place S4 files alongside: `Metalogic/S4Soundness.lean` and `Metalogic/S4Completeness.lean`

**Recommendation**: Use flat naming (`S4Soundness.lean`, `S4Completeness.lean`) to avoid disrupting existing imports. The Metalogic.lean module already imports `Soundness` and `Completeness` -- adding `S4Soundness` and `S4Completeness` imports is non-breaking.

## Key Insight: Minimal Delta from S5

The S4 proofs are a strict subset of the S5 proofs:

| S5 Component | S4 Equivalent | Change |
|--------------|---------------|--------|
| `axiom_sound` (8 cases) | `s4_axiom_sound` (7 cases) | Drop modalB case |
| `canonical_refl` | Same (reuse) | None -- already parameterized |
| `canonical_trans` | Same (reuse) | None -- already parameterized |
| `canonical_eucl` | NOT NEEDED | Skip entirely |
| `truth_lemma` | Same (reuse) | None -- already parameterized |
| `completeness` | `s4_completeness` | Remove eucl from h_valid + instantiation |

The difference is essentially:
1. `s4_axiom_sound`: delete the `modalB` case from `axiom_sound`, remove h_eucl parameter
2. `s4_completeness`: copy `completeness`, remove Euclidean condition from hypothesis and the `canonical_eucl` call

## Tactic Survey Results

No new tactics needed beyond what the existing S5 proofs use:
- `cases` for axiom case analysis
- `intro` / `exact` for the semantic validity proofs
- `by_contra` for the completeness contrapositive
- `obtain` for Lindenbaum extraction
- `simp` for list membership

The proof is entirely structural and does not require automation beyond basic term construction.

## Risk Assessment

**Risk level**: Very low

- All infrastructure is parameterized and ready for reuse
- The S4Axiom type is already defined
- The proof follows an identical pattern to the existing S5 proof
- No new mathematical concepts needed
- No sorry risk -- every component is either reused or a strict simplification of existing code

## Blockers

None identified.

## Recommendations for Planning

1. **Phase 1**: Create `Metalogic/S4Soundness.lean` (~70 lines)
   - `s4_axiom_sound`, `s4_soundness`, `s4_soundness_derivable`
   - Build and verify

2. **Phase 2**: Create `Metalogic/S4Completeness.lean` (~100-220 lines)
   - `s4_completeness`
   - Build and verify

3. **Phase 3**: Update `Metalogic.lean` imports, full `lake build`

Estimated total: ~2-3 hours implementation. Phases are sequential (Completeness imports Soundness).
