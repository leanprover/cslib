# Research Report: Soundness and Completeness for Modal Logics K and T

**Task**: 95 -- Establish soundness and completeness for modal logics K and T
**Date**: 2026-06-11
**Status**: Researched

## Literature Proof Structure

**Sources**:
- Hebert, "Completeness in Modal Logic" (UChicago REU 2020)
- Platzer, "Completeness and Canonical Models" (CMU 15-816, Lecture 20, 2010)
- Sergot, "Canonical models for normal logics" (Imperial College 499, Autumn 2008)
- Blackburn, de Rijke, Venema, "Modal Logic" (Cambridge, 2001) -- referenced by all three

**Strategy**: Canonical model construction with Henkin-style MCS extension

### Step Map

1. **Axiom validity (Soundness)** -- Each axiom of K (resp. T) is valid on all frames (resp. reflexive frames)
2. **Soundness theorem** -- Derivable formulas are valid (by induction on derivation tree)
3. **Canonical model definition** -- Worlds = MCS, Accessibility = box-membership, Valuation = atom-membership
4. **Box witness / Existence lemma** -- If box phi not in S, consistent witness world exists
5. **Truth lemma** -- M^Sigma, w |= phi iff phi in w (by induction on formula structure)
6. **Canonical frame properties** -- For T: canonical frame is reflexive (from axiom T)
7. **Completeness theorem** -- Valid implies derivable (contrapositive via canonical model)

### Dependencies
- Step 2 depends on Step 1
- Step 4 depends on Step 3 (canonical model definition) + Lindenbaum + K distribution + necessitation
- Step 5 depends on Step 4 (box case of truth lemma uses box witness)
- Step 6 depends on Step 3 (canonical model definition) + axiom T
- Step 7 depends on Steps 5 and 6 (truth lemma + frame properties)

### Potential Formalization Challenges
- **Step 4 for K**: Existing `mcs_box_witness` requires `h_T`. K does not have axiom T. Need a new K-specific box witness that avoids `h_T` in the else-branch.
- **Step 5 for K**: Existing `truth_lemma` passes `h_T` to box witness. K-specific truth lemma must use K-specific box witness.
- **Step 7 for T**: Should be simpler than S5 since no transitivity/Euclidean proofs needed.

## Existing Infrastructure Analysis

### Files Read

| File | Lines | Key Contents |
|------|-------|--------------|
| `Metalogic/Soundness.lean` | 144 | `axiom_sound` (S5), `soundness` (parameterized), `s5_soundness` |
| `Metalogic/Completeness.lean` | 325 | `CanonicalWorld`, `CanonicalModel`, `canonical_refl/trans/eucl`, `truth_lemma`, `completeness` |
| `Metalogic/MCS.lean` | 392 | MCS abbreviations, `modal_lindenbaum`, `modal_closed_under_derivation`, `modal_implication_property`, `modal_negation_complete`, `mcs_box_closure`, `mcs_box_box`, `mcs_box_diamond`, `mcs_box_mp`, `mcs_neg_of_not_mem`, `mcs_not_mem_of_neg`, `iteratedDeduction`, `derive_box_from_box_context`, `derive_box_from_inconsistency`, `mcs_box_witness` |
| `Metalogic/DerivationTree.lean` | 218 | `ModalAxiom`, `DerivationTree`, `Deriv`, `Derivable`, `modalDerivationSystem` |
| `Metalogic/DeductionTheorem.lean` | 217 | `deductionTheorem`, `modal_has_deduction_theorem` |
| `ProofSystem/Instances.lean` | 502 | `KAxiom`, `TAxiom`, `DAxiom`, `S4Axiom` inductive types; all typeclass instances for K/T/D/S4/S5 |
| `Basic.lean` | 394 | `Model`, `Proposition`, `Satisfies`, validity proofs for K/T/B/4/5/D axioms |

### Reusable Components

**Fully reusable (no modification needed)**:

1. `CanonicalWorld Axioms` -- Already parameterized over `Axioms`
2. `CanonicalModel Axioms` -- Already parameterized
3. `modal_lindenbaum` -- Already parameterized
4. `modal_closed_under_derivation` -- Already parameterized, needs `h_implyK`, `h_implyS`
5. `modal_implication_property` -- Already parameterized
6. `modal_negation_complete` -- Already parameterized
7. `mcs_neg_of_not_mem`, `mcs_not_mem_of_neg`, `mcs_mem_iff_neg_not_mem` -- Already parameterized
8. `mcs_bot_not_mem` -- Already parameterized
9. `mcs_mp_axiom` -- Already parameterized
10. `mcs_box_mp` -- Already parameterized, needs `h_K`
11. `iteratedDeduction` -- Already parameterized, needs `h_K`
12. `derive_box_from_box_context` -- Already parameterized, needs `h_K`
13. `deductionTheorem` -- Already parameterized, needs `h_implyK`, `h_implyS`
14. `soundness` (parameterized theorem) -- Takes `h_ax_sound` callback; directly usable for K and T
15. `soundness_derivable` -- Same, for derivable formulas

**Reusable with appropriate axiom instantiation**:

16. `canonical_refl` -- Takes `h_implyK`, `h_implyS`, `h_T`; directly usable for T completeness
17. `mcs_box_closure` -- Takes `h_T`; usable where T axiom is available

**NOT reusable for K (require modification or K-specific versions)**:

18. `derive_box_from_inconsistency` -- Takes `h_T`; uses it in the else-branch
19. `mcs_box_witness` -- Takes `h_T`; delegates to `derive_box_from_inconsistency`
20. `truth_lemma` -- Takes `h_T`; delegates to `mcs_box_witness`
21. `completeness` -- Specific to S5

### Axiom Types (from Instances.lean)

**KAxiom** (5 constructors):
```
| implyK (phi psi)         -- phi -> (psi -> phi)
| implyS (phi psi chi)     -- (phi -> (psi -> chi)) -> ((phi -> psi) -> (phi -> chi))
| efq (phi)                -- bot -> phi
| peirce (phi psi)         -- ((phi -> psi) -> phi) -> phi
| modalK (phi psi)         -- box(phi -> psi) -> (box phi -> box psi)
```

**TAxiom** (6 constructors): KAxiom + `modalT (phi) -- box phi -> phi`

## Detailed Design for New Files

### File 1: Metalogic/Soundness/K.lean (~80 lines)

**Purpose**: K soundness -- every KAxiom is valid on all frames.

**Structure**:
```lean
theorem k_axiom_sound {World : Type*} {phi : Proposition Atom}
    (h_ax : KAxiom phi) (m : Model World Atom)
    (w : World) : Satisfies m w phi

theorem k_soundness {World : Type*}
    {Gamma : List (Proposition Atom)} {phi : Proposition Atom}
    (d : DerivationTree (@KAxiom Atom) Gamma phi)
    (m : Model World Atom) (w : World)
    (h_ctx : forall psi in Gamma, Satisfies m w psi) : Satisfies m w phi

theorem k_soundness_derivable {World : Type*}
    {phi : Proposition Atom} (h : Derivable (@KAxiom Atom) phi)
    (m : Model World Atom) (w : World) : Satisfies m w phi
```

**Proof approach for `k_axiom_sound`**: Case split on `h_ax`:
- `implyK`: `intro h_phi _; exact h_phi`
- `implyS`: `intro h1 h2 h3; exact h1 h3 (h2 h3)`
- `efq`: `intro h; exact absurd h id`
- `peirce`: `intro h; by_contra h_not; exact h_not (h (fun h_phi => absurd h_phi h_not))`
- `modalK`: `intro h_box_imp h_box_phi w' hr; exact h_box_imp w' hr (h_box_phi w' hr)`

No frame conditions needed -- all cases are valid on arbitrary frames.

**k_soundness and k_soundness_derivable**: Direct instantiation of the parameterized `soundness` / `soundness_derivable` from Soundness.lean with `h_ax_sound := fun psi h_ax w => k_axiom_sound h_ax m w`.

### File 2: Metalogic/Soundness/T.lean (~60 lines)

**Purpose**: T soundness -- every TAxiom is valid on reflexive frames.

**Structure**:
```lean
theorem t_axiom_sound {World : Type*} {phi : Proposition Atom}
    (h_ax : TAxiom phi) (m : Model World Atom)
    (h_refl : forall w, m.r w w)
    (w : World) : Satisfies m w phi

theorem t_soundness {World : Type*}
    {Gamma : List (Proposition Atom)} {phi : Proposition Atom}
    (d : DerivationTree (@TAxiom Atom) Gamma phi)
    (m : Model World Atom) (h_refl : forall w, m.r w w)
    (w : World) (h_ctx : ...) : Satisfies m w phi

theorem t_soundness_derivable ...
```

**Proof approach for `t_axiom_sound`**: Case split; all propositional + modalK cases identical to K. New case:
- `modalT`: `intro h_box; exact h_box w (h_refl w)`

### File 3: Metalogic/Completeness/K.lean (~250 lines)

**Purpose**: K completeness -- valid on all frames implies K-derivable.

This is the most complex new file. It requires a K-specific box witness and truth lemma.

**Key new theorem: K-specific box witness**

The existing `mcs_box_witness` uses `h_T` in `derive_box_from_inconsistency`. For K, we need a version without `h_T`.

**Analysis of the `h_T` usage**: In `derive_box_from_inconsistency` (MCS.lean line 349-354), when `neg phi not in L`, all elements of `L` are from `{psi | box psi in S}`. The code currently does:
```lean
have h_all_S : forall x in L, x in S := by
  intro x hx
  rcases hL x hx with h | h
  · exact mcs_box_closure h_implyK h_implyS h_T h_mcs h  -- USES h_T
  · exact absurd (h ▸ hx) h_neg_in_L
exact h_mcs.1 L h_all_S ⟨d_bot⟩
```

This shows `L |- bot` with all of `L` in `S`, contradicting MCS consistency.

**K-specific alternative**: When `neg phi not in L`, all elements of `L` are `psi_i` with `box psi_i in S`. From `L |- bot`, we get `L |- phi` (via EFQ + MP: `bot -> phi` then MP). Then by `derive_box_from_box_context`, `box phi in S`, contradicting `h_not_box`.

```lean
theorem k_derive_box_from_inconsistency
    (h_implyK h_implyS h_efq h_peirce h_K)
    -- NO h_T parameter
    {S} (h_mcs) {phi} (h_not_box)
    {L} (hL) (d_bot) : False := by
  -- Same neg_phi-in-L branch as before (identical, doesn't use h_T)
  -- For neg_phi-not-in-L branch:
  --   all x in L have box x in S
  --   from d_bot : L |- bot, derive L |- phi via EFQ
  --   by derive_box_from_box_context: box phi in S
  --   contradiction with h_not_box
```

**Structure**:
```lean
-- K-specific box witness consistency helper
theorem k_derive_box_from_inconsistency ...

-- K-specific box witness
theorem k_mcs_box_witness
    (h_implyK h_implyS h_efq h_peirce h_K)
    -- NO h_T
    {S} (h_mcs) {phi} (h_not_box) :
    exists T, MCS T ∧ (forall psi, box psi in S -> psi in T) ∧ phi not in T

-- K-specific truth lemma
theorem k_truth_lemma
    (h_implyK h_implyS h_efq h_peirce h_K)
    -- NO h_T
    (S : CanonicalWorld KAxiom) :
    (phi : Proposition Atom) ->
    (Satisfies (CanonicalModel KAxiom) S phi <-> phi in S.val)

-- K completeness theorem
theorem k_completeness (phi : Proposition Atom)
    (h_valid : forall (World : Type u) (m : Model World Atom),
      forall w, Satisfies m w phi) :
    Derivable (@KAxiom Atom) phi
```

**Critical design decision**: The K truth lemma box case (`| .box phi`) has the same structure as the existing S5 truth lemma, but calls `k_mcs_box_witness` instead of `mcs_box_witness`.

**The `neg_phi in L` branch**: This branch of `derive_box_from_inconsistency` does NOT use `h_T` at all. It works by:
1. Separating `neg phi` from the rest of `L`
2. Using deduction theorem to get `L' |- neg phi -> bot` (i.e., `L' |- phi`)
3. Using derive_box_from_box_context to get `box phi in S`
4. Contradiction

This branch is identical in K and S5. The ONLY difference is the `neg_phi not in L` branch.

### File 4: Metalogic/Completeness/T.lean (~200 lines)

**Purpose**: T completeness -- valid on reflexive frames implies T-derivable.

**Structure**:
```lean
-- T canonical frame is reflexive (reuse existing canonical_refl)
theorem t_canonical_refl (S : CanonicalWorld TAxiom) :
    (CanonicalModel TAxiom).r S S

-- T truth lemma (can reuse existing truth_lemma!)
-- The existing truth_lemma takes h_T as parameter, which TAxiom provides

-- T completeness theorem
theorem t_completeness (phi : Proposition Atom)
    (h_valid : forall (World : Type u) (m : Model World Atom),
      (forall w, m.r w w) ->
      forall w, Satisfies m w phi) :
    Derivable (@TAxiom Atom) phi
```

**Key insight**: T completeness can REUSE the existing `truth_lemma` and `mcs_box_witness` from Completeness.lean/MCS.lean, since `TAxiom` includes both K and T axioms. The existing parameterized theorems accept explicit axiom hypotheses, and `TAxiom` provides all of them.

However, T completeness does NOT need `canonical_trans` or `canonical_eucl`. The proof structure is:

1. Assume phi is valid on all reflexive frames but not T-derivable.
2. Then `{neg phi}` is T-consistent.
3. Extend to MCS `w` by Lindenbaum.
4. The canonical model for TAxiom has a reflexive frame (by `canonical_refl` instantiated at TAxiom).
5. By the truth lemma, `M^T, w |= neg phi`.
6. But phi is valid on all reflexive frames, and M^T has a reflexive frame, so `M^T, w |= phi`.
7. Contradiction.

The completeness proof is simpler than S5's because we only need reflexivity, not transitivity or Euclideanness.

## Estimated Complexity

| File | New Code | Reuse | Risk |
|------|----------|-------|------|
| Soundness/K.lean | ~50 lines new | `soundness` from Soundness.lean | Low -- straightforward case splits |
| Soundness/T.lean | ~40 lines new | `soundness` from Soundness.lean | Low -- nearly identical to K |
| Completeness/K.lean | ~200 lines new | `CanonicalWorld`, `CanonicalModel`, `derive_box_from_box_context`, `iteratedDeduction`, `deductionTheorem`, MCS properties | Medium -- K-specific box witness is the main new work |
| Completeness/T.lean | ~150 lines new | `truth_lemma`, `mcs_box_witness`, `canonical_refl`, `CanonicalWorld`, `CanonicalModel` | Low -- heavy reuse of existing parameterized infrastructure |

**Total estimated**: ~440 lines of new Lean code.

## Risk Analysis

### Low Risk
- **Soundness proofs**: Direct case analysis on axiom constructors. No complex infrastructure needed.
- **T completeness**: Heavy reuse of existing parameterized infrastructure. The existing `truth_lemma` already takes `h_T` as an explicit parameter, so T completeness just instantiates it at `TAxiom.modalT`.

### Medium Risk
- **K box witness**: The key challenge is handling the else-branch of `derive_box_from_inconsistency` without `h_T`. The mathematical argument is simple (use EFQ to derive phi from bot, then box-lift), but the Lean encoding must carefully thread through `derive_box_from_box_context`.

### Mitigation
- The K box witness proof follows the standard textbook argument (all three sources confirm this).
- The existing `derive_box_from_box_context` and `iteratedDeduction` already handle the necessitation + K distribution step.
- The else-branch fix is ~20 lines of new code replacing ~5 lines of existing code.

## Module Graph Updates

The aggregator `Metalogic.lean` needs to import the new files. The new directory structure:

```
Metalogic/
  Soundness.lean          (existing -- S5 soundness)
  Soundness/
    K.lean                (new)
    T.lean                (new)
  Completeness.lean       (existing -- S5 completeness)
  Completeness/
    K.lean                (new)
    T.lean                (new)
```

**Import note**: `Soundness/K.lean` and `Soundness/T.lean` need to import `Metalogic.DerivationTree` and `ProofSystem.Instances` (for KAxiom/TAxiom). `Completeness/K.lean` and `Completeness/T.lean` need to import `Metalogic.MCS` and `Metalogic.Soundness` (for the parameterized soundness theorem, MCS machinery, and CanonicalWorld/CanonicalModel).

**IMPORTANT**: Lean 4 does not allow a file `Soundness.lean` and a directory `Soundness/` to coexist as siblings in the module hierarchy. The files `Soundness/K.lean` and `Soundness/T.lean` would define modules `Cslib.Logics.Modal.Metalogic.Soundness.K` and `Cslib.Logics.Modal.Metalogic.Soundness.T`, but the existing `Soundness.lean` is already `Cslib.Logics.Modal.Metalogic.Soundness`. This creates a conflict.

**Resolution options**:
1. **Rename new files**: Use `Metalogic/KSoundness.lean`, `Metalogic/TSoundness.lean`, `Metalogic/KCompleteness.lean`, `Metalogic/TCompleteness.lean` -- avoids all module conflicts.
2. **Nest within existing files**: Add K/T soundness to the existing Soundness.lean -- but this bloats the file.
3. **Create a Metalogic/Systems/ directory**: `Metalogic/Systems/K/Soundness.lean`, etc. -- cleaner but more directories.

**Recommended**: Option 1 (flat naming). Simple, avoids module conflicts, consistent with existing flat structure.

New files:
- `Metalogic/KSoundness.lean`
- `Metalogic/TSoundness.lean`
- `Metalogic/KCompleteness.lean`
- `Metalogic/TCompleteness.lean`

## Tactic Survey Results

The proofs in these files are primarily structural (case splits, intro/exact, constructor). The relevant tactics:

| Goal Type | Tactic | Expected Result |
|-----------|--------|-----------------|
| Axiom validity case splits | `cases h_ax` | Primary proof structure |
| Propositional axiom validity | `intro`/`exact`/`absurd` | Standard |
| K distribution validity | `intro`/`exact` | Direct from semantics |
| T axiom validity | `intro`/`exact` + reflexivity hyp | Direct |
| MCS membership | `exact mcs_mp_axiom ...` | Reuse existing |
| Box witness consistency | `classical` + case split | Following existing pattern |
| Truth lemma induction | Pattern match on `Proposition` | Following existing pattern |
| Completeness by contradiction | `by_contra` + Lindenbaum | Following existing S5 pattern |

No `simp`/`omega`/`aesop` needed -- these are structural proofs following the literature step-by-step.

## Summary

The task is well-scoped and achievable with zero sorries. The existing parameterized infrastructure (task 92) does most of the heavy lifting. The main new work is:

1. A K-specific box witness that avoids the axiom T dependency (medium difficulty, ~50 lines)
2. A K-specific truth lemma that uses the K box witness (follows existing pattern, ~80 lines)
3. K/T completeness theorems following the standard canonical model argument (~100 lines each)
4. K/T soundness by straightforward axiom validity case splits (~50 lines each)
