# Research Report: Soundness and Completeness for Modal Logic D

**Task**: 96 -- Establish soundness and completeness for modal logic D (serial frames)
**Date**: 2026-06-10
**Status**: Research findings ready for planning

## Literature Proof Structure

**Source**: Open Logic Project, "Normal Modal Logics" (rev 9f12419, 2026-05-25), Chapters 2-4.
Also: Blackburn, de Rijke, Venema "Modal Logic" (Cambridge, 2001), Chapter 4.
**Strategy**: Canonical model construction with seriality verification.

### Step Map

1. **D Soundness**: Axiom D valid on serial frames -- OLP Theorem 2.1
2. **Parameterized Soundness**: Reuse existing `soundness` theorem with D-specific axiom callback -- Soundness.lean
3. **Canonical Model Construction**: Worlds = MCS, R S T iff box^{-1}S subseteq T -- OLP Def 4.11
4. **Truth Lemma**: Satisfies(CanonicalModel, S, phi) iff phi in S -- OLP Prop 4.12
5. **Canonical Seriality**: The canonical model for KD is serial -- OLP Theorem 4.16
6. **Box Witness (K-style)**: If box phi not in S, exists MCS T with R S T and phi not in T -- existing `mcs_box_witness`
7. **Completeness Assembly**: Combine truth lemma + canonical seriality + contrapositive argument -- OLP Theorem 4.17

### Dependencies
- Step 2 depends on Step 1
- Steps 3, 4, 5, 6 are the canonical model argument
- Step 4 depends on Step 3
- Step 5 depends on Step 3 (and Lindenbaum)
- Step 7 depends on Steps 4, 5, 6

### Potential Formalization Challenges
- **Step 5** (seriality): Requires showing {psi | box psi in S} is consistent. The argument uses axiom D + NEC on tautology. Must adapt existing `derive_box_from_inconsistency` or build a new, simpler argument.
- **Step 6** (box witness): The existing `mcs_box_witness` takes `h_T` (axiom T). For D, we do NOT have axiom T, so we need a new version that does NOT use `mcs_box_closure`. The consistency proof for the witness set must use only axiom K (not T).
- **Step 4** (truth lemma): The existing truth lemma takes `h_T`. For D, we need a version without `h_T` that uses a different box witness.

## Existing Infrastructure Analysis

### What We Have (Reusable)

| Component | File | Reusable? | Notes |
|-----------|------|-----------|-------|
| `DAxiom` inductive | `ProofSystem/Instances.lean` | Yes | 6 constructors: implyK, implyS, efq, peirce, modalK, modalD |
| `DerivationTree DAxiom` | `DerivationTree.lean` | Yes | Parameterized, works with any axiom predicate |
| `modalDerivationSystem` | `DerivationTree.lean` | Yes | Generic over axiom predicate |
| `deductionTheorem` | `DeductionTheorem.lean` | Yes | Parameterized, needs only implyK + implyS |
| `modal_lindenbaum` | `MCS.lean` | Yes | Generic over axiom predicate |
| `modal_closed_under_derivation` | `MCS.lean` | Yes | Generic |
| `modal_negation_complete` | `MCS.lean` | Yes | Generic |
| `mcs_mp_axiom` | `MCS.lean` | Yes | Generic helper |
| `mcs_bot_not_mem` | `MCS.lean` | Yes | Generic |
| `mcs_neg_of_not_mem` | `MCS.lean` | Yes | Generic |
| `mcs_not_mem_of_neg` | `MCS.lean` | Yes | Generic |
| `mcs_mem_iff_neg_not_mem` | `MCS.lean` | Yes | Generic |
| `iteratedDeduction` | `MCS.lean` | Yes | Generic, needs implyK + implyS + K |
| `derive_box_from_box_context` | `MCS.lean` | Yes | Generic, needs implyK + implyS + K |
| `CanonicalWorld` | `Completeness.lean` | Yes | `{ S : Set (Proposition Atom) // Modal.SetMaximalConsistent Axioms S }` |
| `CanonicalModel` | `Completeness.lean` | Yes | R S T = forall phi, box phi in S -> phi in T |
| `Satisfies.d` | `Basic.lean` | Yes | D axiom valid on serial models |
| `Satisfies.d_serial` | `Basic.lean` | Yes | D valid in frame implies serial |
| `Relation.Serial` | `Relation.lean` | Yes | Class with `serial : Relator.LeftTotal r` |

### What We Need to Build

| Component | Why Different from S5 | Difficulty |
|-----------|----------------------|------------|
| `d_axiom_sound` | Cases on DAxiom (6 cases, not 8). Only needs seriality, not refl/trans/eucl. | Low |
| `d_soundness` | Wrapper combining `d_axiom_sound` with parameterized `soundness`. | Low |
| `canonical_serial` | Prove canonical model is serial. Key new theorem. Does NOT exist yet. | Medium |
| `mcs_box_witness_k` | Box witness WITHOUT axiom T. Uses K-style argument only. | Medium |
| `derive_box_from_inconsistency_k` | Inconsistency argument without T. | Medium |
| `truth_lemma_d` | Truth lemma without h_T parameter. Uses K-style box witness. | Medium |
| `d_completeness` | Assembly: contrapositive + canonical model + truth lemma + seriality. | Medium |

## Detailed Proof Analysis

### 1. D Soundness (`d_axiom_sound`)

```
theorem d_axiom_sound {World : Type*} {phi : Proposition Atom}
    (h_ax : DAxiom phi) (m : Model World Atom)
    (h_serial : Relation.Serial m.r)
    (w : World) : Satisfies m w phi
```

Case analysis on `DAxiom`:
- `implyK`, `implyS`, `efq`, `peirce`: Pure propositional, identical to S5.
- `modalK`: Same as S5 (needs no frame property).
- `modalD`: Use seriality. Given `box phi` at w, obtain witness w' from `h_serial.serial w`, then `phi` holds at w', so `diamond phi` holds at w. This is exactly `Satisfies.d`.

### 2. D Soundness Wrapper (`d_soundness`)

```
theorem d_soundness {World : Type*}
    {Gamma : List (Proposition Atom)} {phi : Proposition Atom}
    (d : DerivationTree DAxiom Gamma phi)
    (m : Model World Atom)
    (h_serial : Relation.Serial m.r)
    (w : World)
    (h_ctx : forall psi in Gamma, Satisfies m w psi) : Satisfies m w phi :=
  soundness d m (fun psi h_ax w => d_axiom_sound h_ax m h_serial w) w h_ctx
```

### 3. Canonical Seriality (`canonical_serial`)

**This is the key new theorem.**

```
theorem canonical_serial
    {Axioms : Proposition Atom -> Prop}
    (h_implyK : ...)
    (h_implyS : ...)
    (h_efq : ...)
    (h_K : ...)
    (h_D : forall phi, Axioms (box phi -> diamond phi))
    (S : CanonicalWorld Axioms) :
    exists T : CanonicalWorld Axioms, (CanonicalModel Axioms).r S T
```

**Proof sketch** (from OLP Theorem 4.16):

1. Let W = {psi | box psi in S.val} (the "box-unboxing" of S).
2. Show W is consistent (Modal.SetConsistent Axioms W).
3. By Lindenbaum, extend W to MCS T.
4. Then (CanonicalModel Axioms).r S T (by construction: box psi in S -> psi in W subseteq T).

**Consistency of W** (by contradiction):
- Suppose W is inconsistent, i.e., there exist psi_1, ..., psi_n in W with psi_1, ..., psi_n |-_Axioms bot.
- Since each psi_i in W means box psi_i in S, by `derive_box_from_box_context` we get box bot in S.
- By axiom D instantiated at bot: box bot -> diamond bot. Since box bot in S, diamond bot in S.
- diamond bot = (box(bot -> bot)) -> bot.
- bot -> bot is derivable (from propositional axioms), so by NEC, box(bot -> bot) is derivable, so box(bot -> bot) in S.
- By MP: bot in S. Contradiction with `mcs_bot_not_mem`.

**Implementation note**: This does NOT need `h_T` (axiom T) at all. It only needs:
- `h_implyK`, `h_implyS` (for deduction theorem / closed_under_derivation)
- `h_K` (for `derive_box_from_box_context` / `mcs_box_mp`)
- `h_D` (the D axiom instance)
- `h_efq` (for deriving bot -> bot, or we can derive it from implyK)

### 4. Box Witness for D (`mcs_box_witness_k`)

The existing `mcs_box_witness` in MCS.lean uses `h_T` in the `derive_box_from_inconsistency` helper. Specifically, the line:
```
    exact mcs_box_closure h_implyK h_implyS h_T h_mcs h
```
handles the case where `neg phi` is NOT in L (all elements of L are directly in S via T-closure).

**For D, we need a version that does NOT use T.** The approach:

The witness set is W = {psi | box psi in S} union {neg phi}. To show W is consistent, suppose L subseteq W and L |- bot. Partition L into:
- L' = L \ {neg phi} (elements from {psi | box psi in S})
- The neg phi part

If neg phi is NOT in L: All elements of L are in {psi | box psi in S}. We need to show these are jointly consistent. Since all box psi_i in S, by `derive_box_from_box_context`, box bot in S. Then apply axiom D to get diamond bot in S, and derive contradiction as above.

Wait -- this is different. If neg phi not in L, all of L are psi with box psi in S. If they derive bot, then box bot in S. Apply D: diamond bot in S. But diamond bot = (box(bot->bot))->bot. Since bot->bot is derivable, box(bot->bot) in S. So bot in S. Contradiction.

If neg phi IS in L: Filter it out to get L'. From L' and neg phi, we derive bot. By deduction theorem, L' |- neg phi -> bot. By further propositional reasoning, L' |- phi. Then box phi in S (by `derive_box_from_box_context`). But we assumed box phi not in S. Contradiction.

**Wait**: that second case is EXACTLY the existing `derive_box_from_inconsistency` pattern, except the "all in S" fallback. In the S5 version, the fallback uses `mcs_box_closure` (T axiom) to put elements of L directly into S. For D, the fallback should use the D+NEC argument instead.

Actually, re-examining `derive_box_from_inconsistency` more carefully:

```lean
  · have h_all_S : ∀ x ∈ L, x ∈ S := by
      intro x hx
      rcases hL x hx with h | h
      · exact mcs_box_closure h_implyK h_implyS h_T h_mcs h  -- USES T!
      · exact absurd (h ▸ hx) h_neg_in_L
    exact h_mcs.1 L h_all_S ⟨d_bot⟩
```

When neg phi not in L, all elements satisfy box x in S, and then we apply T to get x in S, making L a subset of S. Then L |- bot contradicts consistency of S.

For D, we cannot go from "box x in S" to "x in S" (no T axiom). Instead:
- All elements of L are psi with box psi in S.
- L |- bot.
- By `derive_box_from_box_context`: box bot in S.
- Then the D+NEC argument gives contradiction.

This is a cleaner approach -- we don't even need to partition. The argument is:

**New `derive_box_from_inconsistency_d`**: Given L |- bot where all x in L satisfy box x in S (or x = neg phi), we can get a contradiction by:
1. If neg phi in L: deduction theorem + propositional reasoning gives L' |- phi, then `derive_box_from_box_context` gives box phi in S, contradicting assumption.
2. If neg phi not in L: All of L are {psi | box psi in S}. L |- bot. `derive_box_from_box_context` gives box bot in S. D gives diamond bot in S. NEC on tautology gives box(bot->bot) in S. MP gives bot in S. Contradiction.

### 5. Truth Lemma for D

The existing truth lemma has signature:
```lean
theorem truth_lemma ... (h_T : ...) ...
```

For D, we need a version WITHOUT `h_T`. The truth lemma's box case uses:
```lean
  | .box phi => by
    constructor
    · intro h_sat
      by_contra h_not_box
      obtain ⟨T, hT_mcs, hST, h_phi_not_T⟩ :=
        mcs_box_witness h_implyK h_implyS h_efq h_peirce h_K h_T
          S.property h_not_box
      ...
```

The call to `mcs_box_witness` passes `h_T`. For D, we need `mcs_box_witness_d` that uses `h_D` instead. The rest of the truth lemma is identical.

**Alternative approach**: Refactor the truth lemma to take the box witness as a parameter/callback. This would allow both S5 and D to use the same truth lemma with different witness strategies.

**Recommended approach**: Create a new `truth_lemma_k` that takes the box witness as a hypothesis rather than `h_T`:

```lean
theorem truth_lemma_k
    (h_implyK : ...) (h_implyS : ...) (h_efq : ...) (h_peirce : ...)
    (h_K : ...)
    (h_witness : forall (S : CanonicalWorld Axioms) (phi : Proposition Atom),
      box phi not in S.val ->
      exists T, SetMaximalConsistent Axioms T wedge
        (forall psi, box psi in S.val -> psi in T) wedge phi not in T)
    (S : CanonicalWorld Axioms) :
    (phi : Proposition Atom) ->
    (Satisfies (CanonicalModel Axioms) S phi <-> phi in S.val)
```

Then both S5 and D can instantiate the witness parameter differently.

### 6. Completeness Assembly

```lean
theorem d_completeness (phi : Proposition Atom)
    (h_valid : forall (World : Type u) (m : Model World Atom),
      Relation.Serial m.r ->
      forall w, Satisfies m w phi) :
    Derivable DAxiom phi
```

Proof by contradiction:
1. Assume `not (Derivable DAxiom phi)`.
2. Then `{neg phi}` is DAxiom-consistent (same argument as S5 completeness).
3. By Lindenbaum, extend to MCS M containing neg phi.
4. Let w = (M, hM_mcs) : CanonicalWorld DAxiom.
5. Show canonical model is serial: `canonical_serial` gives seriality.
6. Apply h_valid to canonical model: `Satisfies (CanonicalModel DAxiom) w phi`.
7. By truth lemma: phi in M.
8. But neg phi in M, so bot in M. Contradiction with `mcs_bot_not_mem`.

## File Structure Recommendation

```
Cslib/Logics/Modal/Metalogic/
  Soundness/
    D.lean        -- d_axiom_sound, d_soundness, d_soundness_derivable
  Completeness/
    D.lean        -- canonical_serial, mcs_box_witness_d, truth_lemma_d, d_completeness
```

Or alternatively, to keep closer to existing structure:
```
Cslib/Logics/Modal/Metalogic/
  Soundness.lean  -- (existing, for S5)
  Completeness.lean -- (existing, for S5)
  Soundness/
    D.lean
  Completeness/
    D.lean
```

The Metalogic.lean module aggregator would need to import these new files.

## Risk Assessment

| Risk | Likelihood | Mitigation |
|------|-----------|------------|
| Truth lemma refactoring breaks S5 | Low | Create new `truth_lemma_k` alongside existing, don't modify S5 |
| Box witness K-style argument is complex | Medium | Follow existing pattern closely, only change the T-fallback case |
| Seriality proof involves NEC on tautology | Low | Standard construction, well-tested pattern |
| Universe polymorphism issues | Low | Follow existing S5 pattern exactly |

## Estimated Complexity

- **Soundness (d_axiom_sound + wrapper)**: ~50 lines. Straightforward case analysis.
- **Canonical seriality**: ~40-60 lines. Key new theorem.
- **Box witness for D**: ~80-100 lines. Adaptation of existing `mcs_box_witness` + `derive_box_from_inconsistency`.
- **Truth lemma for D**: ~100-120 lines. Mostly copy of existing with modified box case.
- **Completeness assembly**: ~60-80 lines. Close adaptation of S5 completeness.
- **Total**: ~350-450 lines across two new files.

## Key Differences from S5

| Aspect | S5 | D |
|--------|----|----|
| Frame property | Reflexive + Transitive + Euclidean | Serial |
| Axioms used | K, T, 4, B | K, D |
| Canonical frame proof | `canonical_refl`, `canonical_trans`, `canonical_eucl` | `canonical_serial` only |
| Box witness consistency | Uses T (mcs_box_closure) for fallback | Uses D + NEC for fallback |
| Truth lemma | Passes h_T | Does not use h_T, uses different witness |
| Completeness | 3 frame conditions to verify | 1 frame condition (seriality) |

## Summary

The D soundness and completeness proof follows the standard canonical model construction but is structurally simpler than S5 because:
1. Only one frame property (seriality) to verify, not three.
2. The seriality proof is more elegant -- it uses the D axiom to derive a contradiction from box bot.
3. The key challenge is adapting the box witness / truth lemma to work WITHOUT axiom T.

The proof is entirely standard in the modal logic literature and maps cleanly to the existing Lean infrastructure. No sorry deferral should be needed.
