# Research Report: Modal K45 Soundness and Completeness

## Task 104 — Modal K45 (K + 4 + 5) over Transitive + Euclidean Frames

### Summary

K45 is the normal modal logic axiomatized by K + axiom 4 (`box phi -> box box phi`) + axiom 5 (`diamond phi -> box diamond phi`), complete with respect to the class of transitive and Euclidean frames. K45 has NO axiom T, which is the critical distinction from S4/S5.

---

## Literature Proof Structure

**Source**: Blackburn, de Rijke, Venema (2002). *Modal Logic*. Ch. 4, Theorems 4.27, 4.29, Definition 4.30.

**Strategy**: Completeness-via-canonicity. Each axiom is canonical (its presence in a logic guarantees the canonical frame has the corresponding property). Since K45 contains both 4 and 5, its canonical frame is transitive and Euclidean.

### Step Map

1. **Axiom 4 canonical for transitivity** -- BRV Theorem 4.27
   - If R(w,v) and R(v,u) and phi in u, then diamond phi in v (by R(v,u)), diamond diamond phi in w (by R(w,v)), axiom 4 gives diamond phi in w. So R(w,u).
   - Formalized as `canonical_trans` in `Completeness.lean`

2. **Axiom 5 canonical for Euclideanness** -- BRV implied by Definition 4.30 and task description
   - If R(w,v) and R(w,u) and phi in u, then diamond phi in w (by R(w,u)), box diamond phi in w (by axiom 5 + MP), diamond phi in v (by R(w,v)). Hence R(v,u).
   - NOT yet formalized. Task 100 will provide `canonical_eucl_from_5`.

3. **Soundness: axiom 4 valid on transitive frames** -- BRV Table 4.1
   - `Satisfies.four` in `Basic.lean` (line 301): proves `diamond diamond phi -> diamond phi` on transitive frames
   - For K45 soundness in Hilbert style: need `box phi -> box box phi` on transitive frames (handled by `modalFour` case in `s4_axiom_sound`)

4. **Soundness: axiom 5 valid on Euclidean frames** -- BRV Table 4.1
   - `Satisfies.five` in `Basic.lean` (line 329): proves `diamond phi -> box diamond phi` on Euclidean frames
   - For K45 soundness: the `modalFive` case validates the 5 schema

5. **K45 uses k_truth_lemma (not truth_lemma)** -- Critical structural choice
   - K45 has NO axiom T, so `mcs_box_witness` (which requires `h_T`) cannot be used
   - Must use `k_mcs_box_witness` from `KCompleteness.lean` (BRV Lemma 4.20 for K)
   - This gives `k_truth_lemma` which only needs: implyK, implyS, efq, peirce, modalK

6. **Composition** -- BRV Theorem 4.29 pattern (generalized)
   - K45 completeness = k_truth_lemma + canonical_trans + canonical_eucl_from_5
   - Analogous to S4 completeness = truth_lemma + canonical_refl + canonical_trans

### Dependencies

- Step 6 depends on Steps 1, 2, and 5
- Step 5 is independent (already in codebase)
- Steps 3, 4 are independent (already in codebase)
- Step 2 depends on task 100 (`canonical_eucl_from_5`)

### Potential Formalization Challenges

- **Step 2**: `canonical_eucl_from_5` does not yet exist; task 100 must provide it. The proof needs a different argument from `canonical_eucl` (which uses B + T + 4).
- **Step 5**: `k_truth_lemma` already exists and needs no modification.
- **Axiom 5 encoding**: The formula `diamond phi -> box diamond phi` where `diamond phi = neg box neg phi` requires careful handling of the encoding in the axiom predicate.

---

## Research Findings

### 1. K45Axiom Predicate (to be created)

Following the established pattern from `KAxiom`, `S4Axiom`, etc., we need:

```lean
inductive K45Axiom : Proposition Atom -> Prop where
  | implyK (phi psi : Proposition Atom) :
      K45Axiom (Proposition.imp phi (Proposition.imp psi phi))
  | implyS (phi psi chi : Proposition Atom) :
      K45Axiom (Proposition.imp (Proposition.imp phi (Proposition.imp psi chi))
        (Proposition.imp (Proposition.imp phi psi) (Proposition.imp phi chi)))
  | efq (phi : Proposition Atom) :
      K45Axiom (Proposition.imp Proposition.bot phi)
  | peirce (phi psi : Proposition Atom) :
      K45Axiom (Proposition.imp (Proposition.imp (Proposition.imp phi psi) phi) phi)
  | modalK (phi psi : Proposition Atom) :
      K45Axiom (Proposition.imp (Proposition.box (Proposition.imp phi psi))
        (Proposition.imp (Proposition.box phi) (Proposition.box psi)))
  | modalFour (phi : Proposition Atom) :
      K45Axiom (Proposition.imp (Proposition.box phi)
        (Proposition.box (Proposition.box phi)))
  | modalFive (phi : Proposition Atom) :
      K45Axiom (Proposition.imp (Proposition.diamond phi)
        (Proposition.box (Proposition.diamond phi)))
```

7 constructors: 4 propositional + 3 modal (K, 4, 5). NO modalT.

### 2. K45 Soundness Structure

File: `K45Soundness.lean`

```lean
theorem k45_axiom_sound {World : Type*} {phi : Proposition Atom}
    (h_ax : K45Axiom phi) (m : Model World Atom)
    (h_trans : forall w1 w2 w3, m.r w1 w2 -> m.r w2 w3 -> m.r w1 w3)
    (h_eucl : forall w1 w2 w3, m.r w1 w2 -> m.r w1 w3 -> m.r w2 w3)
    (w : World) : Satisfies m w phi
```

Cases:
- `implyK`, `implyS`, `efq`, `peirce`, `modalK`: Same as K (no frame conditions needed)
- `modalFour`: Uses transitivity (`h_trans`). Proof: `intro h_box w1 hr1 w2 hr2; exact h_box w2 (h_trans w w1 w2 hr1 hr2)`
- `modalFive`: Uses Euclideanness (`h_eucl`). Proof follows `Satisfies.five` pattern: given `diamond phi` at w, for any w' with R(w,w'), use Euclideanness to transfer the witness.

The `modalFive` case handles axiom 5 = `diamond phi -> box diamond phi`:
```lean
| modalFive phi =>
    -- Goal: Satisfies m w (diamond phi -> box diamond phi)
    -- Unfolded: (exists w', R w w' /\ sat w' phi) ->
    --           forall v, R w v -> exists u, R v u /\ sat u phi
    intro hdiam w' hr
    -- hdiam gives us witness u with R(w,u) and sat(u,phi)
    -- From R(w,w') and R(w,u), Euclidean gives R(w',u)
    -- So we have witness u for diamond phi at w'
    simp only [Satisfies] at hdiam |-
    intro h_box_neg
    apply hdiam
    intro u hru hsat_phi
    -- From h_eucl: R(w,w') and R(w,u) gives R(w',u)
    exact h_box_neg u (h_eucl w w' u hr hru) hsat_phi
```

Actually, reviewing the concrete encoding more carefully: `diamond phi = neg (box (neg phi)) = (box (phi -> bot)) -> bot`. So `Satisfies m w (diamond phi)` = `Satisfies m w ((box (phi -> bot)) -> bot)` = `(forall w', R w w' -> (Satisfies m w' phi -> False)) -> False`.

And `box (diamond phi)` = `forall w', R w w' -> Satisfies m w' (diamond phi)` = `forall w', R w w' -> ((forall u, R w' u -> (Satisfies m u phi -> False)) -> False)`.

So the soundness of axiom 5 unfolds to:
```
Given: ((forall w', R w w' -> sat w' phi -> False) -> False)
Show:  forall v, R w v -> ((forall u, R v u -> sat u phi -> False) -> False)
```

The proof:
```lean
| modalFive phi =>
    intro hdiam v hrv hbox_neg_v
    apply hdiam
    intro u hru hsat
    exact hbox_neg_v u (h_eucl w v u hrv hru) hsat
```

This matches the `Satisfies.five` proof pattern exactly.

### 3. K45 Completeness Structure

File: `K45Completeness.lean`

The completeness theorem for K45 follows the K completeness pattern (contrapositive) but adds two frame property verifications:

```lean
theorem k45_completeness (phi : Proposition Atom)
    (h_valid : forall (World : Type u) (m : Model World Atom),
      (forall w1 w2 w3, m.r w1 w2 -> m.r w2 w3 -> m.r w1 w3) ->
      (forall w1 w2 w3, m.r w1 w2 -> m.r w1 w3 -> m.r w2 w3) ->
      forall w, Satisfies m w phi) :
    Derivable (@K45Axiom Atom) phi
```

Proof structure:
1. Contrapositive: assume not derivable
2. `{neg phi}` is K45-consistent (same DNE argument as k_completeness)
3. Lindenbaum: extend to MCS M
4. Canonical world: `w := (M, hM_mcs) : CanonicalWorld K45Axiom`
5. Apply `k_truth_lemma` (no axiom T needed!) with K45Axiom constructor witnesses
6. Show canonical frame is transitive via `canonical_trans` (from `.modalFour`)
7. Show canonical frame is Euclidean via `canonical_eucl_from_5` (from `.modalFive`)
8. Contradiction via `mcs_not_mem_of_neg`

Key instantiations:
```lean
-- k_truth_lemma witnesses
(fun phi psi => .implyK phi psi)
(fun phi psi chi => .implyS phi psi chi)
(fun phi => .efq phi)
(fun phi psi => .peirce phi psi)
(fun phi psi => .modalK phi psi)

-- canonical_trans witness
(fun phi => .modalFour phi)

-- canonical_eucl_from_5 witness (from task 100)
(fun phi => .modalFive phi)
```

### 4. canonical_eucl_from_5 — The Critical Dependency (Task 100)

This lemma must prove that axiom 5 alone gives Euclideanness of the canonical relation. The expected signature:

```lean
theorem canonical_eucl_from_5
    {Axioms : Proposition Atom -> Prop}
    (h_implyK : forall (phi psi : Proposition Atom), Axioms (phi.imp (psi.imp phi)))
    (h_implyS : forall (phi psi chi : Proposition Atom),
      Axioms ((phi.imp (psi.imp chi)).imp ((phi.imp psi).imp (phi.imp chi))))
    (h_K : forall (phi psi : Proposition Atom),
      Axioms ((Proposition.box (phi.imp psi)).imp
        ((Proposition.box phi).imp (Proposition.box psi))))
    (h_5 : forall (phi : Proposition Atom),
      Axioms ((Proposition.diamond phi).imp
        (Proposition.box (Proposition.diamond phi))))
    (S T U : CanonicalWorld Axioms) :
    (CanonicalModel Axioms).r S T ->
    (CanonicalModel Axioms).r S U ->
    (CanonicalModel Axioms).r T U
```

Proof sketch (following BRV):
- Assume R(S,T) and R(S,U). Want R(T,U), i.e., for all phi, box phi in T implies phi in U.
- Take phi with box phi in T. Want phi in U.
- We know R(S,U), so suffices to show box phi in S.
- Since box phi in T and R(S,T), we'd need box box phi in S...
- Actually, the correct BRV argument for 5:
  - Assume R(S,T), R(S,U), and phi in U. We want diamond phi in T.
  - From phi in U and R(S,U): diamond phi in S (by canonical relation definition -- actually by the *reverse* direction, we know that for all psi, box psi in S -> psi in U; we need diamond phi in S from phi in U and R(S,U))
  
Wait, let me reconsider the canonical relation. The canonical relation is: `R S T iff forall phi, box phi in S -> phi in T`. This is NOT the same as "phi in T implies diamond phi in S". Those are different directions.

For Euclidean property from axiom 5, the correct argument:
- Given R(S,T) and R(S,U), show R(T,U), i.e., for all phi, box phi in T -> phi in U.
- Take phi with box phi in T.
- Want: phi in U.
- From R(S,T): for all psi, box psi in S -> psi in T.
- From R(S,U): for all psi, box psi in S -> psi in U.
- Since box phi in T, by axiom 4 on T, box box phi in T... but T is just an MCS of K45, not necessarily S.

Actually the standard proof for axiom 5 giving Euclideanness uses a *different* argument. Let me re-derive:

Axiom 5 says: `diamond phi -> box diamond phi` (= `neg box neg phi -> box neg box neg phi`).

**Correct argument**: Suppose R(S,T) and R(S,U). Show R(T,U), i.e., for all psi, box psi in T -> psi in U.

Take psi such that box psi in T. By contrapositive, if psi not in U, then neg psi in U (since U is MCS), then diamond neg psi in S (since R(S,U) and neg psi in U means... wait, that's also not directly the canonical relation).

Let me think again about the canonical relation: `R(S,T)` means `forall phi, box phi in S -> phi in T`. 

The equivalent characterization (BRV Lemma 4.19) is: `R(S,T) iff forall psi, psi in T -> diamond psi in S`.

Using this second characterization:
- R(S,T): for all psi, psi in T -> diamond psi in S
- R(S,U): for all psi, box psi in S -> psi in U
- Want R(T,U): for all phi, box phi in T -> phi in U

Proof: Take box phi in T. Then box phi in T means "box phi is in T" (a set membership). By the first direction of R(S,T) (canonical relation), we need to show phi in U. 

Actually, the standard proof is:
- Take box phi in T. From box phi in T, by axiom 4 in T (since T is a K45-MCS containing axiom 4): box box phi in T.
- Wait, but if we're proving `canonical_eucl_from_5`, we might not assume axiom 4.

Let me look at this more carefully. The existing `canonical_eucl` uses B + T + 4. We need `canonical_eucl_from_5` which uses ONLY axiom 5 (plus K for box manipulation).

**Proof using axiom 5 alone**:
- Suppose R(S,T) and R(S,U). Show R(T,U).
- Take phi such that box phi in T. Want phi in U.
- By contraposition: assume phi not in U.
- Since U is MCS: neg phi in U.
- Since R(S,U) uses characterization: for all psi, box psi in S -> psi in U.
- Equivalently (by contraposition on individual psi): psi not in U -> box psi not in S -> (since S is MCS) neg box psi in S -> diamond (neg psi)... 

No wait. The cleaner approach: use the *diamond characterization* of the canonical relation.

Actually the standard textbook proof uses: R(w,v) iff {phi | box phi in w} subset v.

For Euclideanness from 5: Assume R(S,T) and R(S,U). Take phi in U. Want to show diamond phi in T (which is equivalent to R(T,U) by the diamond characterization).

- phi in U and R(S,U) (diamond characterization): diamond phi in S.
  - Wait, R(S,U) means box psi in S -> psi in U. The diamond characterization says R(w,v) iff for all psi, psi in v -> diamond psi in w. Are these equivalent?
  - YES! If box psi in S -> psi in U, and phi in U, does diamond phi in S follow? Not directly from R(S,U). The diamond characterization is: R(w,v) iff for all psi, psi in v -> diamond psi in w. This is indeed equivalent to box psi in w -> psi in v (for MCS).

Let me verify: Suppose R(S,U) (i.e., box psi in S -> psi in U for all psi). Take phi in U. By contraposition: if diamond phi not in S, then box neg phi in S (since S is MCS and diamond phi = neg box neg phi), then neg phi in U (by R(S,U)), contradicting phi in U. So diamond phi in S.

Good! So from R(S,U) and phi in U: diamond phi in S.

Now:
- diamond phi in S (from above)
- S is K45-MCS, so axiom 5 instance `diamond phi -> box diamond phi` is in S
- By MP: box diamond phi in S
- R(S,T) means box psi in S -> psi in T
- So diamond phi in T
- This holds for all phi in U, establishing R(T,U).

This is the CORRECT proof and matches the task description's claim.

### 5. Axiom 5 Formula Encoding

In the codebase, `Proposition.diamond phi = neg (box (neg phi)) = imp (box (imp phi bot)) bot`.

So axiom 5 = `diamond phi -> box diamond phi` = `imp (diamond phi) (box (diamond phi))`:
```lean
Proposition.imp
  (Proposition.imp (Proposition.box (Proposition.imp phi Proposition.bot)) Proposition.bot)
  (Proposition.box
    (Proposition.imp (Proposition.box (Proposition.imp phi Proposition.bot)) Proposition.bot))
```

This matches `Axioms.Axiom5` from `Foundations/Logic/Axioms.lean` (line 112).

### 6. MCS Lemma Needed: mcs_diamond_from_5

For `canonical_eucl_from_5`, we need a helper analogous to `mcs_box_diamond` (axiom B) but for axiom 5:

```lean
/-- If diamond phi in S and S is MCS with axiom 5, then box diamond phi in S. -/
theorem mcs_box_diamond_from_5
    (h_implyK) (h_implyS) (h_5)
    (h_mcs : Modal.SetMaximalConsistent Axioms S)
    (h_diam : Proposition.diamond phi in S) :
    Proposition.box (Proposition.diamond phi) in S :=
  mcs_mp_axiom h_implyK h_implyS h_mcs h_diam (h_5 phi)
```

This is a one-liner using `mcs_mp_axiom`.

### 7. File Dependencies

**K45Soundness.lean** depends on:
- `Cslib.Logics.Modal.Metalogic.Soundness` (parameterized soundness)
- `Cslib.Logics.Modal.ProofSystem.Instances` (K45Axiom definition -- needs to be added here OR in a new Instances extension)

**K45Completeness.lean** depends on:
- `Cslib.Logics.Modal.Metalogic.KCompleteness` (k_truth_lemma, k_mcs_box_witness)
- `Cslib.Logics.Modal.Metalogic.Completeness` (canonical_trans, CanonicalModel, CanonicalWorld)
- Task 100's `canonical_eucl_from_5` (BLOCKER if not available)

### 8. Task 100 Dependency Analysis

Task 100 will provide:
- `canonical_eucl_from_5` theorem in `Completeness.lean` (or a new file)
- `K45Axiom` inductive type in `ProofSystem/Instances.lean`
- `Modal.HilbertK45` tag type
- Typeclass instances for K45

**If task 100 is not completed first**, task 104 can still proceed by:
1. Defining `K45Axiom` locally in the soundness/completeness files
2. Proving `canonical_eucl_from_5` inline (it's not that long -- ~15 lines)
3. This avoids a hard blocker while maintaining zero-sorry policy

### 9. Pattern Match: K45 vs S4

| Aspect | S4 | K45 |
|--------|----|----|
| Axioms | K + T + 4 | K + 4 + 5 |
| Frame class | Reflexive + Transitive | Transitive + Euclidean |
| Has axiom T? | YES | NO |
| Truth lemma | `truth_lemma` (uses T) | `k_truth_lemma` (no T) |
| Box witness | `mcs_box_witness` (uses T) | `k_mcs_box_witness` (no T) |
| canonical_refl | YES (from T) | NO |
| canonical_trans | YES (from 4) | YES (from 4) |
| canonical_eucl | NO | YES (from 5, via `canonical_eucl_from_5`) |
| Soundness cases | 7 (implyK,S,efq,peirce,K,T,4) | 7 (implyK,S,efq,peirce,K,4,5) |

---

## Tactic Survey Results

Based on the existing patterns in S4Soundness/S4Completeness:

| Goal | Approach | Notes |
|------|----------|-------|
| Propositional axiom cases | Direct `intro` + `exact` | Same as KSoundness |
| modalK case | Direct `intro` + `exact` | Same as KSoundness |
| modalFour case | `intro h_box w1 hr1 w2 hr2; exact h_box w2 (h_trans ...)` | Same as S4 |
| modalFive case | Pattern from `Satisfies.five` with `h_eucl` | ~4 lines |
| k_truth_lemma instantiation | Direct constructor application | Same pattern as k_completeness |
| canonical_trans instantiation | `(fun phi => .modalFour phi)` | Same as S4 |
| canonical_eucl_from_5 instantiation | `(fun phi => .modalFive phi)` | New |
| Consistency proof | DNE via Peirce (boilerplate) | Copy from k_completeness |

---

## Blockers

| Blocker | Severity | Mitigation |
|---------|----------|------------|
| Task 100 not started (canonical_eucl_from_5) | Medium | Can be proved inline (~15 lines); or proceed with task 100 first |
| K45Axiom not yet defined | Low | Define in ProofSystem/Instances.lean following established pattern |
| No HilbertK45 tag type | Low | Task 100 scope; can define inline for soundness/completeness |

**Recommendation**: Task 104 is NOT hard-blocked. The `canonical_eucl_from_5` proof is straightforward and can be included in K45Completeness.lean directly. The K45Axiom definition is ~15 lines of boilerplate. Proceed to planning.

---

## Implementation Recommendations

1. **K45Axiom definition**: Add to `ProofSystem/Instances.lean` (7 constructors, following S4Axiom pattern)
2. **K45Soundness.lean**: ~50 lines, follow S4Soundness pattern but with `h_trans` + `h_eucl` instead of `h_refl` + `h_trans`
3. **K45Completeness.lean**: ~80 lines, follow KCompleteness pattern (k_truth_lemma) + add canonical frame property proofs
4. **canonical_eucl_from_5**: Either in shared Completeness.lean (if task 100 is done) or inline in K45Completeness.lean (~20 lines)
5. **Register in Metalogic.lean barrel file**: Add imports for K45Soundness and K45Completeness
