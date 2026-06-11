# Research Report: Modal KB5 Soundness and Completeness

## Task 106: Prove Soundness and Completeness for KB5

### Summary

KB5 = K + B + 5 is the normal modal logic axiomatized by the K distribution axiom, the B symmetry axiom (`phi -> box(diamond phi)`), and the 5 Euclidean axiom (`diamond phi -> box(diamond phi)`). Its frame class is symmetric + Euclidean frames (Blackburn Table 4.1 extended). This is the **first logic in the cube requiring both new canonical lemmas** (`canonical_symm` from B alone, and `canonical_eucl_from_5` from 5 alone) introduced by task 100.

**Key insight**: KB5 does NOT have axiom T. Therefore:
- Soundness uses `Satisfies.b` (symmetry) + `Satisfies.five` (Euclidean) -- no reflexivity needed
- Completeness uses `k_truth_lemma` (K-style, no axiom T) -- NOT the S5 `truth_lemma`
- The canonical frame properties proved are symmetry (via `canonical_symm`) and Euclideanness (via `canonical_eucl_from_5`)

---

## Literature Proof Structure

**Source**: Blackburn, de Rijke, Venema. *Modal Logic* (2002), Chapter 4.
**Strategy**: Completeness-via-canonicity (Definition 4.30, combining Theorems 4.23, 4.28 clause 2, and a new clause for axiom 5).

### Step Map

1. **KB5Axiom predicate** -- Define inductive type with 7 constructors (4 propositional + 3 modal: K, B, 5)
2. **KB5 Soundness** -- Verify each axiom is valid on symmetric + Euclidean frames (BRV Definition 4.9)
3. **canonical_symm** -- Prove canonical frame is symmetric from axiom B alone (BRV Theorem 4.28 clause 2)
4. **canonical_eucl_from_5** -- Prove canonical frame is Euclidean from axiom 5 alone (analogous to Theorem 4.27 for transitivity)
5. **k_truth_lemma instantiation** -- Reuse existing K-specific Truth Lemma (BRV Lemma 4.21 for K) since KB5 has no axiom T
6. **KB5 Completeness** -- Contrapositive argument: not derivable => consistent => Lindenbaum => canonical model satisfies neg phi => frame is symmetric + Euclidean => validity gives phi => contradiction (BRV Theorem 4.22 pattern)

### Dependencies
- Steps 3 and 4 depend on task 100 infrastructure (canonical_symm, canonical_eucl_from_5)
- Step 5 depends on the existing `k_truth_lemma` (already in `KCompleteness.lean`)
- Step 6 depends on Steps 3, 4, and 5
- Step 2 is independent (uses `Satisfies.b` and `Satisfies.five` from `Basic.lean`)

### Potential Formalization Challenges
- **Step 3**: `canonical_symm` must work with B alone (no T, no 4). The BRV proof (Theorem 4.28 clause 2) is straightforward: Rwv => phi in w => box(diamond phi) in w (axiom B) => diamond phi in v (by canonical relation) => Rvw.
- **Step 4**: `canonical_eucl_from_5` is analogous. Proof: Rwv and Rwu => phi in u (supposition for canonical relation T U) ... The key insight: from axiom 5, `diamond phi -> box(diamond phi)`. If Rwv and Rwu and phi in u, then diamond phi in w (by Rwu + canonical relation), then box(diamond phi) in w (by axiom 5 + MCS closure), then diamond phi in v (by Rwv + canonical relation). This shows Rvu, i.e., Euclidean.
- **Step 5**: The K-specific truth lemma has no `h_T` hypothesis, which is exactly what KB5 needs. Direct reuse.

---

## 1. KB5Axiom Predicate

### Design

Following the pattern of `KAxiom`, `TAxiom`, `DAxiom`, `S4Axiom` in `Instances.lean`:

```lean
/-- Axiom schemata for modal logic KB5.
The 7 axiom constructors cover:
- Propositional (4): implyK, implyS, efq, peirce
- Modal (3): modalK, modalB, modalFive -/
inductive KB5Axiom : Proposition Atom -> Prop where
  | implyK (phi psi : Proposition Atom) :
      KB5Axiom (phi.imp (psi.imp phi))
  | implyS (phi psi chi : Proposition Atom) :
      KB5Axiom ((phi.imp (psi.imp chi)).imp ((phi.imp psi).imp (phi.imp chi)))
  | efq (phi : Proposition Atom) :
      KB5Axiom (Proposition.bot.imp phi)
  | peirce (phi psi : Proposition Atom) :
      KB5Axiom (((phi.imp psi).imp phi).imp phi)
  | modalK (phi psi : Proposition Atom) :
      KB5Axiom ((Proposition.box (phi.imp psi)).imp
        ((Proposition.box phi).imp (Proposition.box psi)))
  | modalB (phi : Proposition Atom) :
      KB5Axiom (phi.imp (Proposition.box (Proposition.diamond phi)))
  | modalFive (phi : Proposition Atom) :
      KB5Axiom ((Proposition.diamond phi).imp
        (Proposition.box (Proposition.diamond phi)))
```

**Note**: `Proposition.diamond phi = (Proposition.box (Proposition.neg phi)).imp Proposition.bot` (i.e., `(box(phi -> bot)) -> bot`). The axiom 5 formula is `diamond phi -> box(diamond phi)`.

### Where to Place

- `KB5Axiom` definition: in `ProofSystem/Instances.lean` (following existing patterns) OR in a new file. Task 100 is adding 10 new axiom predicates and tag types, so KB5Axiom will likely be part of that expansion.
- If task 100 is not yet complete, `KB5Axiom` can be defined directly in `KB5Soundness.lean` (self-contained, following the `KAxiom` pattern which is defined in `Instances.lean` but could equally be local).

---

## 2. KB5 Soundness

### File: `KB5Soundness.lean`

**Imports**: `Cslib.Logics.Modal.Metalogic.Soundness` + `Cslib.Logics.Modal.ProofSystem.Instances`

**Main theorems**:

```lean
/-- Every axiom of KB5 is valid over symmetric, Euclidean frames. -/
theorem kb5_axiom_sound {World : Type*} {phi : Proposition Atom}
    (h_ax : KB5Axiom phi) (m : Model World Atom)
    (h_symm : forall w1 w2, m.r w1 w2 -> m.r w2 w1)
    (h_eucl : forall w1 w2 w3, m.r w1 w2 -> m.r w1 w3 -> m.r w2 w3)
    (w : World) : Satisfies m w phi

/-- KB5 Soundness: derivable formulas are valid on symmetric+Euclidean frames. -/
theorem kb5_soundness {World : Type*}
    {Gamma : List (Proposition Atom)} {phi : Proposition Atom}
    (d : DerivationTree (@KB5Axiom Atom) Gamma phi)
    (m : Model World Atom)
    (h_symm : forall w1 w2, m.r w1 w2 -> m.r w2 w1)
    (h_eucl : forall w1 w2 w3, m.r w1 w2 -> m.r w1 w3 -> m.r w2 w3)
    (w : World)
    (h_ctx : forall psi in Gamma, Satisfies m w psi) : Satisfies m w phi

/-- KB5 Soundness for derivable formulas. -/
theorem kb5_soundness_derivable {World : Type*}
    {phi : Proposition Atom} (h : Derivable (@KB5Axiom Atom) phi)
    (m : Model World Atom)
    (h_symm : forall w1 w2, m.r w1 w2 -> m.r w2 w1)
    (h_eucl : forall w1 w2 w3, m.r w1 w2 -> m.r w1 w3 -> m.r w2 w3)
    (w : World) : Satisfies m w phi
```

### Proof Strategy for `kb5_axiom_sound`

Case analysis on `h_ax`:
- `implyK`, `implyS`, `efq`, `peirce`, `modalK`: Standard propositional + K cases (identical to all other systems)
- `modalB`: Axiom B = `phi -> box(diamond phi)`. Given `h_phi : Satisfies m w phi`, need to show `forall w', m.r w w' -> exists w'', m.r w' w'' /\ Satisfies m w'' phi`. Use symmetry: take `w'' = w`, with `m.r w' w` from `h_symm w w' hr`.
- `modalFive`: Axiom 5 = `diamond phi -> box(diamond phi)`. Given `h_diam : exists w', m.r w w' /\ Satisfies m w' phi`, need `forall w'', m.r w w'' -> exists w''', m.r w'' w''' /\ Satisfies m w''' phi`. Given `<w', hr', hs>` from h_diam and `hr''` for w'', use Euclideanness: `h_eucl w w' w'' hr' hr''` gives... wait, Euclidean is `r w1 w2 -> r w1 w3 -> r w2 w3`. So from `r w w'` and `r w w''` we get `r w'' w'` (not `r w' w''`). We need `r w'' w'` -- that gives us `w''' = w'` with `m.r w'' w'` from Euclideanness applied as `h_eucl w w'' w'` with `r w w''` and `r w w'`. Yes, Euclidean: from `r w w''` and `r w w'` get `r w'' w'`.

Actually let me reconsider. `RightEuclidean`: `r a b -> r a c -> r b c`. So from `r w w'` (hr') and `r w w''` (hr'') we get `r w' w''`. And from the other direction, `r w w''` and `r w w'` gives `r w'' w'`. Either way we get a witness. The proof for axiom 5 uses the first: from `r w w'` and `r w w''`, get `r w'' w'`, so we take `w''' = w'` with access `r w'' w'` and satisfaction `hs`.

Wait, this matches `Satisfies.five` in Basic.lean at line 329:
```
theorem Satisfies.five {m : Model World Atom} [Relation.RightEuclidean m.r] {w : World}
    (phi : Proposition Atom) : Satisfies m w (diamond phi -> box(diamond phi))
```
The proof there: from `<w'', hr', hs>` (diamond phi at w) and `hr` (r w w'), use `heuc hr hr'` to get `r w' w''`, then `<w'', heuc hr hr', hs>`. So `heuc` takes `r w w'` and `r w w''` and gives `r w' w''`. Yes: `rightEuclidean : r a b -> r a c -> r b c`, so `heuc hr hr'` with `hr : r w w'` and `hr' : r w w''` gives `r w' w''`.

For the soundness proof, we don't have the instance `[Relation.RightEuclidean m.r]`; we have the explicit hypothesis `h_eucl`. The proof is:
```lean
| modalFive phi =>
    intro h_diam w' hr
    -- h_diam : Satisfies m w (diamond phi) = exists w'', r w w'' /\ Satisfies m w'' phi
    -- Need: Satisfies m w' (diamond phi) = exists w''', r w' w''' /\ Satisfies m w''' phi
    rw [Satisfies.diamond_iff] at h_diam |-
    obtain <w'', hr'', hs> := h_diam
    exact <w'', h_eucl w w' w'' hr hr'', hs>
```

Wait, we need to be careful. `Satisfies.diamond_iff` works at the bundled level. In the soundness proof for modalB/modalFive, we're working with raw `Satisfies` directly. Let me look at how `Satisfies.five` works in Basic.lean more carefully.

At line 329-337:
```lean
theorem Satisfies.five {m : Model World Atom} [Relation.RightEuclidean m.r] {w : World}
    (phi : Proposition Atom) : Satisfies m w (diamond phi -> box(diamond phi)) := by
  have heuc := @Relation.RightEuclidean.rightEuclidean (r := m.r)
  show Satisfies m w (.diamond phi) -> forall w', m.r w w' -> Satisfies m w' (.diamond phi)
  intro hdiam w' hr
  rw [diamond_iff] at hdiam |-
  obtain <w'', hr', hs> := hdiam
  exact <w'', heuc hr hr', hs>
```

So `heuc hr hr'` with `hr : r w w'` and `hr' : r w w''` gives `r w' w''`. The Euclidean property is `r a b -> r a c -> r b c`, so with `a=w, b=w', c=w''` we get `r w' w''`.

For the soundness case, with explicit `h_eucl`:
```lean
| modalFive phi =>
    -- Goal: Satisfies m w ((diamond phi).imp (box (diamond phi)))
    -- = Satisfies m w (diamond phi) -> forall w', r w w' -> Satisfies m w' (diamond phi)
    intro h_diam w' hr
    simp only [Satisfies] at h_diam |- -- or use show/unfold
    -- After unfolding diamond: need to carefully manage the encoding
```

Actually, since `Proposition.diamond phi = .imp (.box (.imp phi .bot)) .bot`, the Satisfies of diamond phi is `(forall w', r w w' -> Satisfies m w' phi -> False) -> False`. This is the double negation form. The `Satisfies.diamond_iff` lemma converts this to `exists w', r w w' /\ Satisfies m w' phi`.

In the existing soundness proofs (e.g., `axiom_sound` in Soundness.lean for S5), the B case at line 76 is:
```lean
| modalB phi =>
    intro hphi w' hr h_box_neg
    have h_symm : m.r w' w := h_eucl w w' w hr (h_refl w)
    exact h_box_neg w h_symm hphi
```

This works with S5 where we have reflexivity + Euclidean giving symmetry. For KB5 where we have explicit symmetry, the B case is simpler:
```lean
| modalB phi =>
    -- Goal: phi -> box(diamond phi)
    -- = Satisfies phi -> forall w', r w w' -> Satisfies (diamond phi) at w'
    -- = Satisfies phi -> forall w', r w w' -> ((forall w'', r w' w'' -> Satisfies phi -> False) -> False)
    intro h_phi w' hr h_box_neg
    exact h_box_neg w (h_symm w w' hr) h_phi
```

And the Five case:
```lean
| modalFive phi =>
    -- Goal: diamond phi -> box(diamond phi)
    -- Unfolded: ((box(neg phi)) -> bot) -> forall w', r w w' -> ((box(neg phi)) -> bot) at w'
    -- i.e., ((forall w', r w w' -> Satisfies phi -> False) -> False) ->
    --        forall w'', r w w'' -> ((forall w''', r w'' w''' -> Satisfies phi -> False) -> False)
    intro h_diam w' hr h_box_neg_w'
    apply h_diam
    intro w'' hr'' h_phi
    exact h_box_neg_w' w'' (h_eucl w w' w'' hr hr'') h_phi
```

Wait, let me reconsider the Euclidean direction. `h_eucl : r a b -> r a c -> r b c`. With `r w w'` (hr) and `r w w''` (hr'') we get `r w' w''`. So:
```lean
    exact h_box_neg_w' w'' (h_eucl w w' w'' hr hr'') h_phi
```
But wait, `h_eucl w w' w''` expects `r w w'` and `r w w''` and gives `r w' w''`. The arguments are `h_eucl w w' w'' hr hr''`. That's right.

Hmm but we need to be careful. Let me re-derive. The goal for modalFive at world w:
- Given: `h_diam : Satisfies m w (diamond phi)` which is `(forall v, r w v -> Satisfies m v (neg phi)) -> False`
  - i.e., `(forall v, r w v -> Satisfies m v phi -> False) -> False`
- Need: `forall w', r w w' -> Satisfies m w' (diamond phi)`
  - i.e., `forall w', r w w' -> ((forall v, r w' v -> Satisfies m v phi -> False) -> False)`

So proof:
```lean
intro h_diam w' hr h_neg_at_w'
-- h_neg_at_w' : forall v, r w' v -> Satisfies m v phi -> False
-- Need: False
-- Apply h_diam to get False
apply h_diam
-- Need: forall v, r w v -> Satisfies m v phi -> False
intro w'' hr'' h_phi
-- Have: r w w'' (hr''), Satisfies m w'' phi (h_phi)
-- From h_eucl w w' w'' hr hr'' : r w' w''
exact h_neg_at_w' w'' (h_eucl w w' w'' hr hr'') h_phi
```

This works. The Euclidean property `r w w' -> r w w'' -> r w' w''` lets us transfer the witness from w's successor w'' to w''s successor (through w').

---

## 3. canonical_symm (Task 100 Dependency)

### Statement

```lean
/-- The canonical accessibility relation is symmetric (from axiom B alone).
BRV Theorem 4.28 clause 2. -/
theorem canonical_symm
    {Axioms : Proposition Atom -> Prop}
    (h_implyK : ...)
    (h_implyS : ...)
    (h_B : forall (phi : Proposition Atom),
      Axioms (phi.imp (Proposition.box (Proposition.diamond phi))))
    (h_K : forall (phi psi : Proposition Atom),
      Axioms ((Proposition.box (phi.imp psi)).imp
        ((Proposition.box phi).imp (Proposition.box psi))))
    (S T : CanonicalWorld Axioms) :
    (CanonicalModel Axioms).r S T ->
    (CanonicalModel Axioms).r T S
```

### Proof Sketch (BRV Theorem 4.28 clause 2)

Given `hST : (CanonicalModel Axioms).r S T` (i.e., `forall phi, box phi in S -> phi in T`), show `(CanonicalModel Axioms).r T S` (i.e., `forall phi, box phi in T -> phi in S`).

1. Let `phi` be any formula with `box phi in T` -- need to show `phi in S`.
2. By contrapositive, assume `phi not in S`. Then `neg phi in S` (negation completeness).
3. By axiom B: `neg phi -> box(diamond(neg phi)) in S` (axiom B instance). Since `neg phi in S`, by MCS closure: `box(diamond(neg phi)) in S`.
4. Since `hST`: `box(diamond(neg phi)) in S` implies `diamond(neg phi) in T`.
5. `diamond(neg phi) = neg(box(neg(neg phi)))`. Having `diamond(neg phi) in T` means `box(neg(neg phi)) not in T` (by negation in MCS).
6. But `box phi in T` and we can derive `box(neg(neg phi))` from `box phi` using double negation in MCS...

Actually, the BRV proof is more direct. Let me re-read Theorem 4.28 clause 2:

> Let w and v be points such that R^KB wv, and suppose phi in w. As w is a KB-MCS, phi -> box(diamond phi) in w, thus by modus ponens box(diamond phi) in w. Hence by Lemma 4.19, diamond(phi) in v. But this means R^KB vw, as required.

So the proof shows: if R S T, then R T S. The argument: need to show `forall phi, box phi in T -> phi in S`. But wait, that's the wrong direction for the BRV argument. Let me re-read.

The BRV canonical relation is: `R w v iff for all psi, psi in v implies diamond psi in w` (Definition 4.18). But in this codebase, the canonical relation is: `R S T iff for all phi, box phi in S -> phi in T` (line 59 of Completeness.lean).

These are equivalent by Lemma 4.19. So the BRV proof adapted to this codebase:

Given R S T (i.e., `forall phi, box phi in S -> phi in T`), show R T S (i.e., `forall phi, box phi in T -> phi in S`).

Let `box phi in T`. Need `phi in S`.
- By contrapositive: suppose `phi not in S`. Then `neg phi in S`.
- By axiom B: `neg phi -> box(diamond(neg phi))` is an axiom. Since `neg phi in S`, by MCS closure: `box(diamond(neg phi)) in S`.
- By R S T: `diamond(neg phi) in T`.
- `diamond(neg phi) = neg(box(neg(neg phi)))` = `neg(box phi)` (since `neg(neg phi)` is `(phi -> bot) -> bot` which is logically equivalent to phi in classical logic, but NOT syntactically equal to phi).

Hmm, this is where it gets tricky. `diamond(neg phi) = neg(box(neg(neg phi)))` which is NOT `neg(box phi)` syntactically. We need a different approach.

Actually, let me re-read the BRV proof more carefully. The BRV convention for the canonical relation is `R w v iff for all psi, psi in v implies diamond psi in w`. Under the codebase convention `R S T iff for all phi, box phi in S -> phi in T`, Lemma 4.19 tells us these are equivalent.

The key BRV argument for symmetry: "suppose phi in w. phi -> box(diamond phi) in w, thus box(diamond phi) in w. By R wv (meaning box psi in w -> psi in v): diamond phi in v. This means R vw."

In the codebase convention, "R vw" means "for all psi, box psi in v -> psi in w". To show R T S we need: "for all psi, box psi in T -> psi in S".

The BRV argument doesn't directly give this. Let me think again...

Actually the BRV argument works differently. It shows R^KB vw by showing: for any formula chi, chi in w implies diamond chi in v. Let me match to codebase:

- We want to show `(CanonicalModel).r T S`, i.e., `forall phi, box phi in T -> phi in S`.
- Start with `box phi in T`. Want `phi in S`.
- Suppose for contradiction `phi not in S`. Then `neg phi in S`.
- Axiom B at `neg phi`: `neg phi -> box(diamond(neg phi))` is an axiom in KB5.
- MCS closure: `box(diamond(neg phi)) in S`.
- By `hST` (R S T): `diamond(neg phi) in T`.
- `diamond(neg phi) = neg(box(neg(neg phi)))`.
- So `neg(box(neg(neg phi))) in T`, meaning `box(neg(neg phi)) not in T`.
- But from `box phi in T`, can we derive `box(neg(neg phi)) in T`?
  - We need `phi -> neg(neg phi)` derivable, i.e., `phi -> ((phi -> bot) -> bot)`.
  - This IS derivable in classical logic: from `phi` and `phi -> bot`, derive `bot`.
  - So `box(phi -> neg(neg phi))` is derivable (by necessitation of a theorem).
  - Then `box phi` + `box(phi -> neg(neg phi))` gives `box(neg(neg phi))` by axiom K + MCS closure.
- So `box(neg(neg phi)) in T` -- contradiction with `box(neg(neg phi)) not in T`.

This is the correct argument. It requires:
1. `mcs_box_diamond` (from B): if `psi in S` then `box(diamond psi) in S`
2. The canonical relation to transfer box-membership
3. Classical double negation derivability to connect `box phi` to `box(neg(neg phi))`

This is indeed what the existing `canonical_eucl` does in a more complex way. The implementation in task 100 will handle this.

---

## 4. canonical_eucl_from_5 (Task 100 Dependency)

### Statement

```lean
/-- The canonical accessibility relation is Euclidean (from axiom 5 alone).
Analogous to BRV Theorem 4.27 for transitivity from axiom 4. -/
theorem canonical_eucl_from_5
    {Axioms : Proposition Atom -> Prop}
    (h_implyK : ...)
    (h_implyS : ...)
    (h_efq : ...)
    (h_peirce : ...)
    (h_K : ...)
    (h_5 : forall (phi : Proposition Atom),
      Axioms ((Proposition.diamond phi).imp
        (Proposition.box (Proposition.diamond phi))))
    (S T U : CanonicalWorld Axioms) :
    (CanonicalModel Axioms).r S T ->
    (CanonicalModel Axioms).r S U ->
    (CanonicalModel Axioms).r T U
```

### Proof Sketch

Given R S T and R S U, show R T U (i.e., `forall phi, box phi in T -> phi in U`).

1. Let `box phi in T`. Need `phi in U`.
2. Suppose `phi not in U`. Then `neg phi in U` (negation completeness).
3. Since R S U: for any `psi`, `box psi in S -> psi in U`. We need the reverse direction to make use of `neg phi in U`. 

Actually, the argument for Euclideanness from 5 is different. Let me think more carefully.

The standard proof of "5 implies Euclidean canonical frame" is analogous to "4 implies transitive canonical frame" (BRV Theorem 4.27):

**Theorem 4.27 pattern (4 -> transitive):** R wv and R vu. Need R wu. Take phi in u. Then diamond phi in v (by R vu). Then diamond(diamond phi) in w (by R wv). Then diamond phi in w (by axiom 4: diamond(diamond phi) -> diamond phi). So R wu.

**Analogous for 5 -> Euclidean:** R wv and R wu. Need R vu. Take phi in u. Then diamond phi in w (by R wu). Then box(diamond phi) in w (by axiom 5: diamond phi -> box(diamond phi)). Then diamond phi in v (by R wv: box(diamond phi) in w -> diamond phi in v). So R vu.

Wait, that last step assumes that R wv transfers `box(diamond phi)` to `diamond phi`. R wv means `for all psi, box psi in w -> psi in v`. So `box(diamond phi) in w` implies `diamond phi in v`. Yes!

So the proof is:
1. Given R S T (forall psi, box psi in S -> psi in T)
2. Given R S U (forall psi, box psi in S -> psi in U)
3. Need R T U (forall phi, box phi in T -> phi in U)

Hmm wait, the "Need R vu" from the BRV argument translates differently. Let me be very precise:

BRV's relation is `R w v iff for all chi, chi in v -> diamond chi in w`. Under the codebase's equivalent formulation: `R w v iff for all psi, box psi in w -> psi in v`.

For Euclidean: R S T and R S U implies R T U.
- R T U means: `for all phi, box phi in T -> phi in U`.

Proof attempt:
- Let `box phi in T`. Need `phi in U`.
- Suppose `phi not in U`. Then `neg phi in U`.

Actually, let me follow the BRV pattern more directly using the codebase relation:

BRV argument adapted: R S T and R S U. Want R T U, i.e., `forall phi, box phi in T -> phi in U`.

Take phi with `box phi in T`. By contrapositive assume `phi not in U`, derive contradiction.
- `phi not in U` -> `neg phi in U` -> `box(neg phi) not in T` (we'd need this but it's not obvious).

Let me try the direct BRV approach:
- We show: `for all phi, box phi in T -> phi in U`.
- Equivalently (by Lemma 4.19 in BRV): for all phi, `phi in U -> diamond phi in T`.
- Let `phi in U`. Since R S U: for box formulas in S, their contents are in U. But we need `diamond phi in T`.
- From `phi in U`: since we need to "look at this through S", consider: does `diamond phi in S`?
  - Well, R S U means `box psi in S -> psi in U`. This is NOT the same as `phi in U -> diamond phi in S`.

OK, the correct approach uses a different formulation. In BRV's Definition 4.18:
- `R w v iff for all psi, psi in v implies diamond psi in w`

Under this formulation:
- R S U means: `for all psi, psi in U -> diamond psi in S`
- R S T means: `for all psi, psi in T -> diamond psi in S`

For Euclidean, need R T U: `for all phi, phi in U -> diamond phi in T`.

BRV proof: Take phi in U. Then diamond phi in S (by R S U). Then box(diamond phi) in S (by axiom 5 + MCS closure). Then diamond phi in T (by R S T... wait, no).

Hmm, let me reconcile. With codebase's `R S T = forall psi, box psi in S -> psi in T`:
- By BRV Lemma 4.19, this is equivalent to `for all psi, psi in T -> diamond psi in S` for the alternative formulation.

So under the codebase convention:
- R S T: `box psi in S -> psi in T`
- R S U: `box psi in S -> psi in U`
- Need R T U: `box phi in T -> phi in U`

The BRV-style argument for "5 -> Euclidean" adapted:
- Approach: show for any phi, `box phi in T -> phi in U`.
- Equivalently by BRV Lemma 4.19 (in the other direction): `phi in U -> diamond phi in T`.
  - Wait, this equivalence only holds for MCS worlds.

Actually, let me look at how `canonical_trans` works in this codebase (line 78 of Completeness.lean):

```lean
theorem canonical_trans ... (S T U : CanonicalWorld Axioms) :
    (CanonicalModel Axioms).r S T ->
    (CanonicalModel Axioms).r T U ->
    (CanonicalModel Axioms).r S U := by
  intro hST hTU phi h_box
  have h_box_box := mcs_box_box h_implyK h_implyS h_4 S.property h_box
  have h_box_T := hST (Proposition.box phi) h_box_box
  exact hTU phi h_box_T
```

Beautiful -- from `box phi in S`, axiom 4 gives `box(box phi) in S`, R S T gives `box phi in T`, R T U gives `phi in U`.

For Euclidean from 5, we need R S T and R S U => R T U:
- Given `box phi in T`, need `phi in U`.
- We need to "go through S" somehow.

The key is axiom 5: `diamond phi -> box(diamond phi)`. Using the MCS membership:
- If `diamond phi in S`, then `box(diamond phi) in S` (by axiom 5 + MCS closure).
- If `box(diamond phi) in S`, then by R S T: `diamond phi in T`.
- If `diamond phi in T`, then... we know `box phi in T` and `diamond phi in T`. But `diamond phi = neg(box(neg phi))`. So having both `box phi in T` and `diamond phi in T` means `box phi in T` and `box(neg phi) not in T`.

Hmm, let me think differently. The correct argument:

We want `phi in U`. Suppose `phi not in U`. Then `neg phi in U`. Since R S U, we know box formulas in S go to U. We need to derive a contradiction.

OK, the cleanest approach: Let `box phi in T`. Want `phi in U`.

By contrapositive: suppose `box phi in T` but `phi not in U`.
- `phi not in U` => `neg phi in U` (negation completeness)
- From `neg phi in U` and R S U (which gives `box psi in S -> psi in U`), we CANNOT directly infer anything about S from U membership.

Wait, I need to use the EQUIVALENT characterization. `R S U` in BRV's alternative form (Lemma 4.19): `for all chi, chi in U -> diamond chi in S`. Is this provable from the codebase's `R S U = forall psi, box psi in S -> psi in U`?

Actually yes, for MCS worlds this is classical: `not (box (neg chi) in S)` iff `neg(box(neg chi)) in S` iff `diamond chi in S`. And `chi in U` + R S U means... hmm, that's the forward direction.

Let me think about it differently. The existing `canonical_eucl` (from B+T+4) uses a complex argument. For the axiom 5 version, the standard textbook proof is:

**Key insight**: Axiom 5 is `diamond phi -> box(diamond phi)`. In MCS terms: if `diamond phi in S`, then `box(diamond phi) in S`.

Proof of Euclidean: R S T, R S U, want R T U.
- Take `box phi in T`. Need `phi in U`.
- Suppose `phi not in U`. Then `neg phi in U`.
- By R S U (box psi in S -> psi in U), take the contrapositive: if `psi not in U` then `box psi not in S`.
  - But we cannot do a direct contrapositive of a universal statement that way in general.

Actually, the cleanest proof I've seen goes:

R S T and R S U, want R T U, i.e., `box phi in T -> phi in U`.

Take box phi in T. Suppose for contradiction phi not in U.
- neg phi in U (negation completeness).
- box(neg phi) not in T (otherwise neg phi in U AND phi in U from applying R T U which we're trying to prove... circular).

Hmm, let me look at this from the "diamond" perspective:

Actually, the cleanest known proof (standard in textbooks) is:

Show R T U, i.e., `forall phi, box phi in T -> phi in U`. Equivalently (by negation completeness of MCS T): `forall phi, neg phi in U -> box phi not in T`, i.e., `forall phi, neg phi in U -> neg(box phi) in T`, i.e., `forall phi, neg phi in U -> diamond(neg phi) in T`.

Even cleaner: show the equivalent `forall chi, chi in U -> diamond chi in T` (BRV Lemma 4.19 reverse direction).

Take chi in U. Since R S U (codebase form: box psi in S -> psi in U):
- We cannot directly go from chi in U to anything in S.

OK let me just follow the standard proof from Chellas or Hughes & Cresswell:

**Standard proof**: R w v and R w u implies R v u.
- Suppose box phi in v (codebase form). Need phi in u.
- Suppose for contradiction phi not in u. Then neg phi in u. Then box(neg phi) not in v (otherwise neg phi in u AND phi in u since we'd have R v u which gives phi in u from box phi in v -- but that's circular).
  
The right argument: We use the diamond characterization.

Since R S T (= box psi in S -> psi in T) and we want R T U (= box phi in T -> phi in U):

Take box phi in T. Toward contradiction assume phi not in U.
- phi not in U => neg phi in U => box(neg phi) not in S (because R S U would give neg phi in U, which is what we have, but that doesn't help).

Actually, wait. `box(neg phi) in S` would give (by R S U) `neg phi in U`. That's consistent. And `box(neg phi) in S` would give (by R S T) `neg phi in T`. Does that contradict `box phi in T`? Not directly unless we have reflexivity.

I think the correct proof uses the following approach:

**Claim**: For any phi, if `box phi in T`, then `box phi in S`.

If we can show this, then from `box phi in S` and R S U, we get `phi in U`. Done.

To show `box phi in T -> box phi in S`:
- Suppose `box phi in T`. Then `box(box phi) in T` (if we have axiom 4)... but we DON'T have axiom 4.

Hmm, this approach fails without axiom 4.

Let me try yet another approach. The standard proof for "5 implies Euclidean canonical frame":

The axiom 5 is: `diamond phi -> box(diamond phi)`.

Proof of R T U (given R S T and R S U):
- Need: `box phi in T -> phi in U`.
- Equivalently: `phi not in U -> box phi not in T`.
- Equivalently: `neg phi in U -> neg(box phi) in T`.
- i.e., `neg phi in U -> diamond(neg phi) in T`.

So we need: if `neg phi in U` then `diamond(neg phi) in T`.

From `neg phi in U`: since R S U gives `box psi in S -> psi in U`, we can ask: is `box(neg phi) in S`?
- Not necessarily. But consider: if `diamond(neg phi) not in S`, then `neg(diamond(neg phi)) in S`, i.e., `box(neg(neg phi)) in S`. Then R S U gives `neg(neg phi) in U`. Can we derive `neg phi in U` and `neg(neg phi) in U` are inconsistent? Yes! `neg phi` = `phi -> bot` and `neg(neg phi)` = `(phi -> bot) -> bot`. Having both in MCS U means `bot in U` by MP, contradiction.

So: `neg phi in U` implies `diamond(neg phi) in S` (by contrapositive argument above).

Now axiom 5: `diamond(neg phi) in S` implies `box(diamond(neg phi)) in S`.

By R S T: `box(diamond(neg phi)) in S` implies `diamond(neg phi) in T`.

So: `neg phi in U` implies `diamond(neg phi) in T`. Done.

**Full proof chain**:
1. `neg phi in U` (given, toward showing diamond(neg phi) in T)
2. Assume for contradiction `diamond(neg phi) not in S`, i.e., `box(neg(neg phi)) in S` (since diamond psi = neg(box(neg psi)), so neg(diamond(neg phi)) = box(neg(neg phi))).

Wait, `diamond(neg phi) = neg(box(neg(neg phi)))` -- let me be careful.
- `diamond psi = neg(box(neg psi))`.
- `diamond(neg phi) = neg(box(neg(neg phi)))`.
- If `diamond(neg phi) not in S`, then by negation completeness: `neg(diamond(neg phi)) in S` = `neg(neg(box(neg(neg phi)))) in S`... this is getting complicated.

Actually: `diamond(neg phi) = (box((neg phi) -> bot)) -> bot = (box(neg(neg phi))) -> bot`. Wait no.

Let me use the exact definition: `Proposition.diamond psi = Proposition.neg (Proposition.box (Proposition.neg psi))` = `(box(psi -> bot)).imp bot`.

So `diamond(neg phi)` = `(box((neg phi) -> bot)).imp bot` = `(box(neg(neg phi))).imp bot` where `neg(neg phi) = (phi -> bot) -> bot`.

Hmm, `neg phi = phi.imp bot`. So `neg(neg phi) = (phi.imp bot).imp bot`. And `box(neg(neg phi)) = box((phi.imp bot).imp bot)`.

So `diamond(neg phi) = (box((phi.imp bot).imp bot)).imp bot`.

If `diamond(neg phi) not in S`, then `neg(diamond(neg phi)) in S`.
`neg(diamond(neg phi))` = `diamond(neg phi).imp bot` = `((box((phi.imp bot).imp bot)).imp bot).imp bot`.

This is `neg(neg(box(neg(neg phi))))` which is double negation of `box(neg(neg phi))`.

In a classical MCS, `neg(neg X)` iff `X`. So `neg(neg(box(neg(neg phi)))) in S` iff `box(neg(neg phi)) in S`.

OK, so: `diamond(neg phi) not in S` => (classically in MCS) `box(neg(neg phi)) in S`.

Then by R S U: `neg(neg phi) in U`, i.e., `(phi -> bot) -> bot in U`.
And we have `neg phi in U`, i.e., `phi -> bot in U`.
By MCS MP: `bot in U`. Contradiction.

So `diamond(neg phi) in S` (step completed).

Then: axiom 5 gives `diamond(neg phi) -> box(diamond(neg phi))` in S (MCS contains all axioms). By MCS MP: `box(diamond(neg phi)) in S`.

Then: by R S T: `diamond(neg phi) in T`.

And `diamond(neg phi) in T` = `neg(box phi) in T`... wait, is that right?

`diamond(neg phi) = neg(box(neg(neg phi)))`. And `neg(box phi) = (box phi).imp bot`.

These are NOT the same formula. `diamond(neg phi) = neg(box(neg(neg phi)))` while we want `neg(box phi)`.

But in a classical MCS, `box(neg(neg phi))` and `box phi` are interderivable (via double negation elimination inside the box, using axiom K and the derivability of `phi <-> neg(neg phi)`).

So `diamond(neg phi) in T` implies `neg(box(neg(neg phi))) in T` which classically implies `box(neg(neg phi)) not in T`. And since `neg(neg phi) <-> phi` is derivable, `box(neg(neg phi)) <-> box phi` is derivable (via K + necessitation of the biconditional). So `box phi not in T`.

This gives: `box phi not in T`, which is the contrapositive of what we want!

So the full proof: given R S T, R S U, we show `box phi in T -> phi in U` by contrapositive: `phi not in U -> box phi not in T`.

**Final proof outline**:
1. Assume `phi not in U`, i.e., `neg phi in U`.
2. Show `diamond(neg phi) in S` (by contradiction using double negation + R S U + MCS consistency).
3. By axiom 5 + MCS: `box(diamond(neg phi)) in S`.
4. By R S T: `diamond(neg phi) in T`.
5. From `diamond(neg phi) in T`, derive `box phi not in T` (using MCS double negation properties).

This is a somewhat involved proof, and task 100 will need to handle the double-negation-under-box manipulation. The key helper needed: **In a classical MCS with axiom K, `box phi in S <-> box(neg(neg phi)) in S`** (or equivalently, the necessitation of the classically derivable `phi <-> neg(neg phi)`).

---

## 5. KB5 Completeness

### File: `KB5Completeness.lean`

**Imports**: `Cslib.Logics.Modal.Metalogic.KCompleteness` + `Cslib.Logics.Modal.Metalogic.Completeness` + `Cslib.Logics.Modal.ProofSystem.Instances`

Once task 100 provides `canonical_symm` and `canonical_eucl_from_5`, the completeness proof follows the standard pattern.

### Main Theorem

```lean
/-- Completeness for KB5: if phi is valid on all symmetric + Euclidean frames,
then phi is KB5-derivable. -/
theorem kb5_completeness (phi : Proposition Atom)
    (h_valid : forall (World : Type u) (m : Model World Atom),
      (forall w1 w2, m.r w1 w2 -> m.r w2 w1) ->
      (forall w1 w2 w3, m.r w1 w2 -> m.r w1 w3 -> m.r w2 w3) ->
      forall w, Satisfies m w phi) :
    Derivable (@KB5Axiom Atom) phi
```

### Proof Structure

```
by_contra h_not_deriv
-- 1. {neg phi} is KB5-consistent (standard derivation argument)
have h_cons : Modal.SetConsistent (@KB5Axiom Atom) ({neg phi}) := ...
-- 2. Lindenbaum extension
obtain <M, hM_sup, hM_mcs> := modal_lindenbaum h_cons
let w : CanonicalWorld (@KB5Axiom Atom) := <M, hM_mcs>
-- 3. Truth lemma (K-style, no axiom T!)
-- Uses k_truth_lemma instantiated at KB5Axiom constructors
-- 4. Frame properties
-- canonical_symm from axiom B
-- canonical_eucl_from_5 from axiom 5
-- 5. Apply h_valid + contradiction
exact mcs_not_mem_of_neg ... hM_mcs (hM_sup (Set.mem_singleton _))
    ((k_truth_lemma
      (fun phi psi => .implyK phi psi)
      (fun phi psi chi => .implyS phi psi chi)
      (fun phi => .efq phi)
      (fun phi psi => .peirce phi psi)
      (fun phi psi => .modalK phi psi)
      w phi).mp
      (h_valid (CanonicalWorld (@KB5Axiom Atom))
        (CanonicalModel (@KB5Axiom Atom))
        (fun S T hST => canonical_symm ... S T hST)
        (fun S T U hST hSU => canonical_eucl_from_5 ... S T U hST hSU)
        w))
```

**Critical distinction from S4/S5**: Uses `k_truth_lemma` (no `h_T` parameter) instead of `truth_lemma` (which requires `h_T`). This is because KB5 does NOT contain axiom T.

---

## 6. Instance Registration (Task 100 Scope)

Task 100 will add to `ProofSystem/Instances.lean`:
- Tag type: `opaque Modal.HilbertKB5 : Type := Empty`
- `KB5Axiom` inductive definition
- Instances: `InferenceSystem`, `ModusPonens`, `Necessitation`, `HasAxiomImplyK`, `HasAxiomImplyS`, `HasAxiomEFQ`, `HasAxiomPeirce`, `HasAxiomK`, `HasAxiomB`, `HasAxiom5`, `ModalHilbert`, `ModalKB5Hilbert`

Bundled class (new):
```lean
class ModalKB5Hilbert (S : Type*) [HasBot F] [HasImp F] [HasBox F]
    extends ModalHilbert S (F := F),
            HasAxiomB S (F := F),
            HasAxiom5 S (F := F)
```

---

## 7. Dependencies and Blockers

### Hard Dependency on Task 100

Task 106 REQUIRES from task 100:
1. **`KB5Axiom`** inductive definition (7 constructors)
2. **`canonical_symm`** theorem (symmetry from B alone)
3. **`canonical_eucl_from_5`** theorem (Euclideanness from 5 alone)
4. **`Modal.HilbertKB5`** tag type
5. **`ModalKB5Hilbert`** bundled class + instances

### Available Infrastructure (Already Exists)

- `k_truth_lemma` -- K-specific truth lemma (no axiom T) -- in `KCompleteness.lean`
- `k_mcs_box_witness` -- K-specific box witness -- in `KCompleteness.lean`
- `k_derive_box_from_inconsistency` -- K-specific consistency -- in `KCompleteness.lean`
- `Satisfies.b` -- B axiom semantic validity -- in `Basic.lean`
- `Satisfies.five` -- 5 axiom semantic validity -- in `Basic.lean`
- `soundness` / `soundness_derivable` -- parameterized soundness -- in `Soundness.lean`
- `CanonicalModel`, `CanonicalWorld` -- canonical model definitions -- in `Completeness.lean`
- `modal_lindenbaum` -- Lindenbaum's lemma -- in `MCS.lean`
- `mcs_box_diamond` -- B axiom MCS property -- in `MCS.lean`
- All propositional MCS properties -- in `MCS.lean`
- `Std.Symm`, `Relation.RightEuclidean` -- frame condition types -- in `Relation.lean`

### What KB5Soundness.lean Can Do Without Task 100

The soundness proof (`kb5_axiom_sound`) only needs `KB5Axiom`. If `KB5Axiom` is defined locally in `KB5Soundness.lean` (self-contained), soundness can proceed independently. The `kb5_soundness` and `kb5_soundness_derivable` wrappers use the parameterized `soundness` theorem.

### What REQUIRES Task 100

The completeness proof (`kb5_completeness`) requires `canonical_symm` and `canonical_eucl_from_5`. These are the core contributions of task 100.

---

## 8. File Structure

### KB5Soundness.lean

```
module
public import Cslib.Logics.Modal.Metalogic.Soundness
public import Cslib.Logics.Modal.ProofSystem.Instances

-- KB5Axiom definition (if not yet in Instances.lean from task 100)
-- kb5_axiom_sound
-- kb5_soundness
-- kb5_soundness_derivable
```

### KB5Completeness.lean

```
module
public import Cslib.Logics.Modal.Metalogic.KCompleteness
public import Cslib.Logics.Modal.Metalogic.Completeness  -- for canonical_symm, canonical_eucl_from_5
public import Cslib.Logics.Modal.ProofSystem.Instances

-- kb5_completeness
```

### Metalogic.lean (update)

Add:
```lean
public import Cslib.Logics.Modal.Metalogic.KB5Soundness
public import Cslib.Logics.Modal.Metalogic.KB5Completeness
```

---

## 9. Tactic Survey Results

Based on the patterns in existing proofs:

| Proof Component | Primary Tactic | Notes |
|----------------|----------------|-------|
| Propositional axiom cases (implyK, implyS, efq, peirce) | `intro` + `exact` / `absurd` | Identical across all logics |
| modalK case | `intro` + `exact` | Identical across all logics |
| modalB case | `intro` + `exact` with `h_symm` | Simple symmetry application |
| modalFive case | `intro` + `apply` + `exact` with `h_eucl` | Euclidean property transfer |
| Consistency argument | Copy from `k_completeness` | Standard double negation elimination |
| Truth lemma | Reuse `k_truth_lemma` | No custom proof needed |
| Frame properties | Instantiate `canonical_symm` / `canonical_eucl_from_5` | Direct application |

No `simp`/`aesop`/`omega` needed for the main proofs. The proof structure is primarily term-mode with explicit `intro`/`exact`/`apply`.

---

## 10. Summary of Findings

1. **KB5Axiom** needs 7 constructors: implyK, implyS, efq, peirce, modalK, modalB, modalFive
2. **Soundness** is straightforward: case analysis with `h_symm` for B and `h_eucl` for 5
3. **Completeness** uses `k_truth_lemma` (NOT `truth_lemma`) since KB5 lacks axiom T
4. **canonical_symm** and **canonical_eucl_from_5** are the critical task 100 deliverables
5. **Proof complexity**: Low for soundness (analogous to KSoundness.lean), medium for completeness (standard canonical model argument with k_truth_lemma reuse)
6. **No blockers** beyond task 100 completion

### Risk Assessment

- **Low risk**: Soundness (self-contained, patterns well-established)
- **Medium risk**: Completeness depends on task 100's `canonical_symm` and `canonical_eucl_from_5` signatures -- if those change, adaptation needed
- **No sorry risk**: All proof components have clear strategies with existing infrastructure
