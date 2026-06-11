# Research Report: Modal B Soundness and Completeness

**Task**: 101 - Modal B Soundness and Completeness
**Date**: 2026-06-10
**References**: Blackburn, de Rijke, Venema (BRV) "Modal Logic" (2002), Chapter 4, Theorem 4.28 clause 2

---

## Literature Proof Structure

**Source**: Blackburn, de Rijke, Venema (2002), Theorem 4.28 clause 2, plus Table 4.1
**Strategy**: Completeness-via-canonicity for KB over symmetric frames

### Step Map

1. **Define BAxiom predicate** -- Task 100 dependency (Instances.lean)
2. **Define HilbertB tag type** -- Task 100 dependency (ProofSystem.lean)
3. **Prove B axiom soundness on symmetric frames** -- BRV Definition 4.9 + Table 4.1
4. **Prove canonical_symm** -- BRV Theorem 4.28 clause 2 (task 100 dependency)
5. **Reuse k_truth_lemma for the truth lemma** -- BRV Lemma 4.21, K-specific version
6. **Prove b_completeness** -- BRV Theorem 4.28 clause 2 + Proposition 4.12

### Dependencies
- Steps 1, 2, 4 depend on task 100 (shared infrastructure)
- Step 5 reuses `k_truth_lemma` from KCompleteness.lean (already exists)
- Step 6 depends on steps 4 and 5

### Potential Formalization Challenges
- Step 4 (canonical_symm): The proof of symmetry from axiom B alone is a core challenge, but it follows BRV directly and is assigned to task 100.
- Step 5 (truth lemma): B has NO axiom T, so we must use `k_truth_lemma` (from KCompleteness.lean), NOT the T-based `truth_lemma` (from Completeness.lean). This is the critical design decision.

---

## 1. Soundness Analysis

### 1.1 BAxiom Predicate (Task 100 Dependency)

Task 100 must create `BAxiom` with 6 constructors -- the 4 propositional axioms plus K and B:

```lean
inductive BAxiom : Proposition Atom -> Prop where
  | implyK (phi psi : Proposition Atom) : BAxiom (phi.imp (psi.imp phi))
  | implyS (phi psi chi : Proposition Atom) : BAxiom ((phi.imp (psi.imp chi)).imp ((phi.imp psi).imp (phi.imp chi)))
  | efq (phi : Proposition Atom) : BAxiom (Proposition.bot.imp phi)
  | peirce (phi psi : Proposition Atom) : BAxiom (((phi.imp psi).imp phi).imp phi)
  | modalK (phi psi : Proposition Atom) : BAxiom ((Proposition.box (phi.imp psi)).imp ((Proposition.box phi).imp (Proposition.box psi)))
  | modalB (phi : Proposition Atom) : BAxiom (phi.imp (Proposition.box (Proposition.diamond phi)))
```

### 1.2 Satisfies.b (Already Exists)

The semantic validity of axiom B on symmetric frames is already proven in `Cslib/Logics/Modal/Basic.lean` at line 276:

```lean
theorem Satisfies.b {m : Model World Atom} [instSymm : Std.Symm m.r] {w : World}
    (phi : Proposition Atom) :
    Modal[m,w |= phi -> box(diamond(phi))] := by
  show Satisfies m w phi -> forall w', m.r w w' -> Satisfies m w' (.diamond phi)
  intro hphi w' hr
  rw [diamond_iff]
  exact <w, instSymm.symm w w' hr, hphi>
```

This proves: on symmetric frames, if `phi` holds at `w`, then for all `w'` with `R(w,w')`, since `R(w',w)` by symmetry, `diamond(phi)` holds at `w'`. So `box(diamond(phi))` holds at `w`.

### 1.3 BSoundness.lean Structure

The soundness file follows the exact pattern of KSoundness.lean/TSoundness.lean/DSoundness.lean:

```
BSoundness.lean:
  imports: Soundness, Instances
  
  b_axiom_sound: BAxiom phi -> symmetric model -> Satisfies m w phi
    - Cases on BAxiom constructors
    - Propositional cases: identical to K/T/D (copy from KSoundness.lean)
    - modalK case: identical to all others
    - modalB case: uses symmetry hypothesis directly
      intro hphi w' hr
      -- Need: Satisfies m w' (diamond phi)
      -- Have: h_symm w w' hr : m.r w' w
      -- So: diamond phi holds at w' via witness w
      
  b_soundness: DerivationTree BAxiom Gamma phi -> symmetric model -> Satisfies
    := soundness d m (fun psi h_ax w => b_axiom_sound h_ax m h_symm w) w h_ctx
    
  b_soundness_derivable: Derivable BAxiom phi -> symmetric model -> Satisfies
    := soundness_derivable h m (fun psi h_ax w => b_axiom_sound h_ax m h_symm w) w
```

**Key**: The `modalB` case needs symmetry of the frame relation. The hypothesis should be `(h_symm : forall w1 w2, m.r w1 w2 -> m.r w2 w1)` to match the explicit style used in other soundness files (not `Std.Symm` typeclass, which is the semantic level).

### 1.4 Soundness Proof for modalB Case

Following the literature (BRV Definition 4.9):

Axiom B: `phi -> box(diamond(phi))`

Unfolded semantics:
- `Satisfies m w phi` implies
- For all `w'` with `m.r w w'`, `Satisfies m w' (diamond phi)`
- i.e., there exists `w''` with `m.r w' w''` and `Satisfies m w'' phi`

On symmetric frames, take `w'' = w`. Since `m.r w w'` and symmetry gives `m.r w' w`, the witness is `w` itself.

Lean proof sketch:
```lean
| modalB phi =>
    intro hphi w' hr
    exact ⟨w, h_symm w w' hr, hphi⟩
```

Note: The `diamond phi` unfolds to `(box (phi.imp bot)).imp bot`, which means `Satisfies m w' (diamond phi)` unfolds to an existential-like statement. Looking at `diamond_iff` in Basic.lean, we need to check how diamond is handled. From the `Satisfies.b` proof, it uses `rw [diamond_iff]` and then provides the witness as a triple. The soundness proof should mirror this.

Actually, looking at the existing proofs more carefully, the approach in the soundness files is more direct. Let me trace through what `Satisfies m w (phi.imp (box (diamond phi)))` unfolds to:

```
Satisfies m w phi -> (forall w', m.r w w' -> Satisfies m w' (diamond phi))
```

And `Satisfies m w' (diamond phi)` unfolds to (since diamond phi = (box (phi.imp bot)).imp bot):

```
(forall w'', m.r w' w'' -> Satisfies m w'' phi -> False) -> False
```

So the proof must show: given `hphi : Satisfies m w phi`, `w' : World`, `hr : m.r w w'`, and `h_box_neg : forall w'', m.r w' w'' -> Satisfies m w'' phi -> False`, derive `False`.

With symmetry giving `m.r w' w`, apply `h_box_neg w (h_symm w w' hr) hphi` to get `False`.

Looking at the existing S5 `axiom_sound` modalB case (Soundness.lean, line 76):
```lean
| modalB phi =>
    intro hphi w' hr h_box_neg
    have h_symm : m.r w' w := h_eucl w w' w hr (h_refl w)
    exact h_box_neg w h_symm hphi
```

For B soundness, the proof is simpler since we directly have symmetry:
```lean
| modalB phi =>
    intro hphi w' hr h_box_neg
    exact h_box_neg w (h_symm w w' hr) hphi
```

---

## 2. Completeness Analysis

### 2.1 Critical Design Decision: K Truth Lemma, NOT T Truth Lemma

**B = K + axiom B**. Crucially, B does NOT include axiom T (`box phi -> phi`).

The codebase has two truth lemmas:
1. `truth_lemma` (Completeness.lean): Requires `h_T` parameter (axiom T). Used by T, S4, S5 completeness.
2. `k_truth_lemma` (KCompleteness.lean): Does NOT require axiom T. Uses `k_mcs_box_witness` with EFQ instead.

**B completeness MUST use `k_truth_lemma`**, mirroring the K completeness pattern. This is the same situation as K itself: no axiom T available.

### 2.2 canonical_symm (Task 100 Dependency)

Task 100 must provide `canonical_symm` in Completeness.lean. Following BRV Theorem 4.28 clause 2:

**Theorem** (BRV 4.28, KB symmetry is canonical): The canonical frame for any normal logic containing axiom B is symmetric.

**Proof**: Let `w, v` be MCS's with `R wv` (i.e., for all `psi`, `box psi in w -> psi in v`). We show `R vw`: suppose `phi in w`. As `w` is a KB-MCS, `phi -> box(diamond(phi)) in w` (axiom B), thus by modus ponens `box(diamond(phi)) in w`. Hence by `R wv` (Lemma 4.19), `diamond(phi) in v`. But this means `R vw`, as required.

Wait -- that last step needs explanation. `diamond(phi) in v` means `(box(phi -> bot)) -> bot in v`, which is `neg(box(neg(phi))) in v`. The canonical relation definition is `R S T iff forall psi, box psi in S -> psi in T`. So `R vw` means: for all `psi`, `box psi in v -> psi in w`. We showed that if `phi in w` then `diamond(phi) in v`, i.e., `neg(box(neg(phi))) in v`.

Actually, let me reconsider. The BRV canonical relation (Definition 4.18) is: `R wv iff forall psi, psi in v implies diamond(psi) in w`. Lemma 4.19 shows this is equivalent to: `R wv iff forall psi, box(psi) in w implies psi in v`.

So `R vw` means: for all `psi`, `box(psi) in v -> psi in w`. But we showed: for all `phi`, `phi in w -> diamond(phi) in v`. By the equivalence (using the other direction of Lemma 4.19 at the `v,w` position), `R vw` iff for all `phi`, `phi in w implies diamond(phi) in v`.

In the codebase, the canonical relation is defined as:
```lean
r := fun S T => forall phi, Proposition.box phi in S.val -> phi in T.val
```

So `R S T` means: `box phi in S -> phi in T`. And `R T S` means: `box phi in T -> phi in S`.

For symmetry: given `R S T` (i.e., `box phi in S -> phi in T`), show `R T S` (i.e., `box phi in T -> phi in S`).

The BRV proof works differently from a direct translation. Let me think about this more carefully.

Given: `R S T` and `box phi in T` (want: `phi in S`).
Need to show: `phi in S`.

From `box phi in T`, by axiom B applied in T: `phi in T` implies `box(diamond(phi)) in T` ... no, that's the wrong direction.

Actually, let me re-read BRV Theorem 4.28 clause 2 carefully:

> "Let w and v be points in this model such that R^KB wv, and suppose phi in w. As w is a KB-MCS, phi -> box(diamond(phi)) in w, thus by modus ponens box(diamond(phi)) in w. Hence by Lemma 4.19, diamond(phi) in v. But this means R^KB vw, as required."

So the proof shows: for all phi, phi in w -> diamond(phi) in v. And then BRV claims this is the same as R vw.

In the codebase definition, `R vw` means `box psi in v -> psi in w`. The equivalence is:
- `R vw` (forall psi, box psi in v -> psi in w)
- iff (forall phi, phi in w -> diamond(phi) in v) [by contraposition + MCS negation properties]

This equivalence is standard. Let me check if this alternative characterization exists in the codebase.

Actually, looking at `canonical_eucl` in Completeness.lean more carefully (lines 95-141), it does NOT use this alternative characterization directly. Instead it proves R T U by showing for each phi with box phi in T, that phi in U. It's a more complex indirect proof.

For canonical_symm, the approach would be:
- Given `R S T` (box psi in S -> psi in T) and `box phi in T`, show `phi in S`.
- Suppose `phi not in S`. Then `neg phi in S` (MCS completeness).
- By axiom B: `neg phi -> box(diamond(neg phi)) in S` (axiom B at neg phi).
- So `box(diamond(neg phi)) in S`.
- By R S T: `diamond(neg phi) in T`.
- `diamond(neg phi) = neg(box(neg(neg phi))) = neg(box phi)` ... hmm, not quite.

Let me be more precise. `diamond(neg phi) = (box (neg phi -> bot)).imp bot = (box (neg (neg phi))).imp bot`. Wait, that's not right either.

In the codebase: `diamond phi = (box (phi.imp bot)).imp bot`. So:
- `diamond (neg phi) = (box ((neg phi).imp bot)).imp bot`
- `(neg phi).imp bot = (phi.imp bot).imp bot`

This gets complex. Let me think about what the task 100 `canonical_symm` proof would actually look like.

The existing `canonical_eucl` proof (which uses B among other axioms) provides a template. The key steps for canonical_symm would need:
1. `mcs_box_diamond`: Given phi in S, get box(diamond(phi)) in S (uses axiom B).
2. From R S T and box(diamond(phi)) in S, get diamond(phi) in T.
3. From diamond(phi) in T, need to derive that R T S... but this requires more work.

Actually, looking at the BRV proof more carefully, the argument is indirect. BRV uses the SECOND characterization of the canonical relation (Lemma 4.19 = Definition 4.18): R wv iff for all phi, phi in v implies diamond(phi) in w. In the codebase the canonical relation uses the first characterization (box-based). So we need to connect them.

The connection is: "R T S" (box psi in T -> psi in S) is equivalent to "for all phi, phi in S implies diamond(phi) in T" when S and T are MCS.

The existing codebase does NOT have this lemma explicitly. But `canonical_eucl` works around it. For `canonical_symm`, the proof from task 100 would likely follow a pattern like:

```lean
theorem canonical_symm
    {Axioms : Proposition Atom -> Prop}
    (h_implyK : ...) (h_implyS : ...)
    (h_B : forall phi, Axioms (phi.imp (box (diamond phi))))
    (h_K : forall phi psi, Axioms ((box (phi.imp psi)).imp ((box phi).imp (box psi))))
    (S T : CanonicalWorld Axioms)
    (hST : (CanonicalModel Axioms).r S T) :
    (CanonicalModel Axioms).r T S
```

The proof needs to show: for all phi, box phi in T -> phi in S.

Given box phi in T, suppose phi not in S. Then neg phi in S (MCS). By axiom B, box(diamond(neg phi)) in S. By R S T, diamond(neg phi) in T. Now diamond(neg phi) = neg(box(neg(neg phi))). Since T is MCS and box phi in T, we need to connect neg(neg phi) with phi and derive a contradiction.

Actually, `diamond(neg phi) = (box (neg_phi.imp bot)).imp bot`. And `neg_phi = phi.imp bot`. So `neg_phi.imp bot = (phi.imp bot).imp bot`. And `box((phi.imp bot).imp bot)` ... this is `box(neg(neg phi))`.

In the codebase: `neg phi = phi.imp bot`, so `neg(neg phi) = (phi.imp bot).imp bot`.

We need: from `box phi in T` and `diamond(neg phi) in T`, derive contradiction.

`diamond(neg phi) in T` means `(box(neg(neg phi))).imp bot in T`, i.e., `neg(box(neg(neg phi))) in T`.

Now we need to show `box(neg(neg phi)) in T`. From `box phi in T`, we can derive `box(neg(neg phi)) in T` if we have `box(phi.imp neg(neg phi)) in T`. Since `phi -> neg(neg phi)` is a theorem (derivable from Peirce/EFQ), by necessitation `box(phi -> neg(neg phi))` is derivable, so it's in T. Then by K: `box phi in T` and `box(phi -> neg(neg phi)) in T` gives `box(neg(neg phi)) in T`.

Then `neg(box(neg(neg phi))) in T` and `box(neg(neg phi)) in T` both in the MCS T, which contradicts MCS consistency.

So the full `canonical_symm` proof structure is clear. Task 100 handles this.

### 2.3 BCompleteness.lean Structure

The completeness file follows the pattern of KCompleteness.lean (since B lacks axiom T):

```
BCompleteness.lean:
  imports: KCompleteness (for k_truth_lemma, k_mcs_box_witness),
           Completeness (for CanonicalModel, canonical_symm when available),
           Instances (for BAxiom)

  -- No new truth lemma needed! Reuse k_truth_lemma.
  
  b_completeness: 
    phi valid on symmetric frames -> Derivable BAxiom phi
    Proof by contrapositive (BRV Proposition 4.12 + Theorem 4.28 clause 2):
    1. Assume phi not derivable
    2. {neg phi} is B-consistent
    3. Lindenbaum extension to MCS M
    4. Canonical model with B axioms
    5. k_truth_lemma instantiated at BAxiom constructors
    6. canonical_symm from axiom B (task 100)
    7. h_valid gives phi satisfied at M
    8. truth lemma gives phi in M
    9. Contradiction with neg phi in M
```

### 2.4 Validity Hypothesis Shape

For `b_completeness`, the hypothesis `h_valid` should match the Cube.lean definition of B:
```lean
def B World Atom := logic {m : Model World Atom | Std.Symm m.r}
```

The hypothesis should be:
```lean
h_valid : forall (World : Type u) (m : Model World Atom),
    (forall w1 w2, m.r w1 w2 -> m.r w2 w1) ->
    forall w, Satisfies m w phi
```

This matches the explicit-hypothesis style used by other completeness theorems (e.g., `t_completeness` takes `(forall w, m.r w w) ->`, `s4_completeness` takes reflexivity + transitivity).

### 2.5 Concrete Proof Term Analysis

The completeness proof will follow this structure (parallel to `k_completeness` in KCompleteness.lean):

```lean
theorem b_completeness (phi : Proposition Atom)
    (h_valid : forall (World : Type u) (m : Model World Atom),
      (forall w1 w2, m.r w1 w2 -> m.r w2 w1) ->
      forall w, Satisfies m w phi) :
    Derivable (@BAxiom Atom) phi := by
  by_contra h_not_deriv
  -- Step 1: {neg phi} is B-consistent (standard boilerplate, identical to K)
  have h_cons : Modal.SetConsistent (@BAxiom Atom) ({Proposition.neg phi} : Set (Proposition Atom)) := by
    ... -- identical pattern to k_completeness / d_completeness
  -- Step 2: Lindenbaum extension
  obtain <M, hM_sup, hM_mcs> := modal_lindenbaum h_cons
  let w : CanonicalWorld (@BAxiom Atom) := <M, hM_mcs>
  -- Step 3: Show canonical model is symmetric
  have h_symm : forall (S T : CanonicalWorld (@BAxiom Atom)),
      (CanonicalModel (@BAxiom Atom)).r S T ->
      (CanonicalModel (@BAxiom Atom)).r T S :=
    canonical_symm
      (fun phi psi => .implyK phi psi)
      (fun phi psi chi => .implyS phi psi chi)
      (fun phi => .modalB phi)
      (fun phi psi => .modalK phi psi)
  -- Step 4: Contradiction via k_truth_lemma + h_valid
  exact mcs_not_mem_of_neg
    (fun phi psi => .implyK phi psi)
    (fun phi psi chi => .implyS phi psi chi)
    hM_mcs (hM_sup (Set.mem_singleton _))
    ((k_truth_lemma
      (fun phi psi => .implyK phi psi)
      (fun phi psi chi => .implyS phi psi chi)
      (fun phi => .efq phi)
      (fun phi psi => .peirce phi psi)
      (fun phi psi => .modalK phi psi)
      w phi).mp
      (h_valid (CanonicalWorld (@BAxiom Atom))
        (CanonicalModel (@BAxiom Atom))
        (fun S T hST => h_symm S T hST)
        w))
```

### 2.6 Symmetry Hypothesis Packaging

The `h_valid` takes symmetry as `forall w1 w2, m.r w1 w2 -> m.r w2 w1`. We need `canonical_symm` to produce evidence matching this. Looking at `canonical_symm`'s expected signature, it would prove `(CanonicalModel Axioms).r T S` given `(CanonicalModel Axioms).r S T`, which wraps neatly into the symmetry hypothesis for `h_valid`.

---

## 3. Task 100 Dependencies

Task 101 depends on task 100 for the following items:

### 3.1 Required from Task 100

| Item | Location | Purpose |
|------|----------|---------|
| `BAxiom` | `Instances.lean` | Axiom predicate for KB (K + B) |
| `Modal.HilbertB` | `ProofSystem.lean` | Tag type for B proof system |
| `ModalBHilbert` | `ProofSystem.lean` | Bundled class for B |
| `canonical_symm` | `Completeness.lean` | Canonical frame symmetry from axiom B |
| Instance registrations | `Instances.lean` | `InferenceSystem`, `HasAxiomB`, etc. for HilbertB |

### 3.2 Already Available (No Task 100 Dependency)

| Item | Location | Purpose |
|------|----------|---------|
| `Satisfies.b` | `Basic.lean:276` | Semantic validity of B on symmetric frames |
| `k_truth_lemma` | `KCompleteness.lean:168` | Truth lemma without axiom T |
| `k_mcs_box_witness` | `KCompleteness.lean:132` | Box witness without axiom T |
| `k_derive_box_from_inconsistency` | `KCompleteness.lean:51` | Consistency helper without axiom T |
| `mcs_box_diamond` | `MCS.lean:164` | `phi in S -> box(diamond(phi)) in S` (from axiom B) |
| `soundness` | `Soundness.lean:85` | Parameterized soundness |
| `soundness_derivable` | `Soundness.lean:108` | Parameterized soundness for derivable formulas |
| `modal_lindenbaum` | via MCS.lean | Lindenbaum's Lemma |
| `CanonicalModel` | `Completeness.lean:57` | Canonical model definition |
| `CanonicalWorld` | `Completeness.lean:50` | Canonical world type |

### 3.3 Blocker Assessment

Task 100 is `[NOT STARTED]`. However, the two files BSoundness.lean and BCompleteness.lean can be structured to compile once task 100 provides the dependencies. The proof structure is fully determined by the existing patterns.

**Blocker status**: Task 100 provides infrastructure (BAxiom, HilbertB, canonical_symm) that task 101 MUST import. Task 101 cannot be fully implemented and compiled until task 100 is complete.

**Mitigation**: The implementation plan can specify the exact code, and the implementer can write the files assuming the task 100 API. The build will succeed once task 100 lands.

---

## 4. File Structure

### 4.1 BSoundness.lean

```
Cslib/Logics/Modal/Metalogic/BSoundness.lean
  imports: Soundness, Instances
  namespace: Cslib.Logic.Modal
  
  Theorems:
  - b_axiom_sound: BAxiom phi -> symmetric model -> Satisfies m w phi
  - b_soundness: DerivationTree BAxiom Gamma phi -> symmetric model -> Satisfies
  - b_soundness_derivable: Derivable BAxiom phi -> symmetric model -> Satisfies
```

Lines: ~60 (similar to TSoundness at 89 lines, DSoundness at 91 lines)

### 4.2 BCompleteness.lean

```
Cslib/Logics/Modal/Metalogic/BCompleteness.lean
  imports: KCompleteness, Completeness (for canonical_symm), Instances
  namespace: Cslib.Logic.Modal
  
  Theorems:
  - b_completeness: phi valid on symmetric frames -> Derivable BAxiom phi
```

Lines: ~80 (similar to TCompleteness at 133 lines, but simpler since we reuse k_truth_lemma directly -- no new truth lemma needed)

### 4.3 Import Dependencies

```
BSoundness.lean:
  public import Cslib.Logics.Modal.Metalogic.Soundness
  public import Cslib.Logics.Modal.ProofSystem.Instances

BCompleteness.lean:
  public import Cslib.Logics.Modal.Metalogic.KCompleteness     -- k_truth_lemma
  public import Cslib.Logics.Modal.Metalogic.Completeness       -- canonical_symm, CanonicalModel
  public import Cslib.Logics.Modal.ProofSystem.Instances         -- BAxiom
```

Note: BCompleteness does NOT import BSoundness (soundness and completeness are independent).

---

## 5. Key Insights and Risks

### 5.1 Why k_truth_lemma and NOT truth_lemma

The `truth_lemma` in Completeness.lean has a parameter `h_T : forall phi, Axioms ((box phi).imp phi)`. This is axiom T. Modal logic B does NOT include axiom T. Using `truth_lemma` would require passing a proof that BAxiom implies axiom T, which is false.

The `k_truth_lemma` in KCompleteness.lean avoids this by using `k_mcs_box_witness` which relies on EFQ + `derive_box_from_box_context` instead of axiom T. BAxiom includes EFQ and K, so this works.

### 5.2 No New Truth Lemma Needed

Unlike D completeness (which needed `truth_lemma_d` with axiom D for box witness consistency), B completeness can directly reuse `k_truth_lemma`. The box witness for B uses the same EFQ-based approach as K.

This is because:
- K's box witness needs: implyK, implyS, efq, peirce, modalK -- all present in BAxiom
- B's extra axiom (modalB) is only needed for `canonical_symm`, not for the truth lemma

### 5.3 Proof Complexity

BSoundness: Trivial. The modalB case is a 3-line proof (intro, symmetry, exact). Total file ~60 lines.

BCompleteness: Moderate. The consistency argument (step 2 in the proof) is boilerplate copied from k_completeness. The main novelty is instantiating canonical_symm and connecting it to h_valid. Total file ~80 lines.

### 5.4 Risk: canonical_symm Signature

The exact signature of `canonical_symm` from task 100 is not yet determined. The proof in BCompleteness.lean will need to match whatever task 100 provides. Based on the existing patterns (canonical_refl, canonical_trans, canonical_eucl), the signature should be:

```lean
theorem canonical_symm
    {Axioms : Proposition Atom -> Prop}
    (h_implyK : forall (phi psi : Proposition Atom), Axioms (phi.imp (psi.imp phi)))
    (h_implyS : forall (phi psi chi : Proposition Atom),
      Axioms ((phi.imp (psi.imp chi)).imp ((phi.imp psi).imp (phi.imp chi))))
    (h_B : forall (phi : Proposition Atom),
      Axioms (phi.imp (Proposition.box (Proposition.diamond phi))))
    (h_K : forall (phi psi : Proposition Atom),
      Axioms ((Proposition.box (phi.imp psi)).imp
        ((Proposition.box phi).imp (Proposition.box psi))))
    (S T : CanonicalWorld Axioms) :
    (CanonicalModel Axioms).r S T ->
    (CanonicalModel Axioms).r T S
```

If task 100 uses a different signature (e.g., bundling S and T differently, or requiring additional axiom hypotheses), the BCompleteness proof will need adjustment. This is a low risk since the pattern is well-established.

---

## 6. Tactic Survey Results

| Goal | Likely Tactic | Notes |
|------|---------------|-------|
| Propositional axiom cases (implyK, implyS, efq, peirce) | `intro` + `exact`/`absurd` | Direct, no automation needed |
| modalK case | `intro` + `exact` | 2-line proof, same as all other soundness files |
| modalB case | `intro` + `exact` | 3-line proof using symmetry |
| Consistency argument (completeness) | Boilerplate from k_completeness | ~30 lines, mechanical copy |
| Truth lemma application | Direct call to k_truth_lemma | Instantiate at BAxiom constructors |
| canonical_symm application | Direct call | Instantiate at BAxiom.modalB and BAxiom.modalK |

No automation (simp, omega, aesop, decide) is needed for any of these proofs. They are all direct term-level constructions.

---

## 7. Summary

- **BSoundness.lean**: Straightforward, ~60 lines. Pattern from KSoundness/TSoundness. The `modalB` case uses symmetry directly.
- **BCompleteness.lean**: Moderate, ~80 lines. Uses `k_truth_lemma` (NOT `truth_lemma`!) since B lacks axiom T. Uses `canonical_symm` from task 100 for the frame property.
- **Dependencies**: Task 100 must provide BAxiom, HilbertB, canonical_symm. All other infrastructure exists.
- **No new truth lemma**: Unlike D completeness, B completeness reuses k_truth_lemma directly.
- **Risk**: Low. The proof structure is fully determined. The only uncertainty is the exact canonical_symm signature from task 100.
