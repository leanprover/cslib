# Literature Proof Structure: Canonical Model Completeness for K and T

## Sources

1. **Hebert, "Completeness in Modal Logic"** (UChicago REU 2020) -- Full canonical model completeness proofs for K, KT, KB, K4, S4, S5
2. **Platzer, "Completeness and Canonical Models"** (CMU 15-816 Lecture 20, 2010) -- Canonical Kripke structure construction, completeness for K and T
3. **Sergot, "Canonical models for normal logics"** (Imperial College 499, 2008) -- Detailed proofs with both box/diamond formulations of accessibility

## Common Proof Architecture

All three sources follow the same high-level structure:

### Step 1: MCS Properties (shared infrastructure)
- Negation completeness: for any MCS Gamma and formula A, either A in Gamma or neg A in Gamma
- Closure under MP: if A in Gamma and A -> B in Gamma, then B in Gamma
- Contains all theorems: if |- A then A in Gamma
- Lindenbaum's Lemma: every consistent set extends to an MCS

### Step 2: Canonical Model Definition
- Worlds: W^Sigma = set of all Sigma-MCS
- Accessibility: w R^Sigma w' iff for all A, box A in w implies A in w'
  - Equivalent (Chellas Thm 4.29): w R w' iff for all A, A in w' implies diamond A in w
- Valuation: V(p) = {w | p in w}

### Step 3: Truth Lemma (by induction on formula structure)
For every world w in M^Sigma and formula A:
  M^Sigma, w |= A iff A in w

- Base (atom p): by definition of V
- Base (bot): bot never satisfied; bot not in MCS (consistency)
- Case (neg A): M, w |= neg A iff not M, w |= A iff (IH) A not in w iff neg A in w
- Case (A -> B): uses MCS closure under MP and negation completeness
- Case (box A): the KEY case
  - Left-to-right (box A in w implies M, w |= box A): by definition of R and IH
  - Right-to-left (box A not in w implies exists w' with w R w' and A not in w'):
    THIS IS THE EXISTENCE LEMMA / BOX WITNESS

### Step 4: Box Witness / Existence Lemma

**Statement**: If box A not in w (MCS), then there exists MCS w' with w R w' and A not in w'.

**Proof** (Hebert Lemma 3.8, Platzer Lemma 7, Sergot Truth Lemma box case):
1. Define W = {B | box B in w} union {neg A}
2. Show W is consistent:
   - Suppose not: there exist box B_1, ..., box B_n in w such that |- (B_1 & ... & B_n) -> A
   - By generalization (necessitation): |- box((B_1 & ... & B_n) -> A)
   - By K distribution + Lemma 3.5: |- (box B_1 & ... & box B_n) -> box A
   - Since all box B_i in w (MCS), box A in w -- contradiction
3. By Lindenbaum, extend W to MCS w'
4. By construction: w R w' (all box-contents of w are in w') and A not in w' (neg A in w')

### Step 5: Completeness for K

**Theorem** (Hebert 4.4, Platzer Prop 11, Sergot Thm 9): K is complete w.r.t. all frames.

**Proof**: The canonical model M^K for K is a Kripke model (no conditions needed on the frame). By the canonical model theorem (Truth Lemma + Lindenbaum), K is complete w.r.t. M^K. Since M^K IS a Kripke model (with an arbitrary frame), K is complete w.r.t. all frames.

More precisely: Suppose phi is valid in all frames. Then phi is valid in M^K. If phi were not a K-theorem, then {neg phi} would be K-consistent, extendable to MCS w, and by Truth Lemma, M^K, w |= neg phi -- contradiction.

### Step 6: Canonical Frame Properties for T

**Lemma** (Hebert 4.5, Platzer Prop 12, Sergot S4 example): If Sigma contains axiom T (box A -> A), then R^Sigma is reflexive.

**Proof**: Let w be MCS in M^Sigma. We show w R w, i.e., for all A, box A in w implies A in w.
- Suppose box A in w.
- Since T in Sigma: (box A -> A) in Sigma, hence in w (MCS contains all theorems).
- By MP closure: A in w. Done.

### Step 7: Completeness for T

**Theorem** (Hebert 4.6 table, Platzer Prop 12): KT is complete w.r.t. reflexive frames.

**Proof**: By Step 6, the canonical frame for KT is reflexive. By the canonical model theorem, KT is complete w.r.t. M^KT. Since the frame of M^KT is reflexive, KT is complete w.r.t. the class of reflexive frames.

### Step 8: Soundness (straightforward)

**K Soundness**: Every K-axiom is valid in all frames.
- Propositional axioms: valid in all models (standard)
- K distribution: box(A -> B) -> (box A -> box B) valid in all frames (Hebert notes "straightforward")

**T Soundness**: Every T-axiom is valid in reflexive frames.
- All K-axioms: valid in all frames, hence in reflexive frames
- Axiom T (box A -> A): if w satisfies box A and R is reflexive, then w R w, so w satisfies A

## Dependencies Between Lemmas

```
Lindenbaum ─────────────────────────┐
                                     v
MCS Properties ──> Truth Lemma ──> Canonical Model Theorem ──> Completeness for K
                        |
                        v
               Box Witness (needs K axiom + necessitation)
                                                              ──> Completeness for T
               Canonical Reflexivity (needs T axiom)         /
```

## Key Difference Between K and S5 Box Witness

In the existing S5 implementation (MCS.lean), `derive_box_from_inconsistency` uses `h_T` in the else-branch where `neg phi not in L`. This branch handles the case where all elements of L are from {psi | box psi in S}.

For K (no axiom T), this branch needs different handling:
- If L = {psi_1, ..., psi_n} with all box psi_i in S, and L |- bot
- By derive_box_from_box_context: box bot in S
- From K axioms: |- bot -> phi (EFQ), so by necessitation |- box(bot -> phi)
- By K distribution: box(bot -> phi) -> (box bot -> box phi) is a theorem, hence in S
- So box bot -> box phi in S, and box bot in S, giving box phi in S -- contradiction

Alternatively (simpler): from L |- bot, derive L |- phi (via EFQ + MP), then by derive_box_from_box_context, box phi in S -- contradiction.

## Potential Formalization Challenges

1. **K Box Witness**: Need to generalize `derive_box_from_inconsistency` to not require `h_T`. The fix is simple: in the else branch, instead of showing each element is in S, use `derive_box_from_box_context` to derive `box bot` directly, then derive `box phi` from it.

2. **Truth Lemma reuse**: The existing truth_lemma takes `h_T` as parameter. For K completeness, we need a truth lemma that does NOT require `h_T`. This requires a K-specific box witness.

3. **Soundness for K**: Need to prove each KAxiom is valid on arbitrary frames. The propositional axioms are trivially valid. The K distribution axiom validity follows the same pattern as in axiom_sound but without frame conditions.

4. **Soundness for T**: Need to prove each TAxiom is valid on reflexive frames. Inherits propositional + K from above, plus T validity on reflexive frames.
