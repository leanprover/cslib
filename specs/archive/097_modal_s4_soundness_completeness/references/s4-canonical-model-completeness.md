# S4 Canonical Model Completeness -- Literature Extraction

## Sources

1. **Hebert, "Completeness in Modal Logic"** (U. Chicago REU, 2020)
   - Full canonical model completeness proof for S4 and S5
   - Reference: Blackburn, de Rijke, Venema "Modal Logic" Ch. 4
2. **Platzer, "Completeness and Canonical Models"** (CMU 15-816, Lecture 20, 2010)
   - Normal modal logic proof systems, canonical Kripke structures, completeness
3. **Sergot, "Canonical models for normal logics"** (Imperial College 499, 2008)
   - Detailed S4 completeness proof with reflexivity and transitivity verification

## Canonical Model Definition

For a normal modal logic Lambda with axiom predicate Axioms:

- **Worlds**: W^Lambda = set of all maximally Lambda-consistent sets (MCS)
- **Accessibility**: R(S, T) iff for all phi, if Box(phi) in S then phi in T
- **Valuation**: V(p) = { S in W^Lambda | atom(p) in S }

## Key MCS Properties

1. **Negation completeness**: For any phi, either phi in S or neg(phi) in S
2. **Closure under MP**: If phi in S and (phi -> psi) in S, then psi in S
3. **Contains all theorems**: Lambda subset of S
4. **Conjunction**: phi, psi in S iff (phi and psi) in S
5. **Bot not in S**: S is consistent, so bot not in S

## Lindenbaum's Lemma

Every Lambda-consistent set extends to an MCS.
Construction: enumerate formulas, at each step add phi_n or neg(phi_n).

## Existence Lemma / Box Witness

**Statement**: If Box(phi) not in S (MCS), then there exists T (MCS) such that
R(S, T) (i.e., for all psi, Box(psi) in S implies psi in T) and phi not in T.

**Construction**: Let W = { psi | Box(psi) in S } union { neg(phi) }.
Show W is consistent (proof by contradiction using K axiom distribution).
Extend W to MCS T via Lindenbaum. Then R(S,T) and neg(phi) in T, so phi not in T.

## Truth Lemma

**Statement**: For all phi and all MCS S: Satisfies(M^Lambda, S, phi) iff phi in S.

**Proof by structural induction on phi**:
- atom(p): by valuation definition
- bot: never satisfied, and bot not in MCS (consistency)
- imp(phi, psi): uses MCS closure under MP, negation completeness, Peirce's law
- box(phi): forward by R definition; backward by Existence Lemma + IH

## S4 Frame Properties

### Reflexivity (from Axiom T: Box(phi) -> phi)

**Claim**: R^S4(S, S) for all MCS S.

**Proof** (Sergot, Imperial College):
Suppose Box(A) in S. Since S4 contains schema T (Box(A) -> A) and S is
S4-maxi-consistent, it follows that A in S. Done.

In this project's notation: this is exactly `mcs_box_closure` applied with h_T.

### Transitivity (from Axiom 4: Box(phi) -> Box(Box(phi)))

**Claim**: R^S4(S, T) and R^S4(T, U) implies R^S4(S, U).

**Proof** (Sergot, Imperial College):
Suppose (1) R^S4(S, T), i.e., { A | Box(A) in S } subset T
and (2) R^S4(T, U), i.e., { A | Box(A) in T } subset U.
We need: for all A, Box(A) in S implies A in U.

So: suppose Box(A) in S.
- Box(A) in S implies Box(Box(A)) in S  (axiom 4, S is maxi)
- Box(Box(A)) in S implies Box(A) in T  (S R^S4 T)
- Box(A) in T implies A in U            (T R^S4 U)
Done.

In this project's notation: this is exactly `canonical_trans` using `mcs_box_box`.

## S4 Completeness Theorem Structure

**Theorem**: If phi is valid over all reflexive, transitive frames, then phi is S4-derivable.

**Proof**:
1. Suppose phi is not S4-derivable.
2. Then { neg(phi) } is S4-consistent.
3. By Lindenbaum, extend to MCS M containing neg(phi).
4. M is a world in the canonical model.
5. The canonical model is reflexive (from T) and transitive (from 4).
6. By the Truth Lemma, phi is not satisfied at M.
7. But phi was assumed valid over all reflexive transitive frames -- contradiction.

## S4 Soundness

**Theorem**: If Gamma |-_{S4} phi, then phi is valid over all reflexive, transitive frames.

For S4, we must show each S4 axiom is valid on reflexive + transitive frames:
- implyK, implyS, efq, peirce: propositional, valid on all frames
- modalK: valid on all frames (distribution)
- modalT: valid on reflexive frames (Box(phi) -> phi at w requires R(w,w))
- modalFour: valid on transitive frames (Box(phi) -> Box(Box(phi)) at w)

The axiom_sound function in Soundness.lean already proves all 8 axiom cases.
For S4, we need only the first 7 (not modalB). The existing proof handles T and 4
directly -- the h_eucl parameter is not used for T/4 cases.

## Mapping to Existing Lean Infrastructure

### Already Available (no new code needed for these):
- `CanonicalWorld Axioms` -- worlds as MCS (Completeness.lean)
- `CanonicalModel Axioms` -- canonical Kripke model (Completeness.lean)
- `canonical_refl` -- reflexivity from axiom T (Completeness.lean, parameterized)
- `canonical_trans` -- transitivity from axiom 4 (Completeness.lean, parameterized)
- `truth_lemma` -- truth lemma parameterized over axioms (Completeness.lean)
- `mcs_box_witness` -- box witness construction (MCS.lean, parameterized)
- `mcs_box_closure` -- T-closure (MCS.lean)
- `mcs_box_box` -- 4-closure (MCS.lean)
- `modal_lindenbaum` -- Lindenbaum's lemma (MCS.lean)
- `axiom_sound` -- S5 axiom soundness covering all 8 axioms (Soundness.lean)
- `soundness` -- parameterized soundness theorem (Soundness.lean)
- `S4Axiom` -- axiom predicate for S4 (Instances.lean)

### New Code Needed:
- `s4_axiom_sound` -- prove each S4Axiom is valid on reflexive+transitive frames
- `s4_soundness` -- S4-specific wrapper combining s4_axiom_sound + soundness
- `s4_completeness` -- instantiate completeness at S4Axiom with refl + trans only
