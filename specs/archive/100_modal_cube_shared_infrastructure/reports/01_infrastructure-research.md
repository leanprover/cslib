# Task 100: Modal Cube Shared Infrastructure -- Research Report

## Summary

This report covers three areas of the modal cube shared infrastructure:
1. Canonical frame property proofs (`canonical_symm`, `canonical_eucl_from_5`)
2. Ten new tag types and bundled classes for `ProofSystem.lean`
3. Ten new axiom predicates and instance registrations for `Instances.lean`

All findings are grounded in BRV (Blackburn, de Rijke, Venema 2002, Chapter 4).

---

## Literature Proof Structure

**Source**: Blackburn, de Rijke, Venema. *Modal Logic*. Cambridge, 2002. Chapter 4.
**Strategy**: Completeness-via-canonicity (Theorem 4.22 + Definition 4.30)

### Step Map

1. **Canonicity of B (Theorem 4.28, clause 2)**: The canonical frame of any normal logic containing axiom B is symmetric.
2. **Canonicity of 5 (standard result)**: The canonical frame of any normal logic containing axiom 5 is Euclidean.
3. **Composability (Theorem 4.29 + Definition 4.30)**: All canonical axioms compose -- any combination yields a canonical (hence complete) logic.
4. **Tag types and bundled classes**: One per logic in the modal cube.
5. **Axiom predicates and instances**: One axiom predicate inductive type per logic, with instance registrations connecting tags to `DerivationTree`.

### Dependencies
- Steps 4 and 5 are independent of Steps 1 and 2
- Steps 1 and 2 are independent of each other
- Step 3 is the theoretical justification that Steps 1-2 are sufficient

---

## Part 1: canonical_symm (from axiom B alone)

### BRV Theorem 4.28 Clause 2 -- Proof Analysis

**Theorem**: The canonical frame of any normal logic containing axiom B is symmetric.

**Proof** (BRV): Let `w` and `v` be points such that `R^KB wv`, and suppose `phi in w`. As `w` is a KB-MCS, `phi -> box(diamond(phi)) in w`, thus by modus ponens `box(diamond(phi)) in w`. Hence by Lemma 4.19 (canonical relation characterization), `diamond(phi) in v`. But this means `R^KB vw`, as required.

### Lean Formalization Strategy

**Goal signature**:
```lean
theorem canonical_symm
    {Axioms : Proposition Atom -> Prop}
    (h_implyK : forall (phi psi : Proposition Atom), Axioms (phi.imp (psi.imp phi)))
    (h_implyS : forall (phi psi chi : Proposition Atom),
      Axioms ((phi.imp (psi.imp chi)).imp ((phi.imp psi).imp (phi.imp chi))))
    (h_B : forall (phi : Proposition Atom),
      Axioms (phi.imp (Proposition.box (Proposition.diamond phi))))
    (S T : CanonicalWorld Axioms) :
    (CanonicalModel Axioms).r S T ->
    (CanonicalModel Axioms).r T S
```

**Proof sketch** (step-by-step in Lean terms):

1. Assume `hST : (CanonicalModel Axioms).r S T` -- i.e., `forall phi, box phi in S.val -> phi in T.val`
2. Goal: show `(CanonicalModel Axioms).r T S` -- i.e., `forall phi, box phi in T.val -> phi in S.val`
3. Take arbitrary `phi` and assume `h_box_T : box phi in T.val`
4. Need to show: `phi in S.val`
5. By contradiction: assume `h_not : phi not in S.val`
6. By `mcs_neg_of_not_mem`: `neg phi in S.val` (i.e., `(phi.imp .bot) in S.val`)
7. By `mcs_box_diamond` (uses axiom B): `box(diamond(neg phi)) in S.val`
   - Note: `diamond(neg phi) = (box(neg(neg phi))).imp .bot = (box((phi.imp .bot).imp .bot)).imp .bot`
8. By `hST`: `diamond(neg phi) in T.val`
   - i.e., `(box((phi.imp .bot).imp .bot)).imp .bot in T.val`
9. Now we need `box((phi.imp .bot).imp .bot) in T.val` to derive a contradiction via MP.
10. From `h_box_T : box phi in T.val`, we can derive `box((phi.imp .bot).imp .bot) in T.val` using axiom K and a derivation of `phi -> (phi.imp .bot) -> .bot` (which is a propositional tautology).
    - Actually, `(phi.imp .bot).imp .bot` is double negation `neg(neg phi)`.
    - So we need `box(neg neg phi) in T.val` from `box phi in T.val`.
    - Derivation: from `phi` derive `neg neg phi` via propositional logic (using implyK to get `phi -> (neg phi -> phi)`, then the rest is standard). Then by necessitation of the implication `phi -> neg neg phi`, plus axiom K, get `box phi -> box(neg neg phi)`.
    - In the codebase: use `derive_box_from_box_context` or direct construction with `mcs_box_mp`.
11. Having `box(neg neg phi) in T.val` and `diamond(neg phi) = (box(neg neg phi)).imp .bot in T.val`, we get `bot in T.val` by `modal_implication_property`.
12. But `bot not in T.val` by `mcs_bot_not_mem`. Contradiction.

**Key helper needed**: A lemma or inline derivation showing `box phi in T.val -> box(neg neg phi) in T.val`. This requires building the propositional derivation `phi -> ((phi -> bot) -> bot)` and then using necessitation + K distribution.

The derivation `phi -> ((phi -> bot) -> bot)` is:
```
From context [phi, phi -> bot]:
  - phi (assumption)
  - phi -> bot (assumption)
  - bot (MP)
By deduction theorem twice: [] |- phi -> ((phi -> bot) -> bot)
```
This is exactly the `d_dni` derivation pattern already used in `canonical_eucl` (lines 131-133 of Completeness.lean).

**Existing infrastructure used**:
- `mcs_neg_of_not_mem` -- get negation from non-membership
- `mcs_box_diamond` -- axiom B application (already exists!)
- `mcs_box_mp` -- box distribution (axiom K application)
- `modal_implication_property` -- MP in MCS
- `mcs_bot_not_mem` -- bot not in MCS
- `derive_box_from_box_context` or direct DerivationTree construction
- `deductionTheorem` -- for building derivations
- `DerivationTree.necessitation` -- for necessitating derivations

**Difficulty assessment**: Moderate. The proof follows the BRV argument directly. The only non-trivial part is the double-negation introduction derivation `phi -> neg neg phi`, but this pattern already appears in `canonical_eucl`.

---

## Part 2: canonical_eucl_from_5 (from axiom 5 alone)

### Literature Basis

**Standard result** (not explicitly in BRV as a standalone theorem, but follows from the canonicity framework + Definition 4.30):

The canonical frame of any normal logic containing axiom 5 is Euclidean.

**Proof**: Suppose `R(w,v)` and `R(w,u)`, and `phi in u`. 
1. By `R(w,u)` and `phi in u`: `diamond(phi) in w` (by definition of canonical relation -- the *reverse* direction needs care).
   - Actually, `R(w,u)` means `forall psi, box psi in w -> psi in u`. We need to show `diamond(phi) in w`.
   - This is NOT immediate from the definition of R. We need: `phi in u` and `R(w,u)` implies `diamond(phi) in w`.
   - In the codebase canonical model: `R w u` iff `forall psi, box psi in w -> psi in u`.
   - So `R(w,u)` does NOT directly give us `diamond(phi) in w` from `phi in u`.
   - We need to use the MCS property: if `diamond(phi) not in w`, then `neg(diamond(phi)) in w`, i.e., `box(neg phi) in w`, so by R(w,u): `neg phi in u`, contradicting `phi in u`.

2. So: `diamond(phi) in w` (from step 1).
3. By axiom 5 (`diamond(phi) -> box(diamond(phi))`): `box(diamond(phi)) in w` (by modus ponens).
4. By `R(w,v)`: `diamond(phi) in v`.
5. So `R(v,u)` holds: for any `phi`, if `phi in u` then `diamond(phi) in v`. But wait, `R(v,u)` means `forall psi, box psi in v -> psi in u`, which is the other direction.

Let me reconsider. We need to show `R(v,u)`, which means: `forall psi, box psi in v -> psi in u`.

**Corrected proof**:
Suppose `R(w,v)` and `R(w,u)`. We need `R(v,u)`, i.e., `forall psi, box psi in v -> psi in u`.

Take arbitrary `psi` and assume `box psi in v`. We need `psi in u`.

By contradiction: assume `psi not in u`. Then `neg psi in u` (MCS property).
By `R(w,u)`: if `box(neg psi) in w` then `neg psi in u`. But we need the reverse. Let's think again.

Actually, the standard proof goes:

Take `psi` with `box psi in v.val`. Need: `psi in u.val`.

By contradiction: assume `psi not in u.val`. Then `neg psi in u.val`.

From `neg psi in u.val` and `R(w,u)`: We need `diamond(neg psi) in w.val`.
- If `diamond(neg psi) not in w.val`, then `neg(diamond(neg psi)) in w.val`, i.e., `box(neg(neg psi)) = box(neg neg psi) in w.val`.
- By `R(w,u)`: `neg neg psi in u.val`.
- But `neg psi in u.val` and `neg neg psi in u.val` gives `bot in u.val`, contradiction.
- So `diamond(neg psi) in w.val`.

From `diamond(neg psi) in w.val` and axiom 5: `box(diamond(neg psi)) in w.val`.
By `R(w,v)`: `diamond(neg psi) in v.val`.
So `(box(neg(neg psi))).imp .bot in v.val` (unfolding diamond).

From `box psi in v.val`, derive `box(neg neg psi) in v.val` (same double-negation introduction pattern as in `canonical_symm`).

By `modal_implication_property`: `bot in v.val`. Contradiction with `mcs_bot_not_mem`.

### Lean Formalization Strategy

**Goal signature**:
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

**Proof sketch**:

1. Assume `hST` and `hSU`. Take `phi` with `h_box_T : box phi in T.val`. Need `phi in U.val`.
2. By contradiction: assume `phi not in U.val`.
3. `neg phi in U.val` (by `mcs_neg_of_not_mem`).
4. Claim: `diamond(neg phi) in S.val`.
   - By contradiction: if not, then `neg(diamond(neg phi)) in S.val`, i.e., `box(neg(neg phi)) in S.val`.
   - By `hSU`: `neg(neg phi) in U.val`, i.e., `((neg phi).imp .bot) in U.val`.
   - By `modal_implication_property` with `neg phi in U.val`: `bot in U.val`. Contradiction.
5. By axiom 5 + MP: `box(diamond(neg phi)) in S.val`.
   - Use `mcs_mp_axiom` with `h_5 (neg phi)` (= `h_5 (phi.imp .bot)`).
   - Wait: axiom 5 says `diamond(phi) -> box(diamond(phi))` for any `phi`. So for `neg phi`:
   - `h_5 (Proposition.neg phi)` gives `Axioms (diamond(neg phi).imp (box(diamond(neg phi))))`.
   - But actually `Axiom5` is defined on the *parameter* `phi`, meaning `Axiom5 phi = diamond(phi) -> box(diamond(phi))`.
   - We want to apply it with `neg phi` as the argument: `diamond(neg phi) -> box(diamond(neg phi))`.
   - Hmm, actually looking at the definition: `Axiom5 (phi : F) = (diamond phi).imp (box(diamond phi))`.
   - So `h_5 (neg phi)` is not directly available because `h_5` universally quantifies over all `phi`.
   - Actually yes: `h_5 : forall (phi : Proposition Atom), Axioms (Axiom5 phi)`. We can instantiate with `Proposition.neg phi` or any formula.
   - But the `HasAxiom5` typeclass says `five {phi : F} : ... (Axioms.Axiom5 phi)`, so `phi` is implicit and universally quantified.
   - In the parameterized canonical proof, `h_5` will be a hypothesis like `h_5 : forall (phi : Proposition Atom), Axioms ((Proposition.diamond phi).imp (Proposition.box (Proposition.diamond phi)))`. We can substitute any formula for `phi`.
   - So `h_5 (Proposition.neg phi)` gives the needed axiom instance.
6. By `hST`: `diamond(neg phi) in T.val`.
7. From `box phi in T.val`, derive `box(neg neg phi) in T.val` (double-negation introduction, same pattern as `canonical_symm`).
8. `diamond(neg phi) = (box(neg(neg phi))).imp .bot`. Together with `box(neg neg phi) in T.val`, by `modal_implication_property`: `bot in T.val`. Contradiction.

**Key observation about h_5 type**: The hypothesis must match the `Axiom5` definition exactly. Looking at `Axioms.lean`:
```lean
protected abbrev Axiom5 (phi : F) : F :=
  HasImp.imp
    (HasImp.imp (HasBox.box (HasImp.imp phi HasBot.bot)) HasBot.bot)
    (HasBox.box (HasImp.imp (HasBox.box (HasImp.imp phi HasBot.bot)) HasBot.bot))
```

So `Axiom5 phi` unfolds to `diamond(phi) -> box(diamond(phi))` where `diamond(phi) = (box(phi -> bot)) -> bot`.

The `h_5` hypothesis should be:
```lean
h_5 : forall (phi : Proposition Atom),
  Axioms ((Proposition.diamond phi).imp (Proposition.box (Proposition.diamond phi)))
```
which unfolds to:
```lean
h_5 : forall (phi : Proposition Atom),
  Axioms (((Proposition.box (phi.imp .bot)).imp .bot).imp
    (Proposition.box ((Proposition.box (phi.imp .bot)).imp .bot)))
```

When we substitute `phi := Proposition.neg psi = psi.imp .bot`, we get:
```
diamond(neg psi) -> box(diamond(neg psi))
= ((box((psi.imp .bot).imp .bot)).imp .bot).imp (box((box((psi.imp .bot).imp .bot)).imp .bot))
```

And `diamond(neg psi) = (box(neg neg psi)).imp .bot = (box((psi.imp .bot).imp .bot)).imp .bot`.

So in the proof, when we have `diamond(neg phi) in S.val` and apply `h_5 (Proposition.neg phi)`, we get `box(diamond(neg phi)) in S.val` as needed.

**Shared derivation helper**: Both `canonical_symm` and `canonical_eucl_from_5` need the derivation `box phi -> box(neg neg phi)`. This should be factored as a helper lemma:

```lean
theorem mcs_box_double_neg_intro
    {Axioms : Proposition Atom -> Prop}
    (h_implyK : ...)
    (h_implyS : ...)
    (h_K : ...)
    {S : Set (Proposition Atom)} (h_mcs : Modal.SetMaximalConsistent Axioms S)
    {phi : Proposition Atom} (h_box : Proposition.box phi in S) :
    Proposition.box (Proposition.neg (Proposition.neg phi)) in S
```

This is derivable as follows:
1. Build `d_dni : DerivationTree Axioms [] (phi.imp ((phi.imp .bot).imp .bot))` (double negation introduction -- same derivation as in `canonical_eucl` lines 127-133).
2. Necessitate: `d_nec : DerivationTree Axioms [] (box(phi.imp ((phi.imp .bot).imp .bot)))`.
3. This gives `box(phi -> neg neg phi) in S` (by `modal_closed_under_derivation`).
4. By `mcs_box_mp`: `box(neg neg phi) in S`.

Actually, this is exactly what `canonical_eucl` does at lines 130-141. The shared helper avoids duplicating this code.

**Difficulty assessment**: Moderate. Similar structure to `canonical_symm` but with an extra step (establishing `diamond(neg phi) in S.val` via contradiction). The double-negation derivation is the same shared pattern.

---

## Part 3: Comparison with existing canonical_eucl

The existing `canonical_eucl` (lines 94-141 of Completeness.lean) proves Euclideanness from axioms B + T + 4:
- Uses axiom 4 to get `box box phi in T.val`
- Uses axiom B on `neg(box phi)` to get `box(diamond(neg(box phi))) in S.val`
- Uses a complex double-negation argument

The new `canonical_eucl_from_5` is **much simpler** because it uses axiom 5 directly:
- `diamond(neg phi) in S.val` (one contradiction step)
- Axiom 5 gives `box(diamond(neg phi)) in S.val` directly (one MP)
- The rest is the same diamond/box contradiction

The existing `canonical_eucl` will remain valid (S5 = K+T+4+B uses it). The new `canonical_eucl_from_5` is needed for logics like K5, K45, D5, D45, KB5 which have axiom 5 but not necessarily B+T+4.

---

## Part 4: Ten New Tag Types and Bundled Classes

### Tag Types (ProofSystem.lean)

The following 10 opaque tag types are needed, added after the existing tag types:

| # | Tag Type | Logic | Description |
|---|----------|-------|-------------|
| 1 | `Modal.HilbertB` | KB | K + axiom B |
| 2 | `Modal.HilbertK4` | K4 | K + axiom 4 |
| 3 | `Modal.HilbertK5` | K5 | K + axiom 5 |
| 4 | `Modal.HilbertK45` | K45 | K + axiom 4 + axiom 5 |
| 5 | `Modal.HilbertTB` | TB | K + axiom T + axiom B |
| 6 | `Modal.HilbertKB5` | KB5 | K + axiom B + axiom 5 |
| 7 | `Modal.HilbertD4` | D4 | K + axiom D + axiom 4 |
| 8 | `Modal.HilbertD5` | D5 | K + axiom D + axiom 5 |
| 9 | `Modal.HilbertD45` | D45 | K + axiom D + axiom 4 + axiom 5 |
| 10 | `Modal.HilbertDB` | DB | K + axiom D + axiom B |

### Bundled Classes (ProofSystem.lean)

Each logic needs a bundled class that extends the appropriate parent classes:

| # | Class | Extends | Additional |
|---|-------|---------|------------|
| 1 | `ModalBHilbert` | `ModalHilbert` | `HasAxiomB` |
| 2 | `ModalK4Hilbert` | `ModalHilbert` | `HasAxiom4` |
| 3 | `ModalK5Hilbert` | `ModalHilbert` | `HasAxiom5` |
| 4 | `ModalK45Hilbert` | `ModalK4Hilbert` | `HasAxiom5` |
| 5 | `ModalTBHilbert` | `ModalTHilbert` | `HasAxiomB` |
| 6 | `ModalKB5Hilbert` | `ModalBHilbert` | `HasAxiom5` |
| 7 | `ModalD4Hilbert` | `ModalDHilbert` | `HasAxiom4` |
| 8 | `ModalD5Hilbert` | `ModalDHilbert` | `HasAxiom5` |
| 9 | `ModalD45Hilbert` | `ModalD4Hilbert` | `HasAxiom5` (or `ModalDHilbert` + `HasAxiom4` + `HasAxiom5`) |
| 10 | `ModalDBHilbert` | `ModalDHilbert` | `HasAxiomB` |

**Note on naming**: The existing pattern uses `ModalTHilbert`, `ModalDHilbert`, `ModalS4Hilbert`, `ModalS5Hilbert`. Following this convention, new classes should use the logic name (e.g., `ModalBHilbert` for KB, `ModalK4Hilbert` for K4). Alternative: `ModalKBHilbert` for KB to match the standard nomenclature. The naming should be decided at implementation time but should be consistent.

**Note on S5 hierarchy**: The existing `ModalS5Hilbert extends ModalS4Hilbert, HasAxiomB`. Since S5 = K+T+4+B, this extends T (reflexive) + 4 (transitive) + B (symmetric). The new `canonical_eucl_from_5` means we could alternatively define S5 with axiom 5 directly, but the existing hierarchy is fine -- the `canonical_eucl` from B+T+4 already works for S5 completeness.

---

## Part 5: Ten New Axiom Predicates and Instance Registrations

### Axiom Predicates (Instances.lean)

Each logic needs an `inductive` axiom predicate listing its axiom schemata. Following the existing pattern (K=5, T=6, D=6, S4=7 constructors):

| Logic | Constructors | Propositional | Modal |
|-------|-------------|---------------|-------|
| KB (B) | 6 | implyK, implyS, efq, peirce | modalK, modalB |
| K4 | 6 | implyK, implyS, efq, peirce | modalK, modalFour |
| K5 | 6 | implyK, implyS, efq, peirce | modalK, modalFive |
| K45 | 7 | implyK, implyS, efq, peirce | modalK, modalFour, modalFive |
| TB | 7 | implyK, implyS, efq, peirce | modalK, modalT, modalB |
| KB5 | 7 | implyK, implyS, efq, peirce | modalK, modalB, modalFive |
| D4 | 7 | implyK, implyS, efq, peirce | modalK, modalD, modalFour |
| D5 | 7 | implyK, implyS, efq, peirce | modalK, modalD, modalFive |
| D45 | 8 | implyK, implyS, efq, peirce | modalK, modalD, modalFour, modalFive |
| DB | 7 | implyK, implyS, efq, peirce | modalK, modalD, modalB |

### Constructor Patterns for Modal Axioms

Each modal axiom constructor follows the same pattern as existing ones:

```lean
-- modalFive (axiom 5): diamond(phi) -> box(diamond(phi))
-- Encoding: ((box(phi -> bot)) -> bot) -> box((box(phi -> bot)) -> bot)
| modalFive (phi : Proposition Atom) :
    XAxiom (((Proposition.box (phi.imp .bot)).imp .bot).imp
      (Proposition.box ((Proposition.box (phi.imp .bot)).imp .bot)))
```

This matches the encoding of `Axiom5` in `Axioms.lean` (lines 112-115) and `Proposition.diamond` (line 72-73 of `Basic.lean`).

### Instance Registrations (Instances.lean)

Each logic needs these instances (following the existing K/T/D/S4/S5 pattern):

1. `InferenceSystem Modal.HilbertX (Modal.Proposition Atom)` -- connects tag to DerivationTree
2. `ModusPonens Modal.HilbertX` -- MP rule
3. `Necessitation Modal.HilbertX` -- NEC rule
4. `HasAxiomImplyK Modal.HilbertX` -- propositional axiom K
5. `HasAxiomImplyS Modal.HilbertX` -- propositional axiom S
6. `HasAxiomEFQ Modal.HilbertX` -- ex falso
7. `HasAxiomPeirce Modal.HilbertX` -- Peirce's law
8. `HasAxiomK Modal.HilbertX` -- modal axiom K
9. `HasAxiom{Y} Modal.HilbertX` -- each additional modal axiom (T, 4, B, 5, D as appropriate)
10. `ModalHilbert Modal.HilbertX` -- base bundled class
11. `Modal{Y}Hilbert Modal.HilbertX` -- each relevant bundled class up the hierarchy

### Instance Hierarchy

For each logic, the instance chain connects all bundled classes in the hierarchy:

| Logic | Bundled Class Instances (from most specific to ModalHilbert) |
|-------|-------------------------------------------------------------|
| KB | `ModalBHilbert`, `ModalHilbert` |
| K4 | `ModalK4Hilbert`, `ModalHilbert` |
| K5 | `ModalK5Hilbert`, `ModalHilbert` |
| K45 | `ModalK45Hilbert`, `ModalK4Hilbert`, `ModalHilbert` |
| TB | `ModalTBHilbert`, `ModalTHilbert`, `ModalHilbert` |
| KB5 | `ModalKB5Hilbert`, `ModalBHilbert`, `ModalHilbert` |
| D4 | `ModalD4Hilbert`, `ModalDHilbert`, `ModalHilbert` |
| D5 | `ModalD5Hilbert`, `ModalDHilbert`, `ModalHilbert` |
| D45 | `ModalD45Hilbert`, `ModalD4Hilbert`, `ModalDHilbert`, `ModalHilbert` |
| DB | `ModalDBHilbert`, `ModalDHilbert`, `ModalHilbert` |

---

## Part 6: File Placement

| Addition | File | Location in File |
|----------|------|-----------------|
| `canonical_symm` | `Completeness.lean` | After `canonical_trans`, before `canonical_eucl` |
| `canonical_eucl_from_5` | `Completeness.lean` | After `canonical_eucl` |
| `mcs_box_double_neg_intro` (optional helper) | `MCS.lean` | After `mcs_box_mp` |
| 10 tag types | `ProofSystem.lean` | After existing `Modal.HilbertS5` (line 388) |
| 10 bundled classes | `ProofSystem.lean` | After existing `ModalS5Hilbert` (line 325) |
| 10 axiom predicates | `Instances.lean` | After existing `S4Axiom` (line 155) |
| 10 instance registrations | `Instances.lean` | After existing S5 instances (line 501) |

---

## Part 7: Tactic Survey Results

Based on analysis of the existing proofs and the structure of the new proofs:

| Goal | Tactic | Expected Result | Notes |
|------|--------|-----------------|-------|
| MCS membership via axiom | `exact mcs_mp_axiom ...` | success | Standard pattern |
| DerivationTree construction | Manual `.modus_ponens`, `.ax`, `.assumption` | required | No automation available |
| Contradiction from `bot in S` | `exact mcs_bot_not_mem h_mcs h_bot` | success | Standard pattern |
| `neg phi from phi not in S` | `exact mcs_neg_of_not_mem ...` | success | Standard pattern |
| Instance declarations | `where` syntax with empty body | success | Lean synthesizes from extends |
| Axiom predicate constructors | Pattern matching on constructor | success | Standard inductive |
| `by_contra` for contradictions | `by_contra` | success | Standard |

Most of the proof construction is manual derivation tree building, following the established patterns in the codebase.

---

## Risk Assessment

1. **Low risk**: Tag types and bundled classes are purely additive, no existing code changes.
2. **Low risk**: Axiom predicates follow exact existing pattern (copy-paste + modify).
3. **Low risk**: Instance registrations follow exact existing pattern.
4. **Medium risk**: `canonical_symm` requires a careful double-negation derivation, but the pattern exists in `canonical_eucl`.
5. **Medium risk**: `canonical_eucl_from_5` is slightly more complex (establishing `diamond(neg phi) in S.val` via contradiction). The key challenge is making sure the diamond/box/neg encodings match up definitionally in Lean.

---

## BRV Citation Index

| Result | BRV Reference | Where Used |
|--------|--------------|------------|
| Canonical model definition | Definition 4.18 | `CanonicalModel` in Completeness.lean |
| Canonical relation characterization | Lemma 4.19 | Canonical relation definition |
| Existence Lemma | Lemma 4.20 | `mcs_box_witness` in MCS.lean |
| Truth Lemma | Lemma 4.21 | `truth_lemma` in Completeness.lean |
| Canonical Model Theorem | Theorem 4.22 | `completeness` in Completeness.lean |
| K4 transitivity is canonical | Theorem 4.27 | `canonical_trans` in Completeness.lean |
| KB symmetry is canonical | Theorem 4.28 clause 2 | **NEW** `canonical_symm` |
| KD seriality is canonical | Theorem 4.28 clause 3 | `canonical_serial` in DCompleteness.lean |
| Composability of canonical axioms | Theorem 4.29 + Def 4.30 | All combined completeness theorems |
| Axiom 5 canonical for Euclideanness | Standard (Def 4.30 pattern) | **NEW** `canonical_eucl_from_5` |
