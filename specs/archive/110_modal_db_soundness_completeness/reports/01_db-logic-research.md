# Research Report: Modal DB Soundness and Completeness

## Task Overview

**Task**: 110 -- Prove soundness and completeness for modal logic DB (K + D + B) over serial + symmetric frames.
**System**: DB = K + axiom D (seriality: box phi -> diamond phi) + axiom B (symmetry: phi -> box diamond phi)
**Frame Class**: Serial + symmetric (Relation.Serial m.r + forall w1 w2, m.r w1 w2 -> m.r w2 w1)

## Literature Proof Structure

**Source**: Blackburn, de Rijke, Venema, "Modal Logic" (2002), Chapter 4
**Strategy**: Completeness-via-canonicity (Theorem 4.22 pattern combined with Theorem 4.28 clauses 2 and 3)

### Step Map

1. **Soundness**: Verify each DBAxiom constructor is valid over serial + symmetric frames -- [BRV] Definition 4.9, Table 4.1
2. **Consistency of {neg phi}**: Standard contrapositive setup via deduction theorem and Peirce's law -- [BRV] Proposition 4.12
3. **Lindenbaum extension**: Extend consistent set to MCS -- [BRV] Lemma 4.17
4. **Canonical model construction**: CanonicalWorld/CanonicalModel parameterized over DBAxiom -- [BRV] Definition 4.18
5. **Canonical seriality**: canonical_serial from axiom D -- [BRV] Theorem 4.28, clause 3
6. **Canonical symmetry**: canonical_symm from axiom B -- [BRV] Theorem 4.28, clause 2
7. **Truth lemma (D-specific)**: truth_lemma_d using axiom D for box witness consistency -- [BRV] Lemma 4.21
8. **Completeness**: Combine steps 3-7 for contradiction -- [BRV] Theorem 4.22

### Dependencies
- Step 7 depends on Steps 4-5 (D-specific box witness uses axiom D)
- Step 8 depends on Steps 2, 3, 5, 6, 7

### Potential Formalization Challenges
- None identified. All components already exist in the codebase.

## Infrastructure Inventory

### All Required Components Already Exist

| Component | Location | Status |
|-----------|----------|--------|
| `DBAxiom` (7 constructors) | `Instances.lean:439-463` | EXISTS |
| `Modal.HilbertDB` tag type | `ProofSystem.lean:478` | EXISTS |
| `ModalDBHilbert` bundled class | `ProofSystem.lean:382-385` | EXISTS |
| All DB typeclass instances | `Instances.lean:1457-1529` | EXISTS |
| `canonical_serial` | `DCompleteness.lean:209-259` | EXISTS |
| `canonical_symm` | `Completeness.lean:99-139` | EXISTS |
| `truth_lemma_d` | `DCompleteness.lean:269-365` | EXISTS |
| `modal_lindenbaum` | `MCS.lean` | EXISTS |
| `mcs_not_mem_of_neg` | `MCS.lean` | EXISTS |
| `soundness` / `soundness_derivable` | `Soundness.lean` | EXISTS |
| `deductionTheorem` | `DeductionTheorem.lean` | EXISTS |
| `Satisfies.d` (semantic D validity) | `Basic.lean` | EXISTS |
| `Satisfies.b` (semantic B validity) | `Basic.lean` | EXISTS |

**Conclusion**: Zero new infrastructure is needed. Both files are pure assembly from existing components.

### DBAxiom Constructors (7 total)

From `Instances.lean:439-463`:

```
1. implyK    : phi -> (psi -> phi)
2. implyS    : (phi -> (psi -> chi)) -> ((phi -> psi) -> (phi -> chi))
3. efq       : bot -> phi
4. peirce    : ((phi -> psi) -> phi) -> phi
5. modalK    : box(phi -> psi) -> (box phi -> box psi)
6. modalD    : box phi -> diamond phi   [= box phi -> (box(phi -> bot)) -> bot]
7. modalB    : phi -> box(diamond phi)
```

## Implementation Design: DBSoundness.lean

### File Structure

```
module
public import Cslib.Logics.Modal.Metalogic.Soundness
public import Cslib.Logics.Modal.ProofSystem.Instances
```

### Theorem: db_axiom_sound

**Signature** (follow D4Soundness pattern):
```lean
theorem db_axiom_sound {World : Type*} {phi : Proposition Atom}
    (h_ax : DBAxiom phi) (m : Model World Atom)
    (h_serial : Relation.Serial m.r)
    (h_symm : forall w1 w2, m.r w1 w2 -> m.r w2 w1)
    (w : World) : Satisfies m w phi
```

**Case analysis** (7 cases):

| Case | Proof Strategy | Source Pattern |
|------|---------------|----------------|
| `implyK` | `intro hphi _; exact hphi` | All soundness files |
| `implyS` | `intro h1 h2 h3; exact h1 h3 (h2 h3)` | All soundness files |
| `efq` | `intro h; exact absurd h id` | All soundness files |
| `peirce` | `by_contra; apply` | All soundness files |
| `modalK` | `intro h_box_imp h_box_phi w' hr; exact h_box_imp w' hr (h_box_phi w' hr)` | All soundness files |
| `modalD` | Use `h_serial.serial w` for witness; apply h_box_neg | DSoundness.lean:61-68 |
| `modalB` | `intro hphi w' hr h_box_neg; exact h_box_neg w (h_symm w w' hr) hphi` | BSoundness.lean:62-68 |

### Theorem: db_soundness

**Signature**:
```lean
theorem db_soundness {World : Type*}
    {Gamma : List (Proposition Atom)} {phi : Proposition Atom}
    (d : DerivationTree (@DBAxiom Atom) Gamma phi)
    (m : Model World Atom)
    (h_serial : Relation.Serial m.r)
    (h_symm : forall w1 w2, m.r w1 w2 -> m.r w2 w1)
    (w : World)
    (h_ctx : forall psi in Gamma, Satisfies m w psi) : Satisfies m w phi :=
  soundness d m (fun psi h_ax w => db_axiom_sound h_ax m h_serial h_symm w) w h_ctx
```

### Theorem: db_soundness_derivable

One-liner using `soundness_derivable`.

### Estimated Size

~70 lines (following D4Soundness.lean which is 103 lines with similar structure).

## Implementation Design: DBCompleteness.lean

### File Structure

```
module
public import Cslib.Logics.Modal.Metalogic.Completeness
public import Cslib.Logics.Modal.Metalogic.DCompleteness
```

**Critical design choice**: Import both `Completeness` (for `canonical_symm`) and `DCompleteness` (for `truth_lemma_d` and `canonical_serial`).

### Key Design Decision: truth_lemma_d, NOT truth_lemma

DB contains axiom D but NOT axiom T. This is critical:
- `truth_lemma` (Completeness.lean) requires axiom T (`h_T` parameter)
- `truth_lemma_d` (DCompleteness.lean) requires axiom D (`h_D` parameter)
- DB must use `truth_lemma_d` because it has D, not T

This matches the D4Completeness pattern, NOT the TBCompleteness pattern.

### Theorem: db_completeness

**Signature** (follow D4Completeness pattern with symmetry replacing transitivity):
```lean
theorem db_completeness (phi : Proposition Atom)
    (h_valid : forall (World : Type u) (m : Model World Atom),
      Relation.Serial m.r ->
      (forall w1 w2, m.r w1 w2 -> m.r w2 w1) ->
      forall w, Satisfies m w phi) :
    Derivable (@DBAxiom Atom) phi
```

**Proof structure** (follows D4Completeness.lean exactly, replacing canonical_trans with canonical_symm):

1. `by_contra h_not_deriv` -- contrapositive
2. Build consistency of `{neg phi}` -- standard DNE derivation (identical boilerplate to all completeness proofs)
3. `obtain <M, hM_sup, hM_mcs> := modal_lindenbaum h_cons` -- Lindenbaum
4. `let w : CanonicalWorld (@DBAxiom Atom) := <M, hM_mcs>` -- canonical world
5. Show seriality: `canonical_serial` with `.implyK`, `.implyS`, `.efq`, `.modalK`, `.modalD`
6. Show symmetry: `canonical_symm` with `.implyK`, `.implyS`, `.modalK`, `.modalB`
7. Apply `truth_lemma_d` with `.implyK`, `.implyS`, `.efq`, `.peirce`, `.modalK`, `.modalD`
8. Apply `h_valid` with canonical model, serial, symmetric hypotheses
9. Contradiction via `mcs_not_mem_of_neg`

### Constructor Mapping for DB

The proof passes DBAxiom constructors to the parameterized lemmas:

| Parameter | DBAxiom Constructor |
|-----------|-------------------|
| `h_implyK` | `fun phi psi => .implyK phi psi` |
| `h_implyS` | `fun phi psi chi => .implyS phi psi chi` |
| `h_efq` | `fun phi => .efq phi` |
| `h_peirce` | `fun phi psi => .peirce phi psi` |
| `h_K` | `fun phi psi => .modalK phi psi` |
| `h_D` | `fun phi => .modalD phi` |
| `h_B` | `fun phi => .modalB phi` |

### Symmetry Proof Structure

```lean
have h_symm : forall (S T : CanonicalWorld (@DBAxiom Atom)),
    (CanonicalModel (@DBAxiom Atom)).r S T ->
    (CanonicalModel (@DBAxiom Atom)).r T S :=
  canonical_symm
    (fun phi psi => .implyK phi psi)
    (fun phi psi chi => .implyS phi psi chi)
    (fun phi psi => .modalK phi psi)
    (fun phi => .modalB phi)
```

### Seriality Proof Structure

```lean
have h_serial : Relation.Serial (CanonicalModel (@DBAxiom Atom)).r := by
  constructor
  intro S
  exact canonical_serial
    (fun phi psi => .implyK phi psi)
    (fun phi psi chi => .implyS phi psi chi)
    (fun phi => .efq phi)
    (fun phi psi => .modalK phi psi)
    (fun phi => .modalD phi)
    S
```

### Estimated Size

~90 lines (following D4Completeness.lean which is 147 lines but with identical boilerplate).

## Comparison with Closest Analogs

### DB vs D4 (task 107)

| Aspect | D4 | DB |
|--------|----|----|
| Axioms | D + 4 | D + B |
| Frame class | Serial + transitive | Serial + symmetric |
| Truth lemma | `truth_lemma_d` | `truth_lemma_d` |
| Canonical property 1 | `canonical_serial` | `canonical_serial` |
| Canonical property 2 | `canonical_trans` | `canonical_symm` |
| Soundness axiom cases | 7 (same 4 prop + K + D + 4) | 7 (same 4 prop + K + D + B) |
| Soundness D case | seriality witness | seriality witness |
| Soundness extra case | transitivity chain | symmetry flip |

### DB vs TB (task 105)

| Aspect | TB | DB |
|--------|----|----|
| Axioms | T + B | D + B |
| Frame class | Reflexive + symmetric | Serial + symmetric |
| Truth lemma | `truth_lemma` (T-based) | `truth_lemma_d` (D-based) |
| Reflexivity/seriality | `canonical_refl` | `canonical_serial` |
| Symmetry | `canonical_symm` | `canonical_symm` |

### DB vs B (task 101)

| Aspect | B | DB |
|--------|---|----|
| Axioms | B only | D + B |
| Frame class | Symmetric | Serial + symmetric |
| Truth lemma | `k_truth_lemma` (K-based) | `truth_lemma_d` (D-based) |
| Extra frame property | none | `canonical_serial` |
| Key difference | No seriality | Has seriality via D |

## Metalogic.lean Aggregator Update

After implementing DBSoundness.lean and DBCompleteness.lean, two import lines must be added to `Metalogic.lean`:

```lean
public import Cslib.Logics.Modal.Metalogic.DBSoundness
public import Cslib.Logics.Modal.Metalogic.DBCompleteness
```

**Note**: Task 111 is specifically designated for the aggregator update. The implementation task for 110 should add these imports or coordinate with task 111.

## Risk Assessment

**Risk Level**: MINIMAL

All proof components are reused from existing infrastructure. The implementation is purely mechanical assembly:
- Soundness: 7 cases, all with existing proof patterns
- Completeness: follows D4Completeness.lean with one substitution (canonical_symm for canonical_trans)

**No blockers identified**.

## Verification Plan

1. `lake build Cslib.Logics.Modal.Metalogic.DBSoundness`
2. `lake build Cslib.Logics.Modal.Metalogic.DBCompleteness`
3. `lean_verify` on `db_axiom_sound`, `db_soundness`, `db_soundness_derivable`, `db_completeness` -- confirm zero sorry, zero axioms
4. Full project build: `lake build`

## Summary

- DB = K + D + B over serial + symmetric frames
- All infrastructure exists: DBAxiom (7 constructors), canonical_serial, canonical_symm, truth_lemma_d
- DBSoundness.lean: ~70 lines, 7 case analysis following DSoundness + BSoundness patterns
- DBCompleteness.lean: ~90 lines, follows D4Completeness pattern with canonical_symm replacing canonical_trans
- CRITICAL: Uses truth_lemma_d (D-based), NOT truth_lemma (T-based), because DB has D but not T
- Zero new lemmas needed; pure assembly from existing parameterized theorems
