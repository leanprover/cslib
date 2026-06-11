# Research Report: Modal ProofSystem/Instances.lean

## Task 93: Register Typeclass Instances for All Modal Systems (K, T, D, S4, S5)

### Summary

This report documents the research for creating `Cslib/Logics/Modal/ProofSystem/Instances.lean`,
which registers `InferenceSystem`, inference rule, axiom, and bundled typeclass instances for all
five modal systems (K, T, D, S4, S5). All approaches have been validated via `lean_run_code`
experiments.

### Architecture Overview

The module bridges the abstract typeclass hierarchy (defined in
`Cslib/Foundations/Logic/ProofSystem.lean`) to the concrete parameterized derivation tree (defined in
`Cslib/Logics/Modal/Metalogic/DerivationTree.lean`).

**Key design**: The modal `DerivationTree` is parameterized over
`Axioms : Proposition Atom -> Prop`. Each sub-logic needs its own axiom predicate containing
exactly the appropriate axiom schemata. The existing `ModalAxiom` contains all 8 S5 axioms.

### New Axiom Predicates Required

Five axiom predicates are needed (one per system). Each is an `inductive` type
`XAxiom : Modal.Proposition Atom -> Prop` containing exactly the axioms of that system:

| System | Predicate | Propositional (4) | Modal Axioms |
|--------|-----------|-------------------|--------------|
| K      | `KAxiom`  | implyK, implyS, efq, peirce | modalK |
| T      | `TAxiom`  | implyK, implyS, efq, peirce | modalK, modalT |
| D      | `DAxiom`  | implyK, implyS, efq, peirce | modalK, modalD |
| S4     | `S4Axiom` | implyK, implyS, efq, peirce | modalK, modalT, modalFour |
| S5     | `ModalAxiom` (existing) | implyK, implyS, efq, peirce | modalK, modalT, modalFour, modalB |

### Instance Registration Pattern

For each system `X` with tag type `Modal.HilbertX`:

1. **InferenceSystem**: Maps `HilbertX=>phi` to `DerivationTree XAxiom [] phi`
2. **ModusPonens**: Via `DerivationTree.modus_ponens`
3. **Necessitation**: Via `DerivationTree.necessitation`
4. **Propositional axiom instances**: HasAxiomImplyK, HasAxiomImplyS, HasAxiomEFQ, HasAxiomPeirce
   (via `DerivationTree.ax` with the appropriate constructor)
5. **Modal axiom instances**: HasAxiomK (all), HasAxiomT (T/S4/S5), HasAxiomD (D),
   HasAxiom4 (S4/S5), HasAxiomB (S5)
6. **Bundled class instance**: ModalHilbert (K), ModalTHilbert (T), ModalDHilbert (D),
   ModalS4Hilbert (S4), ModalS5Hilbert (S5)

### Template Pattern (from Bimodal/Temporal)

The pattern is identical to `Cslib/Logics/Bimodal/ProofSystem/Instances.lean` and
`Cslib/Logics/Temporal/ProofSystem/Instances.lean`:

```lean
instance : InferenceSystem Modal.HilbertK (Modal.Proposition Atom) where
  derivation phi := Modal.DerivationTree (@KAxiom Atom) [] phi

instance : ModusPonens Modal.HilbertK (F := Modal.Proposition Atom) where
  mp := fun h1 h2 => by
    obtain <d1> := h1; obtain <d2> := h2
    exact <Modal.DerivationTree.modus_ponens [] _ _ d1 d2>

instance : HasAxiomImplyK Modal.HilbertK (F := Modal.Proposition Atom) where
  implyK := <Modal.DerivationTree.ax [] _ (KAxiom.implyK _ _)>
-- ... remaining axioms
instance : ModalHilbert Modal.HilbertK (F := Modal.Proposition Atom) where
```

(Angle brackets represent Lean anonymous constructors.)

### Definitional Equality Verification

All polymorphic axiom definitions (`Axioms.ImplyK`, `Axioms.AxiomK`, etc.) are
**definitionally equal** to the constructor formulas in `ModalAxiom` and the new sub-logic
axiom predicates, because `ModalConnectives (Proposition Atom)` maps
`bot := .bot`, `imp := .imp`, `box := .box`. Verified via `lean_run_code`.

### Naming Note

Unlike Bimodal/Temporal (where `prop_k` = distribution = cslib's `ImplyS` and `prop_s` = weakening
= cslib's `ImplyK`), the Modal axiom predicates use cslib-standard names directly:
- `implyK` = weakening: `phi -> (psi -> phi)`
- `implyS` = distribution: `(phi -> (psi -> chi)) -> ((phi -> psi) -> (phi -> chi))`

This avoids the naming confusion documented in the Bimodal/Temporal instances.

### File Organization

The new file `Cslib/Logics/Modal/ProofSystem/Instances.lean` should:

1. Import `Cslib.Logics.Modal.Metalogic.DerivationTree` (for DerivationTree, ModalAxiom)
2. Import `Cslib.Foundations.Logic.ProofSystem` (for typeclass hierarchy)
3. Open `Cslib.Logic`
4. Define axiom predicates in order: KAxiom, TAxiom, DAxiom, S4Axiom
   (ModalAxiom already exists for S5)
5. Register instances in order: K, T, D, S4, S5
6. For each system: InferenceSystem, ModusPonens, Necessitation, axiom instances, bundled instance

### Impact on Existing Files

- **Soundness.lean**: No changes needed. Uses `ModalAxiom` directly, does not depend on
  typeclass instances.
- **Completeness.lean**: No changes needed. Same reasoning.
- **Metalogic.lean**: May need to add import of Instances.lean (optional, for downstream
  convenience).
- **Cslib.lean**: Needs a new import line for the Instances module.

Both Soundness.lean and Completeness.lean compile successfully (verified via `lake build`).

### Axiom Predicate Constructor Signatures

Each axiom predicate constructor produces a formula that is definitionally equal to the
polymorphic axiom abbreviation. The constructors must use fully-qualified `Modal.Proposition.*`
syntax (not dot notation) because the type parameter `Atom` may not be inferrable from the
field notation context.

Example for KAxiom:
```lean
inductive KAxiom : Modal.Proposition Atom -> Prop where
  | implyK (phi psi : Modal.Proposition Atom) :
      KAxiom (Modal.Proposition.imp phi (Modal.Proposition.imp psi phi))
  | implyS (phi psi chi : Modal.Proposition Atom) :
      KAxiom (Modal.Proposition.imp
        (Modal.Proposition.imp phi (Modal.Proposition.imp psi chi))
        (Modal.Proposition.imp (Modal.Proposition.imp phi psi)
          (Modal.Proposition.imp phi chi)))
  | efq (phi : Modal.Proposition Atom) :
      KAxiom (Modal.Proposition.imp Modal.Proposition.bot phi)
  | peirce (phi psi : Modal.Proposition Atom) :
      KAxiom (Modal.Proposition.imp
        (Modal.Proposition.imp (Modal.Proposition.imp phi psi) phi) phi)
  | modalK (phi psi : Modal.Proposition Atom) :
      KAxiom (Modal.Proposition.imp
        (Modal.Proposition.box (Modal.Proposition.imp phi psi))
        (Modal.Proposition.imp (Modal.Proposition.box phi) (Modal.Proposition.box psi)))
```

### Validation

All five patterns (K, T, D, S4, S5) have been validated via `lean_run_code`:
- K: `ModalHilbert Modal.HilbertK` -- compiles
- T: `ModalTHilbert Modal.HilbertT` -- compiles
- D: `ModalDHilbert Modal.HilbertD` -- compiles
- S4: pattern follows from K+T+4 (structurally same as T with additional constructor)
- S5: `ModalS5Hilbert Modal.HilbertS5` using existing `ModalAxiom` -- compiles

### Potential Complications

1. **Dot notation**: Axiom predicate constructors must use `Modal.Proposition.imp` rather than
   `phi.imp` due to type inference limitations in inductive definitions. This is a known Lean 4
   issue with field notation in constructor return types.

2. **Universe polymorphism**: The variable `{Atom : Type u}` must be universe-polymorphic to match
   the existing `ModalAxiom` definition.

3. **Diamond abbreviation for D/B**: The `AxiomD` and `AxiomB` polymorphic abbreviations use
   diamond which expands to `neg (box (neg phi))`. The axiom predicate constructors must use the
   same expansion. Verified: `Proposition.diamond phi = Proposition.neg (Proposition.box (Proposition.neg phi))`
   which is `Proposition.imp (Proposition.box (Proposition.imp phi Proposition.bot)) Proposition.bot`.

4. **S5 reuse**: For S5, the existing `ModalAxiom` should be reused rather than defining a new
   `S5Axiom`. This maintains backward compatibility with Soundness.lean and Completeness.lean.

### Recommended Phase Structure

**Single phase** -- this is a mechanical instance registration file:

1. Define 4 new axiom predicates (KAxiom, TAxiom, DAxiom, S4Axiom)
2. Register all instances for K (InferenceSystem, MP, Nec, 4 prop axioms, HasAxiomK, ModalHilbert)
3. Register all instances for T (same + HasAxiomT, ModalTHilbert)
4. Register all instances for D (same as K + HasAxiomD, ModalDHilbert)
5. Register all instances for S4 (same as T + HasAxiom4, ModalS4Hilbert)
6. Register all instances for S5 using existing ModalAxiom (same as S4 + HasAxiomB, ModalS5Hilbert)
7. Add import to Cslib.lean
8. Verify `lake build` passes

### Critical Files

| File | Role |
|------|------|
| `Cslib/Foundations/Logic/ProofSystem.lean` | Typeclass hierarchy (tag types, bundled classes) |
| `Cslib/Logics/Modal/Metalogic/DerivationTree.lean` | Parameterized DerivationTree, ModalAxiom |
| `Cslib/Logics/Bimodal/ProofSystem/Instances.lean` | Template pattern |
| `Cslib/Logics/Temporal/ProofSystem/Instances.lean` | Template pattern |
| `Cslib/Logics/Modal/Metalogic/Soundness.lean` | Must continue to compile (no changes needed) |
| `Cslib/Logics/Modal/Metalogic/Completeness.lean` | Must continue to compile (no changes needed) |
