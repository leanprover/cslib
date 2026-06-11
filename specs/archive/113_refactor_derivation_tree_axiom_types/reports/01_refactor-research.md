# Research Report: Refactor Propositional DerivationTree to Axiom-Parameterized Form

## 1. Current Codebase Structure

### 1.1 Propositional Proof System Files

| File | Key Definitions | Lines |
|------|----------------|-------|
| `Defs.lean` | `Proposition`, `Theory`, `MPL`, `IPL`, `CPL`, `IsIntuitionistic`, `IsClassical` | 167 |
| `ProofSystem/Axioms.lean` | `PropositionalAxiom` (4 constructors: implyK, implyS, efq, peirce) | 55 |
| `ProofSystem/Derivation.lean` | `DerivationTree Gamma phi` (hardcoded), `Deriv`, `Derivable`, `propDerivationSystem` | 148 |
| `ProofSystem/Instances.lean` | `InferenceSystem`, `ModusPonens`, `HasAxiom*`, `ClassicalHilbert` for `HilbertCl` | 90 |
| `Metalogic/DeductionTheorem.lean` | `HasHilbertTree` instance, `deductionWithMem`, `deductionTheorem`, `prop_has_deduction_theorem` | 178 |
| `Metalogic/MCS.lean` | `PropSetConsistent`, `PropSetMaximalConsistent`, MCS properties | 130 |
| `NaturalDeduction/FromHilbert.lean` | `impI`, `impE`, `botE`, `axiomRule`, `subst_preserves_axiom`, `hilbertSubstitution` | 220 |
| `NaturalDeduction/HilbertDerivedRules.lean` | `hilbertDne`, `hilbertAndI/E`, `hilbertOrI/E`, etc. | 448 |
| `NaturalDeduction/Equivalence.lean` | `HilbertAxiomTheory`, `hilbertToND`, `ndToHilbert`, `hilbert_iff_nd` | 169 |
| `NaturalDeduction/Basic.lean` | Standalone ND system (separate, uses `Theory.Derivation`) | ~300 |
| `NaturalDeduction/DerivedRules.lean` | ND derived rules (standalone, no Hilbert dependency) | ~300 |

### 1.2 Import Chain (Critical Path)

```
Defs.lean
  -> Axioms.lean
    -> Derivation.lean
      -> Instances.lean
      -> DeductionTheorem.lean
        -> FromHilbert.lean
          -> Equivalence.lean
          -> HilbertDerivedRules.lean
        -> MCS.lean
```

### 1.3 Current DerivationTree Signature

```lean
-- CURRENT (hardcoded axiom type)
inductive DerivationTree : List (PL.Proposition Atom) -> PL.Proposition Atom -> Type _ where
  | ax (Gamma) (phi) (h : PropositionalAxiom phi) : DerivationTree Gamma phi
  | assumption (Gamma) (phi) (h : phi in Gamma) : DerivationTree Gamma phi
  | modus_ponens (Gamma) (phi psi) (d1 : DerivationTree Gamma (phi.imp psi))
      (d2 : DerivationTree Gamma phi) : DerivationTree Gamma psi
  | weakening (Gamma Delta) (phi) (d : DerivationTree Gamma phi)
      (h : forall x in Gamma, x in Delta) : DerivationTree Delta phi
```

## 2. The Modal Pattern to Follow

### 2.1 Modal DerivationTree Signature

```lean
-- TARGET PATTERN (parameterized)
inductive DerivationTree (Axioms : Proposition Atom -> Prop) :
    List (Proposition Atom) -> Proposition Atom -> Type _ where
  | ax (Gamma) (phi) (h : Axioms phi) : DerivationTree Axioms Gamma phi
  | assumption (Gamma) (phi) (h : phi in Gamma) : DerivationTree Axioms Gamma phi
  | modus_ponens (Gamma) (phi psi) (d1 : DerivationTree Axioms Gamma (phi.imp psi))
      (d2 : DerivationTree Axioms Gamma phi) : DerivationTree Axioms Gamma psi
  | weakening (Gamma Delta) (phi) (d : DerivationTree Axioms Gamma phi)
      (h : forall x in Gamma, x in Delta) : DerivationTree Axioms Delta phi
```

Note: The propositional version has 4 constructors (no `necessitation`), matching the current structure. Only the `ax` constructor changes from `PropositionalAxiom phi` to `Axioms phi`.

### 2.2 Modal Deriv/Derivable/DerivationSystem Pattern

```lean
def Deriv (Axioms : Proposition Atom -> Prop) (Gamma) (phi) : Prop :=
  Nonempty (DerivationTree Axioms Gamma phi)

def Derivable (Axioms : Proposition Atom -> Prop) (phi) : Prop :=
  Deriv Axioms [] phi

def propDerivationSystem (Axioms : PL.Proposition Atom -> Prop) :
    Metalogic.DerivationSystem (PL.Proposition Atom) where
  Deriv := Deriv Axioms
  weakening := ...
  assumption := ...
  mp := ...
```

### 2.3 Modal DeductionTheorem Pattern

The modal deduction theorem takes explicit `h_implyK` and `h_implyS` proofs:

```lean
noncomputable def deductionTheorem
    {Axioms : Proposition Atom -> Prop}
    (h_implyK : forall (phi psi), Axioms (phi.imp (psi.imp phi)))
    (h_implyS : forall (phi psi chi), Axioms ((phi.imp (psi.imp chi)).imp ((phi.imp psi).imp (phi.imp chi))))
    (Gamma) (A B) (d : DerivationTree Axioms (A :: Gamma) B) :
    DerivationTree Axioms Gamma (A.imp B)
```

### 2.4 Modal MCS Pattern

```lean
abbrev Modal.SetConsistent (Axioms) (S) :=
  Metalogic.SetConsistent (modalDerivationSystem Axioms) S

-- Properties take {Axioms} plus h_implyK/h_implyS
theorem modal_closed_under_derivation {Axioms} (h_implyK) (h_implyS)
    (h_mcs) (h_sub) (h_deriv) : phi in S
```

### 2.5 Modal Backward Compatibility Pattern

```lean
abbrev S5DerivationTree := @DerivationTree Atom ModalAxiom
abbrev S5Deriv := @Deriv Atom ModalAxiom
abbrev S5Derivable := @Derivable Atom ModalAxiom
def s5DerivationSystem := modalDerivationSystem (@ModalAxiom Atom)
```

## 3. Specific Changes Per File

### 3.1 Axioms.lean -- ADD IntPropAxiom, MinPropAxiom

**New definitions** (add alongside existing `PropositionalAxiom`):

```lean
/-- Axiom schemata for intuitionistic propositional logic. -/
inductive IntPropAxiom : PL.Proposition Atom -> Prop where
  | implyK (phi psi) : IntPropAxiom (phi.imp (psi.imp phi))
  | implyS (phi psi chi) : IntPropAxiom ((phi.imp (psi.imp chi)).imp ((phi.imp psi).imp (phi.imp chi)))
  | efq (phi) : IntPropAxiom (Proposition.bot.imp phi)

/-- Axiom schemata for minimal propositional logic. -/
inductive MinPropAxiom : PL.Proposition Atom -> Prop where
  | implyK (phi psi) : MinPropAxiom (phi.imp (psi.imp phi))
  | implyS (phi psi chi) : MinPropAxiom ((phi.imp (psi.imp chi)).imp ((phi.imp psi).imp (phi.imp chi)))
```

**Existing `PropositionalAxiom` is kept** -- it remains the classical axiom set.

### 3.2 Derivation.lean -- PARAMETERIZE DerivationTree

**Change signature** from `DerivationTree Gamma phi` to `DerivationTree (Axioms : PL.Proposition Atom -> Prop) Gamma phi`.

Specific changes:
1. Add `Axioms` parameter to `DerivationTree` inductive
2. Change `.ax` constructor from `(h : PropositionalAxiom phi)` to `(h : Axioms phi)`
3. Add `Axioms` parameter to `height` and all height theorems
4. Parameterize `Deriv`, `Derivable`, `mp_deriv`, `weakening_deriv`, `assumption_deriv`
5. Parameterize `propDerivationSystem` to take `(Axioms : PL.Proposition Atom -> Prop)`
6. Add backward-compatible aliases:
   ```lean
   abbrev ClDerivationTree := @DerivationTree Atom PropositionalAxiom
   abbrev ClDeriv := @Deriv Atom PropositionalAxiom
   abbrev ClDerivable := @Derivable Atom PropositionalAxiom
   def clPropDerivationSystem := propDerivationSystem (@PropositionalAxiom Atom)
   ```

### 3.3 DeductionTheorem.lean -- PARAMETERIZE

Follow the modal pattern exactly:

1. **`HasHilbertTree` instance**: Change from hardcoded `DerivationTree` to `DerivationTree ModalAxiom` style. For backward compat, instantiate at `PropositionalAxiom`.

2. **`deductionWithMem`**: Add `{Axioms}`, `h_implyK`, `h_implyS` parameters. Build local `HasHilbertTree` instance inside the function body (modal pattern uses `letI`).

3. **`deductionTheorem`**: Same parameterization as `deductionWithMem`.

4. **`prop_has_deduction_theorem`**: Parameterize to take `{Axioms}`, `h_implyK`, `h_implyS`. Add backward-compatible wrapper:
   ```lean
   theorem cl_prop_has_deduction_theorem :
       Metalogic.HasDeductionTheorem (propDerivationSystem (@PropositionalAxiom Atom)) :=
     prop_has_deduction_theorem
       (fun phi psi => .implyK phi psi)
       (fun phi psi chi => .implyS phi psi chi)
   ```

**Key design decision**: The deduction theorem only requires `implyK` and `implyS`. It works for ALL three axiom sets (MinPropAxiom, IntPropAxiom, PropositionalAxiom) since they all have these constructors.

### 3.4 MCS.lean -- PARAMETERIZE

1. **`PropSetConsistent`/`PropSetMaximalConsistent`**: Parameterize by `Axioms`:
   ```lean
   abbrev PropSetConsistent (Axioms : PL.Proposition Atom -> Prop) (S) :=
     Metalogic.SetConsistent (propDerivationSystem Axioms) S
   ```

2. **All MCS theorems**: Add `{Axioms}` parameter plus `h_implyK`/`h_implyS` where deduction theorem is used.

3. **EFQ-dependent properties** (`prop_mcs_bot_not_mem`, `prop_mcs_neg_of_not_mem`, etc.): These depend on `PropositionalAxiom.efq` via `propDerivationSystem`. In the parameterized version, the MCS specific properties that use EFQ need the axiom predicate to include EFQ. Options:
   - Add explicit `h_efq : forall phi, Axioms (Proposition.bot.imp phi)` parameter
   - Or restrict these to axiom sets that include EFQ

4. **Peirce-dependent properties** (`prop_negation_complete`): Needs peirce. Similarly parameterize.

5. **Classical-specific backward compat wrappers**: Instantiate at `PropositionalAxiom`.

### 3.5 Instances.lean -- UPDATE HilbertCl, ADD Instances

1. **Update HilbertCl**: Change `DerivationTree [] phi` to `DerivationTree PropositionalAxiom [] phi` in `InferenceSystem` instance.

2. **Add HilbertInt instances** (new file `IntMinInstances.lean` or same file):
   ```lean
   instance : InferenceSystem Propositional.HilbertInt (PL.Proposition Atom) where
     derivation phi := PL.DerivationTree IntPropAxiom [] phi

   instance : ModusPonens Propositional.HilbertInt (F := PL.Proposition Atom) where ...
   instance : HasAxiomImplyK Propositional.HilbertInt (F := PL.Proposition Atom) where
     implyK := ⟨PL.DerivationTree.ax [] _ (.implyK _ _)⟩
   instance : HasAxiomImplyS Propositional.HilbertInt (F := PL.Proposition Atom) where ...
   instance : HasAxiomEFQ Propositional.HilbertInt (F := PL.Proposition Atom) where ...
   instance : IntuitionisticHilbert Propositional.HilbertInt (F := PL.Proposition Atom) where
   ```

3. **Add HilbertMin instances**:
   ```lean
   instance : InferenceSystem Propositional.HilbertMin (PL.Proposition Atom) where
     derivation phi := PL.DerivationTree MinPropAxiom [] phi

   instance : ModusPonens Propositional.HilbertMin (F := PL.Proposition Atom) where ...
   instance : HasAxiomImplyK Propositional.HilbertMin (F := PL.Proposition Atom) where ...
   instance : HasAxiomImplyS Propositional.HilbertMin (F := PL.Proposition Atom) where ...
   instance : MinimalHilbert Propositional.HilbertMin (F := PL.Proposition Atom) where
   ```

**Note**: Tag types `Propositional.HilbertMin` and `Propositional.HilbertInt` already exist in `ProofSystem.lean`.

### 3.6 NaturalDeduction/FromHilbert.lean -- UPDATE

1. **All definitions using `DerivationTree`** gain an implicit `{Axioms}` parameter since `DerivationTree` is now parameterized.

2. **`impI` (deductionTheorem wrapper)**: Must now take `h_implyK`/`h_implyS` or be fixed at a specific axiom set.

   **Design decision**: The `impI`/`impE`/`botE` rules are currently classical (they use `PropositionalAxiom.efq`). Two approaches:
   - (A) Keep them fixed at `PropositionalAxiom` via backward-compat aliases
   - (B) Parameterize them and pass axiom assumptions

   **Recommendation**: Approach (A) for this task. The NaturalDeduction files are downstream of the core refactor and can be further generalized in a follow-up. They use `PropositionalAxiom` constructors directly in proofs (e.g., `.efq`, `.peirce`), making full parameterization a larger change.

3. **`axiomRule`**: Changes from `(h : PropositionalAxiom phi)` to `(h : Axioms phi)`.

4. **`subst_preserves_axiom`**: Currently specific to `PropositionalAxiom`. If kept at `PropositionalAxiom`, no change needed.

5. **`hilbertSubstitution`**: Currently uses `DerivationTree` and `subst_preserves_axiom`. Needs `Axioms` parameter and a generic "axiom preservation under substitution" hypothesis.

### 3.7 NaturalDeduction/HilbertDerivedRules.lean -- UPDATE

All definitions use `DerivationTree` directly and reference `PropositionalAxiom` constructors explicitly (`.peirce`, `.efq`, `.implyK`, `.implyS`).

**These are inherently classical** -- `hilbertDne` uses Peirce's law, `hilbertAndE1/E2` use Peirce and EFQ.

**Recommendation**: Fix these at `PropositionalAxiom` using backward-compat aliases. The `DerivationTree` type will carry `PropositionalAxiom` as the axiom parameter.

### 3.8 NaturalDeduction/Equivalence.lean -- UPDATE

1. **`HilbertAxiomTheory`**: Currently `{ phi | PropositionalAxiom phi }`. Keep as-is or parameterize.
2. **`hilbertToND`/`ndToHilbert`**: Use `DerivationTree` directly. Fix at `PropositionalAxiom`.
3. **`hilbert_iff_nd`**: Fix at `PropositionalAxiom` (it's specifically about classical equivalence).

## 4. Dependency Analysis

### 4.1 What Imports What

```
Axioms.lean        <- Derivation.lean <- Instances.lean
                                      <- DeductionTheorem.lean <- FromHilbert.lean <- Equivalence.lean
                                                               <- MCS.lean          <- HilbertDerivedRules.lean
```

### 4.2 Change Propagation

| Change | Affects |
|--------|---------|
| `DerivationTree` gains `Axioms` param | Everything downstream |
| `Deriv`/`Derivable` gain `Axioms` param | DeductionTheorem, MCS, FromHilbert |
| `propDerivationSystem` gains `Axioms` param | MCS |
| `deductionTheorem` gains `h_implyK`/`h_implyS` | FromHilbert (`impI`), MCS |
| New axiom types added to Axioms.lean | Instances.lean (new file) |

### 4.3 Files NOT Needing Changes

| File | Reason |
|------|--------|
| `Defs.lean` | No DerivationTree references |
| `NaturalDeduction/Basic.lean` | Standalone ND, no Hilbert dependency |
| `NaturalDeduction/DerivedRules.lean` | Uses `Theory.Derivation`, not `DerivationTree` |
| `Modal/FromPropositional.lean` | Only imports `Defs.lean` |
| `Temporal/FromPropositional.lean` | Only imports `Defs.lean` |

## 5. Risk Areas and Potential Complications

### 5.1 HIGH RISK: NaturalDeduction/FromHilbert.lean

The `impI` function wraps `deductionTheorem`. After parameterization, `deductionTheorem` requires `h_implyK`/`h_implyS` proof arguments. Every call to `impI` in `HilbertDerivedRules.lean` (there are ~15 uses including `hilbertNegI`, `hilbertAndI`, `hilbertOrI1`, `hilbertOrE`, `hilbertIffI`) would need to thread these through.

**Mitigation**: Fix the NaturalDeduction files at `PropositionalAxiom` using backward-compat aliases. Define `impI` with `PropositionalAxiom` as the specific axiom set.

### 5.2 MEDIUM RISK: MCS.lean EFQ/Peirce Dependencies

Several MCS theorems rely on specific axioms:
- `prop_mcs_bot_not_mem` uses `propDerivationSystem` (needs `.assumption`)
- `prop_negation_complete` uses the deduction theorem (needs implyK/implyS)
- `prop_mcs_neg_of_not_mem` depends on `prop_negation_complete`

These can be parameterized with explicit axiom assumptions (following the modal pattern in `Modal.MCS.lean`).

### 5.3 MEDIUM RISK: HasHilbertTree Instance

The current `HasHilbertTree` instance in DeductionTheorem.lean is fixed at `PropositionalAxiom`:
```lean
noncomputable instance : HasHilbertTree (PL.Proposition Atom) where
  Tree := fun Gamma phi => DerivationTree Gamma phi
```

After refactoring, this must become:
```lean
noncomputable instance : HasHilbertTree (PL.Proposition Atom) where
  Tree := fun Gamma phi => DerivationTree PropositionalAxiom Gamma phi
```

The modal pattern instantiates `HasHilbertTree` at `ModalAxiom` for the global instance but builds local `letI` instances inside `deductionWithMem`/`deductionTheorem` for the parameterized versions.

### 5.4 LOW RISK: Universe Polymorphism

The `DerivationTree` uses `Type _` (auto universe). Adding the `Axioms` parameter should not cause universe issues since `Axioms : PL.Proposition Atom -> Prop` is in `Prop`.

### 5.5 LOW RISK: Backward Compatibility Aliases

Using `abbrev` for backward compat may cause definitional unfolding issues. If problems arise, use `def` with `@[reducible]` or explicit `abbrev`.

## 6. Recommended Implementation Order

### Phase 1: Core Parameterization (Axioms.lean + Derivation.lean)

1. **Add `IntPropAxiom` and `MinPropAxiom`** to `Axioms.lean`
2. **Parameterize `DerivationTree`** in `Derivation.lean`
3. **Parameterize `Deriv`, `Derivable`, combinators, `propDerivationSystem`**
4. **Add backward-compat aliases** (`ClDerivationTree`, etc.)
5. **Build**: `lake build Cslib.Logics.Propositional.ProofSystem.Derivation`

### Phase 2: DeductionTheorem Parameterization

1. **Parameterize `deductionWithMem`** with `{Axioms}`, `h_implyK`, `h_implyS`
2. **Parameterize `deductionTheorem`** similarly
3. **Parameterize `prop_has_deduction_theorem`**
4. **Update `HasHilbertTree` global instance** to use `PropositionalAxiom`
5. **Add backward-compat wrapper** `cl_prop_has_deduction_theorem`
6. **Build**: `lake build Cslib.Logics.Propositional.Metalogic.DeductionTheorem`

### Phase 3: MCS Parameterization

1. **Parameterize `PropSetConsistent`, `PropSetMaximalConsistent`**
2. **Parameterize MCS theorems** with `{Axioms}`, `h_implyK`, `h_implyS`
3. **Parameterize EFQ-dependent theorems** with explicit `h_efq`
4. **Add backward-compat wrappers**
5. **Build**: `lake build Cslib.Logics.Propositional.Metalogic.MCS`

### Phase 4: Instance Registration

1. **Update `Instances.lean`** for `HilbertCl` (change `DerivationTree` to `DerivationTree PropositionalAxiom`)
2. **Create `IntMinInstances.lean`** (or extend `Instances.lean`) with:
   - `HilbertInt` instances (InferenceSystem, ModusPonens, HasAxiomImplyK/S, HasAxiomEFQ, IntuitionisticHilbert)
   - `HilbertMin` instances (InferenceSystem, ModusPonens, HasAxiomImplyK/S, MinimalHilbert)
3. **Register in `Cslib.lean`** root import file
4. **Build**: `lake build Cslib.Logics.Propositional.ProofSystem.Instances`

### Phase 5: NaturalDeduction Updates

1. **Update `FromHilbert.lean`** -- fix `impI`/`impE`/`botE` at `PropositionalAxiom`
2. **Update `HilbertDerivedRules.lean`** -- fix at `PropositionalAxiom`
3. **Update `Equivalence.lean`** -- fix at `PropositionalAxiom`
4. **Build**: `lake build Cslib.Logics.Propositional.NaturalDeduction.Equivalence`

### Phase 6: Full Build + Verification

1. **Full build**: `lake build`
2. **Verify no sorry**: `lean_verify` on key definitions
3. **Check no regressions in downstream modules** (Modal, Temporal, Bimodal)

## 7. Key Design Decisions

### 7.1 Where to Put IntMinInstances

The task description says "new IntMinInstances.lean". **Recommendation**: Create `Cslib/Logics/Propositional/ProofSystem/IntMinInstances.lean` importing `Derivation.lean` and `ProofSystem.lean`. This parallels keeping Instances.lean for classical and adding a new file for the new logics.

### 7.2 Subsumption Proofs

It may be useful to prove that `MinPropAxiom phi -> IntPropAxiom phi` and `IntPropAxiom phi -> PropositionalAxiom phi` (every minimal axiom is intuitionistic, every intuitionistic axiom is classical). These enable lifting derivation trees between systems.

```lean
theorem MinPropAxiom.toIntProp {phi} (h : MinPropAxiom phi) : IntPropAxiom phi
theorem IntPropAxiom.toProp {phi} (h : IntPropAxiom phi) : PropositionalAxiom phi
```

These are simple case analyses and should be included in `Axioms.lean`.

### 7.3 Naming Convention

Follow the modal pattern:
- Generic functions take `Axioms` as first parameter
- Backward-compat aliases use `Cl`/`Int`/`Min` prefix or the existing names
- The existing `propDerivationSystem` becomes parameterized; `clPropDerivationSystem` is the backward-compat alias

## 8. Estimated Scope

| Phase | Files Modified | Files Created | Estimated Complexity |
|-------|---------------|---------------|---------------------|
| 1 | 2 (Axioms, Derivation) | 0 | Medium |
| 2 | 1 (DeductionTheorem) | 0 | High (well-founded recursion changes) |
| 3 | 1 (MCS) | 0 | Medium |
| 4 | 1 (Instances) | 1 (IntMinInstances) | Low |
| 5 | 3 (FromHilbert, HilbertDerivedRules, Equivalence) | 0 | Medium-High (many callsites) |
| 6 | 0 | 0 | Build verification |

**Total**: 8 files modified, 1 file created. The heaviest work is in Phases 2 and 5.
