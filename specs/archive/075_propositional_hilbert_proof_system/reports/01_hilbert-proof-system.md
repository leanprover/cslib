# Research Report: Propositional Hilbert Proof System

**Task**: 75 -- Develop propositional Hilbert proof system and derive natural deduction rules
**Session**: sess_1781099803_31c6ac
**Date**: 2026-06-10

## 1. Current Codebase Structure Analysis

### 1.1 Propositional Logic (Current State)

The propositional logic lives under `Cslib/Logics/Propositional/` with only two files:

- **`Defs.lean`**: Defines `PL.Proposition` (inductive with `atom`, `bot`, `imp`), derived connectives (`neg`, `top`, `or`, `and` via Lukasiewicz encoding), `Theory` (set of propositions), `IsIntuitionistic`, `IsClassical`, `Theory.MPL/IPL/CPL`, and substitution/monad.
  - Registers `PropositionalConnectives` instance for `PL.Proposition`.
  - Defines `Theory.intuitionisticCompletion`.

- **`NaturalDeduction/Basic.lean`**: Defines a **standalone inductive type** `Theory.Derivation` with 5 constructors (`ax`, `ass`, `impI`, `impE`, `botE`). This is a sequent-style natural deduction system where:
  - Contexts are `Finset (Proposition Atom)` (implicit contraction/exchange).
  - Derivations are parameterized by a `Theory T` (set of extra axioms).
  - Proves weakening, cut, substitution, atom substitution, and equivalence properties.
  - Defines `InferenceSystem T Sequent` and `InferenceSystem T (Proposition Atom)`.

**Key observation**: The current `NaturalDeduction/Basic.lean` does NOT use the Foundations infrastructure at all. It has its own `InferenceSystem` instances directly, and does not interact with `ProofSystem.lean`, `DerivationSystem`, or the MCS framework. It is completely self-contained.

### 1.2 Foundations/Logic Infrastructure

The foundations layer provides generic infrastructure used by Modal, Temporal, and Bimodal:

- **`InferenceSystem.lean`**: Defines `InferenceSystem S α` typeclass mapping tag `S` + value `α` to `Sort v`. Provides `DerivableIn S a = Nonempty (S⇓a)` and `S⇓a` notation.

- **`Connectives.lean`**: Defines `HasBot`, `HasImp`, `HasBox`, `HasUntil`, `HasSince`, bundled classes (`PropositionalConnectives`, `ModalConnectives`, `TemporalConnectives`, `BimodalConnectives`), and `LukasiewiczDerived` specification class (intentionally uninstantiated).

- **`Axioms.lean`**: Defines polymorphic axiom formulas (`Axioms.ImplyK`, `Axioms.ImplyS`, `Axioms.EFQ`, `Axioms.Peirce`, `Axioms.DNE`, modal/temporal axioms) as `abbrev`s parameterized over connective typeclasses.

- **`ProofSystem.lean`**: Defines:
  - Rule typeclasses: `ModusPonens`, `Necessitation`, `TemporalNecessitation`
  - Axiom typeclasses: `HasAxiomImplyK`, `HasAxiomImplyS`, `HasAxiomEFQ`, `HasAxiomPeirce`, `HasAxiomDNE`, plus modal/temporal axiom classes
  - **Bundled classes**: `PropositionalHilbert S` (extends `ModusPonens`, `HasAxiomImplyK`, `HasAxiomImplyS`, `HasAxiomEFQ`, `HasAxiomPeirce`), `ModalHilbert`, `ModalS5Hilbert`, `TemporalBXHilbert`, `BimodalTMHilbert`
  - **Tag types**: `Propositional.HilbertCl` (opaque, no instances yet!), `Modal.HilbertK`, `Modal.HilbertS5`, `Temporal.HilbertBX`, `Bimodal.HilbertTM`

- **`Metalogic/Consistency.lean`**: Generic MCS framework (`DerivationSystem`, `SetConsistent`, `SetMaximalConsistent`, Lindenbaum's lemma, `HasDeductionTheorem`, closure properties).

- **`Theorems/Combinators.lean`**: Generic combinators for `[PropositionalHilbert S]`: `imp_trans`, `identity`, `b_combinator`, `theorem_flip`, `theorem_app1`, `theorem_app2`, `pairing`, `dni`, `combine_imp_conj`.

- **`Theorems/Propositional/Core.lean`**: Generic propositional theorems for `[PropositionalHilbert S]`: `efq_axiom`, `peirce_axiom`, `double_negation` (DNE derived), `raa`, `efq_neg`, `rcp`, `lce_imp`, `rce_imp`, `lem`.

- **`Theorems/Propositional/Connectives.lean`**: Generic derived connective theorems: `contrapose_imp`, `classical_merge`, `iff_intro`, `contrapose_iff`, De Morgan laws.

### 1.3 The Hilbert Proof System Pattern (Modal/Temporal/Bimodal)

Each logic follows this pattern:

#### Step 1: Axiom Inductive Type
Define an inductive `Axiom : Formula Atom -> Prop/Type` enumerating axiom schemata. Example: Modal has `ModalAxiom` with 8 constructors (4 propositional + 4 modal).

#### Step 2: DerivationTree Inductive Type
Define `DerivationTree : Context -> Formula -> Type` with constructors:
- `ax`: axiom schema instances
- `assumption`: context membership
- `modus_ponens`: from `phi -> psi` and `phi`, get `psi`
- Logic-specific rules: `necessitation` (Modal, Bimodal), `temporal_necessitation` (Temporal, Bimodal), `temporal_duality` (Temporal, Bimodal)
- `weakening`: context extension

With computable `height` function for termination in deduction theorem.

#### Step 3: Deriv Wrapper + DerivationSystem Instance
- `Deriv L phi := Nonempty (DerivationTree L phi)` (Prop wrapper)
- `modalDerivationSystem : DerivationSystem (Proposition Atom)` connecting to generic MCS framework

#### Step 4: InferenceSystem + Typeclass Instances
Register `InferenceSystem Tag Formula` mapping tag to `DerivationTree [] phi`. Register `ModusPonens`, `HasAxiomImplyK/S/EFQ/Peirce`, and bundled `PropositionalHilbert` (plus logic-specific axiom classes).

#### Step 5: Deduction Theorem
Prove by well-founded recursion on `DerivationTree.height`. Result: `HasDeductionTheorem derivationSystem`.

#### Step 6: MCS Properties
Instantiate generic MCS framework (Lindenbaum, closed_under_derivation, implication_property, negation_complete), then prove logic-specific MCS properties.

#### Step 7: Soundness, Completeness
Use DerivationTree and MCS for metalogic results.

### 1.4 Duplication Analysis

**Severe duplication exists across logics.** Each of Modal, Temporal, and Bimodal independently redevelops:

1. **Propositional axiom constructors** in their `Axiom` type (4 constructors: `implyK`, `implyS`, `efq`, `peirce`)
2. **Propositional combinator derivations** (`imp_trans`, `identity`, `double_negation`, `pairing`, `lce_imp`, `rce_imp`, `dni`, `demorgan`, etc.)
3. **Deduction theorem helper cases** (`deduction_axiom`, `deduction_imp_self`, `deduction_assumption_other`, `deduction_mp`)

**Specifically**:

| Component | Bimodal | Temporal | Modal |
|-----------|---------|----------|-------|
| `Axiom` inductive | `Theorems/Propositional/Core.lean` & `ProofSystem/Axioms.lean` | `ProofSystem/Axioms.lean` | `Metalogic/DerivationTree.lean` |
| Propositional combinators | `Theorems/Combinators.lean` (via Foundations bridge) | `Metalogic/PropositionalHelpers.lean` (standalone) | Inline in `DeductionTheorem.lean` |
| DeductionTheorem | `Metalogic/Core/DeductionTheorem.lean` | `Metalogic/DeductionTheorem.lean` | `Metalogic/DeductionTheorem.lean` |
| MCS properties | `Metalogic/Core/MaximalConsistent.lean` | `Metalogic/MCS.lean` | `Metalogic/MCS.lean` |

**Bimodal uses a wrap/unwrap bridge pattern** to delegate to Foundations generic theorems:
```lean
private def unwrap {phi : Formula Atom}
    (h : InferenceSystem.DerivableIn Bimodal.HilbertTM phi) :
    DerivationTree FrameClass.Base [] phi := h.some
```

**Temporal does NOT use Foundations** -- it re-proves everything from scratch in `PropositionalHelpers.lean`.

**Modal does NOT use Foundations** -- it builds propositional reasoning inline within the deduction theorem.

### 1.5 FromPropositional Embeddings

- `Modal/FromPropositional.lean`: `PL.Proposition.toModal` (structural embedding, coercion)
- `Temporal/FromPropositional.lean`: `PL.Proposition.toTemporal` (structural embedding, coercion)
- `Bimodal/Embedding/PropositionalEmbedding.lean`: `PL.Proposition.toBimodal` + commutativity proofs

These embeddings are **formula-level only** -- they embed syntactic formulas but do NOT lift derivations.

## 2. What Needs to Be Created for Propositional

### 2.1 New File Structure

```
Cslib/Logics/Propositional/
  Defs.lean                          -- (existing, minimal changes)
  NaturalDeduction/
    Basic.lean                       -- (existing, to be refactored later)
  ProofSystem/
    Axioms.lean                      -- PropositionalAxiom inductive
    Derivation.lean                  -- DerivationTree + height + Deriv
    Instances.lean                   -- InferenceSystem + typeclass instances
  Metalogic/
    DeductionTheorem.lean            -- Deduction theorem for PL
    MCS.lean                         -- MCS properties for PL
  Theorems.lean                      -- Re-exports / convenience
```

### 2.2 Detailed File Contents

#### `ProofSystem/Axioms.lean`

Define `PropositionalAxiom : PL.Proposition Atom -> Prop` with 4 constructors:
```lean
inductive PropositionalAxiom : PL.Proposition Atom -> Prop where
  | implyK (phi psi) : PropositionalAxiom (phi.imp (psi.imp phi))
  | implyS (phi psi chi) : PropositionalAxiom ((phi.imp (psi.imp chi)).imp ((phi.imp psi).imp (phi.imp chi)))
  | efq (phi) : PropositionalAxiom (Proposition.bot.imp phi)
  | peirce (phi psi) : PropositionalAxiom (((phi.imp psi).imp phi).imp phi)
```

This is directly analogous to the first 4 constructors of `ModalAxiom`, `Temporal.Axiom`, and `Bimodal.Axiom`.

#### `ProofSystem/Derivation.lean`

Define `DerivationTree : List (PL.Proposition Atom) -> PL.Proposition Atom -> Type` with 4 constructors (no necessitation):
```lean
inductive DerivationTree : List (PL.Proposition Atom) -> PL.Proposition Atom -> Type _ where
  | ax (Gamma) (phi) (h : PropositionalAxiom phi) : DerivationTree Gamma phi
  | assumption (Gamma) (phi) (h : phi in Gamma) : DerivationTree Gamma phi
  | modus_ponens (Gamma) (phi psi) (d1 : DerivationTree Gamma (phi.imp psi))
      (d2 : DerivationTree Gamma phi) : DerivationTree Gamma psi
  | weakening (Gamma Delta) (phi) (d : DerivationTree Gamma phi)
      (h : forall x in Gamma, x in Delta) : DerivationTree Delta phi
```

Plus `height` function, height lemmas, `Deriv` wrapper, `propDerivationSystem : DerivationSystem`.

**Key difference from Modal/Temporal/Bimodal**: No necessitation rule (propositional logic has no modal operators).

#### `ProofSystem/Instances.lean`

Register:
- `InferenceSystem Propositional.HilbertCl (PL.Proposition Atom)` mapping to `DerivationTree [] phi`
- `ModusPonens`, `HasAxiomImplyK`, `HasAxiomImplyS`, `HasAxiomEFQ`, `HasAxiomPeirce` instances
- `PropositionalHilbert Propositional.HilbertCl` (auto from the above)

This makes all generic theorems in `Foundations/Logic/Theorems/` immediately available for `Propositional.HilbertCl`.

#### `Metalogic/DeductionTheorem.lean`

Prove the deduction theorem by well-founded recursion on `DerivationTree.height`. Simpler than Modal (no necessitation case). Produces `HasDeductionTheorem propDerivationSystem`.

#### `Metalogic/MCS.lean`

Instantiate the generic MCS framework:
- `prop_lindenbaum`: Lindenbaum's lemma
- `prop_closed_under_derivation`: Closure under derivation
- `prop_implication_property`: Implication property
- `prop_negation_complete`: Negation completeness
- `mcs_bot_not_mem`: Bottom not in MCS

### 2.3 Tag Type Activation

The tag type `Propositional.HilbertCl` already exists in `ProofSystem.lean` as:
```lean
opaque Propositional.HilbertCl : Type := Empty
```

The new `Instances.lean` will register the first concrete instances for this tag.

## 3. NaturalDeduction/Basic.lean Refactoring

### 3.1 Current State

`NaturalDeduction/Basic.lean` defines a standalone `Theory.Derivation` inductive with constructors:
- `ax` (axiom from theory `T`)
- `ass` (assumption from context `Gamma`)
- `impI` (implication introduction -- discharge assumption)
- `impE` (implication elimination -- modus ponens)
- `botE` (ex falso)

And an `InferenceSystem T Sequent` instance.

### 3.2 Refactoring Strategy

The natural deduction rules should become **derived lemmas** over the Hilbert infrastructure:

| ND Rule | Hilbert Derivation |
|---------|-------------------|
| `impI` (arrow intro) | Deduction theorem: from `A :: Gamma |- B`, get `Gamma |- A -> B` |
| `impE` (arrow elim / MP) | Modus ponens: from `Gamma |- A -> B` and `Gamma |- A`, get `Gamma |- B` |
| `botE` (ex falso) | EFQ axiom + MP: from `Gamma |- bot`, use `bot -> A` and MP to get `Gamma |- A` |
| `ass` (assumption) | Direct: `assumption` constructor of `DerivationTree` |
| `ax` (theory axiom) | Needs mapping: theory axioms as extra assumptions in context |

### 3.3 Proposed Approach

**Option A: Thin wrapper**. Keep the current `Theory.Derivation` type but redefine each constructor as a lemma calling into the Hilbert `DerivationTree`:

```lean
-- impI becomes:
theorem impI_from_hilbert (Gamma : List (PL.Proposition Atom)) (A B : PL.Proposition Atom)
    (d : DerivationTree (A :: Gamma) B) : DerivationTree Gamma (A.imp B) :=
  deduction_theorem Gamma A B d

-- impE becomes:
theorem impE_from_hilbert (Gamma : List (PL.Proposition Atom)) (A B : PL.Proposition Atom)
    (d1 : DerivationTree Gamma (A.imp B)) (d2 : DerivationTree Gamma A) :
    DerivationTree Gamma B :=
  DerivationTree.modus_ponens Gamma A B d1 d2

-- botE becomes:
theorem botE_from_hilbert (Gamma : List (PL.Proposition Atom)) (A : PL.Proposition Atom)
    (d : DerivationTree Gamma Proposition.bot) : DerivationTree Gamma A :=
  DerivationTree.modus_ponens Gamma Proposition.bot A
    (DerivationTree.weakening [] Gamma _ (DerivationTree.ax [] _ (.efq A)) (fun _ h => nomatch h))
    d
```

**Option B: Type-level abbreviation**. Make `Theory.Derivation` an abbreviation or notation that unfolds to `DerivationTree` usage. This is more invasive and may break downstream code.

**Recommendation**: Option A (thin wrapper). Create a new file `NaturalDeduction/FromHilbert.lean` that provides the ND-flavored lemma names as wrappers around Hilbert derivations. The existing `NaturalDeduction/Basic.lean` can coexist initially, with a deprecation path.

### 3.4 Theory Parameter Handling

The current ND system is parameterized by `Theory T` (a set of propositions used as extra axioms). The Hilbert system uses a fixed axiom set (the 4 propositional axioms). To handle theories:

1. Extend the Hilbert `DerivationTree` to accept an additional `Theory T` parameter, where theory axioms become available via an `ax_theory` constructor.
2. Or: model `Theory T` as additional assumptions in the context (weakening-closed).

The simplest approach: add a `theory_ax` constructor to the propositional `DerivationTree`:
```lean
| theory_ax (Gamma : List (PL.Proposition Atom)) (phi : PL.Proposition Atom)
    (h : phi in T) : DerivationTree T Gamma phi
```
making `DerivationTree` parameterized by `T : Theory Atom`.

## 4. Import Hierarchy Changes

### 4.1 Current Hierarchy

```
Foundations/Logic/ (generic infrastructure)
    |
    +-- Propositional/Defs.lean (formulas, theories)
    |       |
    |       +-- NaturalDeduction/Basic.lean (standalone ND)
    |       +-- Modal/FromPropositional.lean
    |       +-- Temporal/FromPropositional.lean
    |
    +-- Modal/Basic.lean (formulas, semantics)
    |       +-- Modal/Metalogic/DerivationTree.lean (Hilbert proof system)
    |       +-- Modal/Metalogic/DeductionTheorem.lean
    |       +-- Modal/Metalogic/MCS.lean
    |       ...
    |
    +-- Temporal/ProofSystem/ (Hilbert proof system)
    |       +-- Temporal/Metalogic/DeductionTheorem.lean
    |       +-- Temporal/Metalogic/PropositionalHelpers.lean (!)
    |       +-- Temporal/Metalogic/MCS.lean
    |       ...
    |
    +-- Bimodal/ProofSystem/ (Hilbert proof system)
            +-- Bimodal/Theorems/Combinators.lean (via Foundations bridge)
            +-- Bimodal/Theorems/Propositional/ (via Foundations bridge)
            +-- Bimodal/Metalogic/Core/DeductionTheorem.lean
            ...
```

### 4.2 Proposed New Hierarchy

```
Foundations/Logic/ (generic infrastructure -- unchanged)
    |
    +-- Propositional/
    |       Defs.lean (unchanged)
    |       ProofSystem/
    |           Axioms.lean (new: PropositionalAxiom inductive)
    |           Derivation.lean (new: DerivationTree, height, Deriv, DerivationSystem)
    |           Instances.lean (new: InferenceSystem + typeclass instances)
    |       Metalogic/
    |           DeductionTheorem.lean (new)
    |           MCS.lean (new)
    |       NaturalDeduction/
    |           Basic.lean (existing, may gain deprecation notice)
    |           FromHilbert.lean (new: ND rules as Hilbert wrappers)
    |
    +-- Modal/
    |       FromPropositional.lean (may gain derivation lifting)
    |       Metalogic/DerivationTree.lean (may import Propositional axioms?)
    |       ...
    |
    +-- Temporal/
    |       FromPropositional.lean (may gain derivation lifting)
    |       Metalogic/PropositionalHelpers.lean (candidates for refactoring)
    |       ...
    |
    +-- Bimodal/
            Embedding/PropositionalEmbedding.lean (may gain derivation lifting)
            Theorems/ (already uses Foundations bridge, minimal change needed)
            ...
```

### 4.3 What Modal/Temporal/Bimodal Should Import

**Short-term (this task)**: No changes to Modal/Temporal/Bimodal imports. The propositional Hilbert system is self-contained and serves as the foundation for future refactoring.

**Medium-term (follow-up tasks)**:

1. **Temporal/Metalogic/PropositionalHelpers.lean** should be refactored to import from Propositional's Hilbert system or (better) from Foundations generic theorems via the bridge pattern that Bimodal already uses.

2. **Modal/Metalogic/DerivationTree.lean** could extract the propositional axiom constructors of `ModalAxiom` into a shared definition, but this is complex due to the formula type difference (`Modal.Proposition` vs `PL.Proposition`).

3. **Derivation lifting**: The `FromPropositional.lean` embeddings could be extended to lift propositional `DerivationTree` derivations into Modal/Temporal/Bimodal derivations, proving that propositional theorems are automatically available in all logics. This is NOT needed for this task but is the ultimate goal.

## 5. Dependencies and Risks

### 5.1 Dependencies

| Dependency | Status | Risk |
|------------|--------|------|
| `Foundations/Logic/ProofSystem.lean` | Exists, has `PropositionalHilbert` class and `Propositional.HilbertCl` tag | None -- ready to use |
| `Foundations/Logic/InferenceSystem.lean` | Exists | None |
| `Foundations/Logic/Metalogic/Consistency.lean` | Exists, provides generic MCS framework | None |
| `Foundations/Logic/Theorems/` | Exists, provides generic propositional theorems | None -- will auto-apply once instances registered |
| `Propositional/Defs.lean` | Exists, defines formula type | None |

### 5.2 Risks

1. **Definitional equality between Lukasiewicz connectives**: The generic `Axioms.lean` uses `HasImp.imp`/`HasBot.bot` encoding while `PL.Proposition` uses direct `.imp`/`.bot` constructors. Since `PropositionalConnectives` is registered as `{ bot := .bot, imp := .imp }`, these should be definitionally equal. **Low risk** but needs verification during implementation.

2. **Theory parameter mismatch**: The current ND system is parameterized by `Theory T`, while the Hilbert system has a fixed axiom set. The refactoring needs to handle this gracefully. **Medium risk** -- may require a theory-parameterized variant of `DerivationTree`.

3. **Context representation**: The ND system uses `Finset` contexts (implicit contraction/exchange), while the Hilbert pattern uses `List` contexts. The Hilbert `DerivationTree` with `List` contexts is the established pattern and should be followed. The ND wrapper can translate between representations. **Low risk**.

4. **Opaque tag type**: `Propositional.HilbertCl` is declared `opaque`. This should be fine for instance registration but needs to be verified. All other tag types (`Modal.HilbertK`, `Modal.HilbertS5`, `Temporal.HilbertBX`, `Bimodal.HilbertTM`) follow the same pattern and work correctly. **Very low risk**.

5. **Build time impact**: Adding new files to the Propositional module will increase build time. Since these files are small and self-contained, the impact should be minimal. **Very low risk**.

## 6. Recommended Implementation Phases

### Phase 1: Axioms and DerivationTree
Create `ProofSystem/Axioms.lean` and `ProofSystem/Derivation.lean`.
- Define `PropositionalAxiom` inductive
- Define `DerivationTree` with 4 constructors (ax, assumption, modus_ponens, weakening)
- Define `height`, height lemmas
- Define `Deriv`, `Derivable`, basic combinators
- Define `propDerivationSystem : DerivationSystem (PL.Proposition Atom)`

### Phase 2: Instance Registration
Create `ProofSystem/Instances.lean`.
- Register `InferenceSystem Propositional.HilbertCl (PL.Proposition Atom)`
- Register `ModusPonens`, `HasAxiomImplyK`, `HasAxiomImplyS`, `HasAxiomEFQ`, `HasAxiomPeirce`
- Register `PropositionalHilbert Propositional.HilbertCl`
- Verify: all generic theorems from `Foundations/Logic/Theorems/` should now be available

### Phase 3: Deduction Theorem
Create `Metalogic/DeductionTheorem.lean`.
- Prove `deduction_theorem` by well-founded recursion on `height`
- Define `removeAll` helper and supporting lemmas
- Prove `prop_has_deduction_theorem : HasDeductionTheorem propDerivationSystem`

### Phase 4: MCS Properties
Create `Metalogic/MCS.lean`.
- Instantiate generic MCS framework for propositional logic
- Prove `prop_lindenbaum`, `prop_closed_under_derivation`, `prop_implication_property`, `prop_negation_complete`, `mcs_bot_not_mem`

### Phase 5: Natural Deduction Wrappers
Create `NaturalDeduction/FromHilbert.lean`.
- Define ND-flavored lemma names as wrappers around Hilbert derivations
- `impI` = deduction theorem
- `impE` = modus ponens
- `botE` = EFQ + MP
- Prove cut, weakening, and substitution as derived rules
- Add deprecation notices to `NaturalDeduction/Basic.lean` (or leave coexistence)

### Phase 6: Lakefile Registration
Add new modules to the Lean project structure so they are built.

## 7. Comparison Table: Propositional vs. Modal Pattern

| Component | Modal (S5) | Propositional (New) |
|-----------|-----------|-------------------|
| Formula type | `Modal.Proposition Atom` | `PL.Proposition Atom` |
| Connectives | `ModalConnectives` | `PropositionalConnectives` (existing) |
| Axiom inductive | `ModalAxiom` (8 constructors) | `PropositionalAxiom` (4 constructors) |
| DerivationTree | 5 constructors (ax, assumption, mp, nec, weak) | 4 constructors (ax, assumption, mp, weak) |
| Inference rules | MP + Necessitation | MP only |
| Tag type | `Modal.HilbertS5` | `Propositional.HilbertCl` (existing) |
| Bundled class | `ModalS5Hilbert` | `PropositionalHilbert` (existing) |
| DeductionTheorem | `modal_has_deduction_theorem` | `prop_has_deduction_theorem` (new) |
| MCS | `Modal.SetMaximalConsistent` | `PL.SetMaximalConsistent` (new) |

## 8. Summary of Findings

1. The Foundations infrastructure (`ProofSystem.lean`, `Theorems/`, `Metalogic/Consistency.lean`) is fully ready to support a Propositional Hilbert system. The `PropositionalHilbert` class and `Propositional.HilbertCl` tag already exist but lack concrete instances.

2. The Modal, Temporal, and Bimodal logics each independently implement the Hilbert pattern with significant propositional duplication. Creating a Propositional Hilbert system establishes the shared foundation.

3. The implementation is straightforward -- it follows the exact same pattern as Modal (the simplest existing implementation) minus the necessitation constructor.

4. The NaturalDeduction refactoring can be done as thin wrappers (ND-flavored lemma names calling Hilbert infrastructure), preserving backwards compatibility.

5. No changes to Modal/Temporal/Bimodal are needed in this task. Future tasks can refactor them to import from the Propositional Hilbert system.

6. The deduction theorem is simpler than in Modal/Temporal/Bimodal because there is no necessitation rule (which requires the empty-context constraint).

7. All generic theorems (combinators, propositional core, connectives) from Foundations will be automatically available once the `PropositionalHilbert` instance is registered.
