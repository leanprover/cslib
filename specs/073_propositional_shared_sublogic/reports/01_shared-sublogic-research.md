# Research Report: Make Propositional a Shared Sub-Logic

## 1. Propositional/Defs.lean Analysis

`PL.Proposition` (in `Cslib.Logic.PL` namespace) is an inductive with three constructors:

```lean
inductive Proposition (Atom : Type u) : Type u where
  | atom (x : Atom)
  | bot
  | imp (a b : Proposition Atom)
```

It provides:
- **Derived connectives**: `neg`, `top`, `or`, `and` (all `abbrev`, Lukasiewicz-style)
- **Typeclass instances**: `Bot`, `Top`, `PropositionalConnectives`, `DecidableEq`, `BEq`, `Monad`
- **Substitution**: `Proposition.subst` and a `Monad` instance (`pure := atom`, `bind := subst`)
- **Theories**: `Theory Atom := Set (Proposition Atom)`, with `MPL`, `IPL`, `CPL`
- **Theory properties**: `IsIntuitionistic`, `IsClassical` classes with membership witnesses
- **Completion**: `intuitionisticCompletion` lifting any theory to intuitionistic logic
- **Scoped notation**: `⊥ ⊤ ∧ ∨ → ¬`

Additionally, `Propositional/NaturalDeduction/Basic.lean` provides:
- Sequent-style natural deduction (`Theory.Derivation` inductive)
- Weakening, cut, substitution rules
- Theory-relative equivalence (`Theory.equiv`, `Theory.Equiv`)

## 2. Modal Formula Comparison

`Modal.Proposition` (in `Cslib.Logic.Modal` namespace):

```lean
inductive Proposition (Atom : Type u) : Type u where
  | atom (p : Atom)
  | bot
  | imp (phi1 phi2 : Proposition Atom)
  | box (phi : Proposition Atom)
```

**Comparison with PL.Proposition**:
- The first three constructors (`atom`, `bot`, `imp`) are structurally identical to PL.Proposition
- `box` is the additional modal constructor
- Derived connectives (`neg`, `top`, `or`, `and`) are defined identically using Lukasiewicz encoding
- Additionally defines `diamond`, `iff` as modal-specific derived connectives
- Registers as `ModalConnectives` (which extends `PropositionalConnectives`)
- Also defines `Model`, `Satisfies`, `Judgement`, and semantic theorems (K, T, B, 4, 5, D axioms) all in the same file

**Import structure**: `Modal/Basic.lean` imports `Cslib.Foundations.Logic.Connectives` but NOT `Cslib.Logics.Propositional.Defs`.

## 3. Temporal Formula Comparison

`Temporal.Formula` (in `Cslib.Logic.Temporal` namespace):

```lean
inductive Formula (Atom : Type u) : Type u where
  | atom (p : Atom)
  | bot
  | imp (phi1 phi2 : Formula Atom)
  | untl (phi1 phi2 : Formula Atom)
  | snce (phi1 phi2 : Formula Atom)
```

**Comparison with PL.Proposition**:
- First three constructors (`atom`, `bot`, `imp`) are structurally identical
- `untl` and `snce` are additional temporal constructors
- Derived connectives (`neg`, `top`, `or`, `and`) are defined identically
- Additionally defines temporal operators (`someFuture`, `allFuture`, `somePast`, `allPast`, etc.)
- Registers as `TemporalConnectives`
- Includes `Countable`, `Infinite`, `Denumerable` instances, `BEq` laws, complexity measure, temporal depth, swap temporal duality, atoms collection

**Import structure**: `Temporal/Syntax/Formula.lean` imports `Cslib.Foundations.Logic.Connectives` but NOT `Cslib.Logics.Propositional.Defs`.

## 4. Bimodal Formula Comparison

`Bimodal.Formula` (in `Cslib.Logic.Bimodal` namespace):

```lean
inductive Formula (Atom : Type u) : Type u where
  | atom (p : Atom)
  | bot
  | imp (phi1 phi2 : Formula Atom)
  | box (phi : Formula Atom)
  | untl (phi1 phi2 : Formula Atom)
  | snce (phi1 phi2 : Formula Atom)
```

**Comparison**: Union of Modal and Temporal constructors. Registers as `BimodalConnectives`. Does NOT extend either Modal or Temporal -- it is a standalone inductive that happens to duplicate all their constructors.

## 5. Structural Feasibility: Lean 4 Constraints

### Can You Extend Inductives in Lean 4?

**No.** Lean 4 does not support inductive extension or open inductives. You cannot write:

```lean
-- NOT valid Lean 4:
inductive Modal.Proposition extends PL.Proposition where
  | box (phi : Modal.Proposition)
```

Each inductive type must be self-contained with all constructors defined at once.

### Available Approaches

**Approach A: Embedding Functions (Current Pattern)**
Already implemented via `PL.Proposition.toModal`, `PL.Proposition.toTemporal`, etc. in `Bimodal/Embedding/`. This is the cleanest Lean-idiomatic approach and is already in place.

**Approach B: Shared Propositional Fragment Typeclass**
Already implemented via `PropositionalConnectives` in `Foundations/Logic/Connectives.lean`. All four formula types register as instances. Generic theorems in `Foundations/Logic/Theorems/` use these typeclasses.

**Approach C: Parametric Inductive with Extensible Constructors**
Define a formula type parameterized over an "extension" type:
```lean
inductive Formula (Atom : Type u) (Ext : Formula Atom -> Type u) : Type u where
  | atom (p : Atom)
  | bot
  | imp (phi psi : Formula Atom Ext)
  | ext (e : Ext (Formula Atom Ext))
```
This is theoretically possible but would require massive refactoring of all four formula types and all downstream proofs. The ergonomics are poor (every pattern match must handle `ext`).

**Approach D: Sum-of-Inductives with a Shared Base**
Define propositional formulas as the base, then define modal/temporal as wrappers:
```lean
inductive ModalFormula (Atom) where
  | prop (p : PL.Proposition Atom)
  | box (phi : ModalFormula Atom)
```
This breaks pattern matching ergonomics severely: every propositional constructor requires wrapping/unwrapping through `.prop`. It also breaks the `DecidableEq`, `BEq` derives.

## 6. PropositionalConnectives Typeclass as Integration Point

### Current State

`PropositionalConnectives` is already defined in `Foundations/Logic/Connectives.lean` and all four formula types register as instances:

```lean
class PropositionalConnectives (F : Type*) extends HasBot F, HasImp F
-- PL.Proposition: instance
-- Modal.Proposition: via ModalConnectives extends PropositionalConnectives
-- Temporal.Formula: via TemporalConnectives extends PropositionalConnectives
-- Bimodal.Formula: via BimodalConnectives extends ModalConnectives extends PropositionalConnectives
```

### Generic Infrastructure Already Built

The `Foundations/Logic/` directory already contains:
1. **Generic axiom definitions** (`Axioms.lean`): `ImplyK`, `ImplyS`, `EFQ`, `Peirce`, etc. -- all parameterized over `HasBot F`, `HasImp F`
2. **Generic proof system typeclasses** (`ProofSystem.lean`): `PropositionalHilbert`, `ModalHilbert`, `ModalS5Hilbert`, `TemporalBXHilbert`, `BimodalTMHilbert`
3. **Generic propositional theorems** (`Theorems/Propositional/Core.lean`, `Theorems/Combinators.lean`): ~625 lines of theorems generic over `[PropositionalHilbert S]`
4. **Generic modal theorems** (`Theorems/Modal/`): generic over `[ModalHilbert S]`, `[ModalS5Hilbert S]`
5. **Generic temporal theorems** (`Theorems/Temporal/`): generic over `[TemporalBXHilbert S]`

### What's Already Working

The Bimodal proof system already delegates propositional theorems to Foundations:
- `Bimodal/Theorems/Combinators.lean` uses a "wrap/unwrap bridge pattern" to delegate to `Foundations.Logic.Theorems.Combinators`
- `Bimodal/Theorems/Propositional/Core.lean` delegates to `Foundations.Logic.Theorems.Propositional.Core`

### What's NOT Working (The Real Problem)

1. **Modal does not use the Foundations generic theorems at all.** The Modal metalogic (`Modal/Metalogic/DerivationTree.lean`) defines its own `ModalAxiom` inductive with propositional axioms inlined, and its `DerivationTree` is self-contained. It does NOT register a `PropositionalHilbert` or `ModalS5Hilbert` instance for `Modal.HilbertS5`.

2. **Temporal duplicates propositional helpers.** `Temporal/Metalogic/PropositionalHelpers.lean` (228 lines) manually re-proves `double_negation`, `efq_axiom`, `imp_trans`, `pairing`, and other propositional combinator derivations specifically for `Temporal.Formula`, even though identical proofs exist at the Foundations level. The Temporal proof system DOES register `PropositionalHilbert` and `TemporalBXHilbert` instances.

3. **No import from Propositional/ to Modal/ or Temporal/.** Neither Modal nor Temporal imports anything from `Logics/Propositional/`. The embeddings only exist in `Bimodal/Embedding/`.

## 7. NaturalDeduction Reuse

### Current State

`Propositional/NaturalDeduction/Basic.lean` defines a sequent-style natural deduction system with:
- `Derivation` inductive (ax, ass, impI, impE, botE)
- Weakening, cut, substitution
- Theory equivalence

### Could Modal/Temporal Benefit?

**Not directly.** Modal and Temporal use Hilbert-style proof systems (axiom schemata + modus ponens + necessitation), not natural deduction. The proof architectures are fundamentally different:

- Propositional: Natural deduction with contexts (`Finset`) and explicit hypotheses
- Modal/Temporal/Bimodal: Hilbert-style derivation trees with assumption lists (`List`)

However, if Propositional were also given a Hilbert-style proof system with a `PropositionalHilbert` instance for `Propositional.HilbertCl`, then the Propositional generic theorems could serve as a validation target.

**Verdict**: NaturalDeduction reuse across Modal/Temporal is not feasible given the different proof system architectures.

## 8. Impact Assessment

### What the Task Actually Requires

Given the Lean 4 constraint that inductives cannot be extended, the task "make Propositional a shared sub-logic" cannot mean literal type inheritance. Instead, it means establishing Propositional as a genuine **intermediate dependency layer** where Modal and Temporal:
1. Import from `Propositional/` for embedding functions
2. Reuse the Foundations generic propositional theorem infrastructure consistently
3. Have explicit embeddings FROM Propositional (not just ad-hoc duplication)

### Current Dependency Flow

```
Foundations/Logic/Connectives -----> Propositional/Defs
                              |
                              +----> Modal/Basic
                              |
                              +----> Temporal/Syntax/Formula
                              |
                              +----> Bimodal/Syntax/Formula
                              
Bimodal/Embedding/ imports from all four
```

### Desired Dependency Flow

```
Foundations/Logic/ --> Propositional/ --> Modal/ --> Bimodal/
                                    |            |
                                    +--> Temporal/ --+
```

### Concrete Changes Required

**Phase 1: Add Propositional-to-Modal and Propositional-to-Temporal embeddings (LOW RISK)**
- Move `PL.Proposition.toModal` from `Bimodal/Embedding/PropositionalEmbedding.lean` to a new `Propositional/Embedding/Modal.lean`
- Move `PL.Proposition.toTemporal` similarly to `Propositional/Embedding/Temporal.lean`
- Keep `PL.Proposition.toBimodal` in `Bimodal/Embedding/`
- Update `Bimodal/Embedding/PropositionalEmbedding.lean` to import from the new locations
- Files affected: ~3-5 files (new embedding files + updated Bimodal import)

**Phase 2: Make Modal import from Propositional (MEDIUM RISK)**
- `Modal/Basic.lean` would add `import Cslib.Logics.Propositional.Defs` (or just the embedding module)
- No changes to `Modal.Proposition` itself (the inductive stays the same)
- Provide a `Coe (PL.Proposition Atom) (Modal.Proposition Atom)` at the Modal level
- Files affected: 1-2 files (Modal/Basic.lean, possibly Modal/Metalogic/*.lean)

**Phase 3: Make Temporal import from Propositional (MEDIUM RISK)**
- `Temporal/Syntax/Formula.lean` would add `import Cslib.Logics.Propositional.Defs`
- Provide a `Coe (PL.Proposition Atom) (Temporal.Formula Atom)` at the Temporal level
- Files affected: 1-2 files

**Phase 4: Eliminate duplicated propositional helpers in Temporal (MEDIUM-HIGH RISK)**
- Replace `Temporal/Metalogic/PropositionalHelpers.lean` (228 lines) with delegation to Foundations generic theorems via the wrap/unwrap bridge pattern (as Bimodal already does)
- Files affected: ~3-5 files (PropositionalHelpers.lean + callers in Chronicle/*.lean)

**Phase 5: Register Modal proof system instances with Foundations (MEDIUM-HIGH RISK)**
- Register `Modal.HilbertS5` as `ModalS5Hilbert` instance, connecting to Foundations
- This would allow Modal metalogic to use generic propositional theorems
- Files affected: ~2-5 files (new Instances.lean + possible DerivationTree adjustments)

### Risk Analysis

| Risk | Severity | Mitigation |
|------|----------|------------|
| Import cycle | High | Embeddings must flow one-way: PL -> Modal/Temporal. No reverse imports. |
| Notation conflicts | Medium | PL, Modal, Temporal all define scoped `→ ∧ ∨ ¬`. Opening multiple namespaces simultaneously will cause ambiguity. Mitigated by using qualified names or selective `open`. |
| Compile time regression | Low | Adding imports increases module dependencies but PL/Defs.lean is small (~163 lines). |
| Breaking API changes | Low | No changes to existing inductive types. Coercions/embeddings are additive. |
| Proof breakage in Temporal metalogic | Medium | Replacing PropositionalHelpers with Foundations delegation requires verifying all Chronicle callers still work. |
| Modal metalogic proof breakage | Medium | Registering `ModalS5Hilbert` instance requires careful alignment of the concrete `DerivationTree` with the abstract proof system typeclasses. |

### File Count Summary

| Phase | Files Changed | New Files | Risk |
|-------|--------------|-----------|------|
| Phase 1 (Embedding relocation) | 1-2 | 2 | Low |
| Phase 2 (Modal imports PL) | 1-2 | 0 | Medium |
| Phase 3 (Temporal imports PL) | 1-2 | 0 | Medium |
| Phase 4 (Eliminate PL helpers) | 3-5 | 0 | Medium-High |
| Phase 5 (Modal proof system instances) | 2-5 | 1 | Medium-High |
| **Total** | **8-16** | **3** | |

## 9. Recommendation

### Feasibility: FEASIBLE with caveats

The task is structurally feasible because:
1. The typeclass hierarchy (`PropositionalConnectives`, `PropositionalHilbert`) already exists
2. The embedding functions already exist (just in the wrong location)
3. The generic theorem infrastructure already exists in Foundations
4. The Bimodal proof system already demonstrates the delegation pattern

### Recommended Approach

**Do Phases 1-3 first** (Low to Medium risk, ~5 files). This establishes the dependency flow `Propositional -> {Modal, Temporal} -> Bimodal` and provides coercions. No existing proofs break.

**Defer Phases 4-5** (Medium-High risk) to a follow-up task. These involve replacing working proof infrastructure and are higher risk.

### What This Refactoring Does NOT Do

- It does NOT unify the inductive types (impossible in Lean 4)
- It does NOT reduce the constructor definitions (each formula type keeps its own `atom`, `bot`, `imp`)
- It does NOT make `Modal.Proposition` literally "extend" `PL.Proposition`

### What This Refactoring DOES Do

- Establishes Propositional as a genuine intermediate layer in the import DAG
- Provides direct coercions from PL to Modal and Temporal (currently only available through Bimodal)
- Moves embedding functions to their natural location (near the source type, not the target)
- Enables future elimination of duplicated propositional proof machinery
- Makes the "Foundations -> Propositional -> {Modal, Temporal} -> Bimodal" architecture explicit
