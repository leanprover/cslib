# Research Report: NaturalDeduction Refactoring to Eliminate Backward-Compat Aliases

**Task**: 113 -- Refactor DerivationTree Axiom Types
**Focus**: Can the NaturalDeduction files be cleanly refactored to use parameterized `DerivationTree` without backward-compatibility aliases?
**Date**: 2026-06-11

---

## 1. File-by-File Inventory

### 1.1 Basic.lean -- Standalone ND System

**What it does**: Defines the core natural deduction system (`Theory.Derivation`) as an inductive type parameterized over a `Theory Atom` (a `Set (Proposition Atom)`). Provides weakening, cut, substitution, and equivalence.

**Axiom references**: NONE. This file is completely axiom-agnostic. The ND system is parameterized over an arbitrary theory `T : Theory Atom`. It has 5 constructors:
- `ax` -- appeals to axioms from theory `T`
- `ass` -- uses a formula from the context `Gamma`
- `impI` -- implication introduction
- `impE` -- implication elimination (modus ponens)
- `botE` -- ex falso quodlibet (bottom elimination)

**Key observation**: `botE` is a PRIMITIVE constructor of the ND system. This means the ND system inherently includes EFQ as a structural rule, not as a theory axiom. This has major implications for the subsystem decomposition question.

**Refactoring needed**: None. This file is already fully generic.

### 1.2 DerivedRules.lean -- Derived ND Rules

**What it does**: Provides derived introduction/elimination rules for negation, top, conjunction, disjunction, and biconditional within the standalone ND system.

**Axiom references**: NONE directly. Uses the `[IsClassical T]` typeclass constraint for rules that require classical reasoning:
- `dne` (double negation elimination) -- requires `[IsClassical T]`
- `andE1`, `andE2` -- require `[IsClassical T]`
- `orE` -- requires `[IsClassical T]`
- `iffE1`, `iffE2` -- require `[IsClassical T]`

**Rules that work for ANY theory** (no `IsClassical` constraint):
- `negI`, `negE` -- just wrappers for `impI`/`impE`
- `topI` -- uses `impI` + `ass`
- `andI` -- uses `impI` + `impE` + `ass` + weakening
- `orI1` -- uses `impI` + `botE` + `impE` + `ass`
- `orI2` -- uses `impI` + weakening

**Key observation**: The `IsClassical T` constraint works through `IsClassical.dne A : (neg neg A -> A) in T`. This means `dne` in the ND system gets double negation elimination from the THEORY, not from the proof system's structural rules. The `dne` rule is: `impE (ax (IsClassical.dne A)) d`.

**Refactoring needed**: None. Already parameterized via `[IsClassical T]`.

### 1.3 FromHilbert.lean -- ND Wrappers for Hilbert System

**What it does**: Provides ND-flavored names (`impI`, `impE`, `botE`, `assume`, `axiomRule`) as thin wrappers around the Hilbert `DerivationTree` system. Also provides `hilbertCut`, `hilbertWeakening`, `hilbertSubstitution`, and `subst_preserves_axiom`.

**Axiom references**: EVERY definition is hardcoded to `PropositionalAxiom`:
- `impI` -- calls `deductionTheorem` with `.implyK` and `.implyS`
- `impE` -- wraps `DerivationTree.modus_ponens` at `PropositionalAxiom`
- `botE` -- uses `DerivationTree.ax [] _ (.efq A)` (EFQ axiom)
- `assume` -- wraps `DerivationTree.assumption` at `PropositionalAxiom`
- `axiomRule` -- wraps `DerivationTree.ax` at `PropositionalAxiom`
- `hilbertCut` -- uses `deductionTheorem` with `.implyK`, `.implyS`
- `hilbertWeakening` -- wraps `DerivationTree.weakening` at `PropositionalAxiom`
- `subst_preserves_axiom` -- pattern-matches all 4 `PropositionalAxiom` constructors (`.implyK`, `.implyS`, `.efq`, `.peirce`)
- `hilbertSubstitution` -- uses `subst_preserves_axiom`, fixed at `PropositionalAxiom`

**Specific axiom usage**:
- `.implyK` and `.implyS` -- used in `impI` and `hilbertCut` (via `deductionTheorem`)
- `.efq` -- used in `botE`
- `.peirce` -- used only in `subst_preserves_axiom` (pattern match on all constructors)

**Refactoring needed**: MAJOR. This is the primary file that needs parameterization.

### 1.4 HilbertDerivedRules.lean -- Derived Hilbert Rules

**What it does**: Provides derived rules (negation, conjunction, disjunction, biconditional, DNE) within the Hilbert system. These mirror the ND derived rules from DerivedRules.lean but operate on `DerivationTree` instead of `Theory.Derivation`.

**Axiom references**: EVERY definition is hardcoded to `PropositionalAxiom`. Specific axiom constructors used:
- `.implyK` -- used extensively (via `PropositionalAxiom.implyK`)
- `.implyS` -- used extensively (via `PropositionalAxiom.implyS`)
- `.efq` -- used in `hilbertTopI`, `hilbertDne`, `hilbertAndE1`
- `.peirce` -- used in `hilbertDne`, `hilbertAndE1`, `hilbertAndE2` (via `PropositionalAxiom.peirce`)

**Key observation**: Rules like `hilbertDne`, `hilbertAndE1`, `hilbertAndE2`, `hilbertOrE` inherently require Peirce's law. They cannot be generalized to work with `IntPropAxiom` or `MinPropAxiom`.

**Refactoring needed**: MAJOR. Needs to be split by axiom subsystem.

### 1.5 Equivalence.lean -- Hilbert-ND Equivalence

**What it does**: Proves the bidirectional equivalence between the Hilbert system (using `DerivationTree PropositionalAxiom`) and the ND system (using `Theory.Derivation` under `HilbertAxiomTheory`).

**Axiom references**:
- `HilbertAxiomTheory` is defined as `{ phi | PropositionalAxiom phi }`, fixed to classical logic
- `hilbertToND` -- translates `DerivationTree PropositionalAxiom` to `Theory.Derivation HilbertAxiomTheory`
- `ndToHilbert` -- translates `Theory.Derivation HilbertAxiomTheory` to `DerivationTree PropositionalAxiom`
  - The `botE` case calls `PL.botE` from FromHilbert.lean (which uses `.efq`)
  - The `impI` case calls `deductionTheorem` with `.implyK`, `.implyS`
- `hilbert_iff_nd` -- top-level equivalence, fixed at `PropositionalAxiom`

**Refactoring needed**: MAJOR. This is the centerpiece that needs to be parameterized.

---

## 2. The Two Proof Systems

Understanding the architecture is essential for answering the subsystem question.

### 2.1 Hilbert System (`DerivationTree`)
- Parameterized over `Axioms : PL.Proposition Atom -> Prop`
- Constructors: `ax`, `assumption`, `modus_ponens`, `weakening`
- NO structural `botE` -- EFQ must come from axioms
- Already supports subsystems: `MinPropAxiom` (K, S), `IntPropAxiom` (K, S, EFQ), `PropositionalAxiom` (K, S, EFQ, Peirce)

### 2.2 ND System (`Theory.Derivation`)
- Parameterized over `T : Theory Atom` (a set of propositions)
- Constructors: `ax`, `ass`, `impI`, `impE`, `botE`
- HAS structural `botE` -- EFQ is built into the proof system
- Theory provides additional axioms (like DNE for classical logic)

### 2.3 The Fundamental Mismatch

The ND system has `botE` as a primitive, which means it is always AT LEAST intuitionistic. You cannot represent minimal logic (no EFQ) in the current ND system without removing the `botE` constructor.

The Hilbert system separates concerns cleanly: the structural rules (ax, assumption, MP, weakening) contain NO logical content, and ALL logical power comes from the axiom predicate.

---

## 3. Subsystem Decomposition Analysis

### 3.1 Can we have ND equivalence for MINIMAL logic?

**No, not with the current ND system.** The ND system has `botE` as a primitive constructor. Every `Theory.Derivation` proof can use `botE` freely, regardless of what theory `T` is. This means the ND system with the empty theory `MPL = emptyset` already has EFQ, making it strictly stronger than the Hilbert system with `MinPropAxiom` (which has only K and S).

To get minimal logic ND equivalence, we would need to define a separate inductive type `MinDerivation` WITHOUT the `botE` constructor. This is a significant design change.

**Effort to fix**: Would require a new inductive type `Theory.MinDerivation` with only `ax`, `ass`, `impI`, `impE`. Then re-prove weakening, cut, substitution, etc. for this new type. Substantial but mechanical.

### 3.2 Can we have ND equivalence for INTUITIONISTIC logic?

**Yes, and this is the natural baseline.** The ND system with `botE` as a primitive exactly matches the power of the Hilbert system with `IntPropAxiom` (K, S, EFQ), when the ND theory is empty (`MPL`).

The equivalence would be:
```
Derivable IntPropAxiom phi  <->  DerivableIn (emptyset : Theory Atom) (emptyset turnstile phi)
```

This works because:
- Hilbert side: K axiom handled by deduction theorem, S axiom handled by deduction theorem, EFQ handled by the `botE` translation
- ND side: `impI` handled by deduction theorem on Hilbert side, `impE` handled by modus ponens, `botE` handled by EFQ axiom

The current `ndToHilbert` translation handles `botE` by calling `PL.botE` which uses `.efq`. If we parameterize this to require only `IntPropAxiom`, it works because `IntPropAxiom` includes `.efq`.

### 3.3 Can we have ND equivalence for CLASSICAL logic?

**Yes, this is the current state** (just needs parameterization). The equivalence would be:
```
Derivable PropositionalAxiom phi  <->  DerivableIn HilbertAxiomTheory (emptyset turnstile phi)
```

Where `HilbertAxiomTheory = { phi | PropositionalAxiom phi }`. Since `PropositionalAxiom` includes all four axioms (K, S, EFQ, Peirce), and the ND system can appeal to theory axioms via the `ax` constructor, the Peirce instances in the theory provide classical power.

### 3.4 The Clean Decomposition

Given the mismatch with minimal logic, the cleanest decomposition is:

| Level | Hilbert Axioms | ND Theory | ND botE | Equivalence |
|-------|---------------|-----------|---------|-------------|
| Intuitionistic | `IntPropAxiom` | `emptyset` | primitive | natural baseline |
| Classical | `PropositionalAxiom` | `{ phi | PropositionalAxiom phi }` | primitive + theory axioms | extends intuitionistic |

For the classical case, the extra power comes from the theory containing Peirce's law instances, which the ND `ax` constructor can appeal to.

Alternatively, we could define:
```lean
def AxiomTheory (Axioms : PL.Proposition Atom -> Prop) : Theory Atom :=
  { phi | Axioms phi }
```

And prove the equivalence generically for any `Axioms` that include at least K and S (for the deduction theorem) and EFQ (for `botE`):
```lean
theorem hilbert_iff_nd (Axioms : PL.Proposition Atom -> Prop)
    (h_K : forall phi psi, Axioms (phi.imp (psi.imp phi)))
    (h_S : forall phi psi chi, Axioms (...))
    (h_EFQ : forall phi, Axioms (Proposition.bot.imp phi)) :
    Derivable Axioms phi <-> DerivableIn (AxiomTheory Axioms) (emptyset turnstile phi)
```

This is the most general form and would cover both intuitionistic and classical as special cases.

---

## 4. Concrete Refactoring Proposal

### Phase 1: Parameterize FromHilbert.lean

**Current state**: All definitions hardcoded to `PropositionalAxiom`.

**Target**: Parameterize over `Axioms` with explicit axiom requirements.

```lean
-- Core rules that need only K, S (for deduction theorem)
noncomputable def impI
    {Axioms : PL.Proposition Atom -> Prop}
    (h_K : forall phi psi, Axioms (phi.imp (psi.imp phi)))
    (h_S : forall phi psi chi, Axioms (...))
    {Gamma : List (PL.Proposition Atom)}
    {A B : PL.Proposition Atom}
    (d : DerivationTree Axioms (A :: Gamma) B) :
    DerivationTree Axioms Gamma (A.imp B) :=
  deductionTheorem (fun phi psi => h_K phi psi) (fun phi psi chi => h_S phi psi chi) Gamma A B d

-- EFQ needs the efq axiom
def botE
    {Axioms : PL.Proposition Atom -> Prop}
    (h_EFQ : forall phi, Axioms (Proposition.bot.imp phi))
    {Gamma : List (PL.Proposition Atom)}
    {A : PL.Proposition Atom}
    (d : DerivationTree Axioms Gamma Proposition.bot) :
    DerivationTree Axioms Gamma A := ...
```

**Alternative approach** (cleaner): Define typeclasses or structure for axiom requirements:

```lean
class HasMinAxioms (Axioms : PL.Proposition Atom -> Prop) where
  implyK : forall phi psi, Axioms (phi.imp (psi.imp phi))
  implyS : forall phi psi chi, Axioms (...)

class HasIntAxioms (Axioms : PL.Proposition Atom -> Prop) extends HasMinAxioms Axioms where
  efq : forall phi, Axioms (Proposition.bot.imp phi)

class HasClAxioms (Axioms : PL.Proposition Atom -> Prop) extends HasIntAxioms Axioms where
  peirce : forall phi psi, Axioms (((phi.imp psi).imp phi).imp phi)
```

This would allow the rules to take `[HasMinAxioms Axioms]` or `[HasIntAxioms Axioms]` constraints. However, this introduces new typeclass infrastructure that may be over-engineering for the current needs.

**Recommended approach**: Use explicit function parameters (matching the existing `deductionTheorem` pattern), with convenience wrappers for `PropositionalAxiom`, `IntPropAxiom`, and `MinPropAxiom`.

### Phase 2: Split HilbertDerivedRules.lean

Split into layers based on axiom requirements:

**MinPropAxiom layer** (K, S only):
- Nothing currently -- all rules use at least EFQ

**IntPropAxiom layer** (K, S, EFQ):
- `hilbertNegI` (uses `impI` which needs K, S)
- `hilbertNegE` (uses `impE`, trivial)
- `hilbertTopI` (uses `.efq`)
- `hilbertAndI` (uses `impI`)
- `hilbertOrI1` (uses `impI` + `botE` which needs EFQ)
- `hilbertOrI2` (uses `.implyK`)
- `hilbertIffI` (uses `hilbertAndI`)

**PropositionalAxiom layer** (K, S, EFQ, Peirce):
- `hilbertDne` (uses `.peirce`)
- `hilbertAndE1` (uses `.peirce` + `.efq`)
- `hilbertAndE2` (uses `hilbertDne` which uses `.peirce`)
- `hilbertOrE` (uses `hilbertDne` + `hilbertNegI`)
- `hilbertIffE1` (uses `hilbertAndE1`)
- `hilbertIffE2` (uses `hilbertAndE2`)

**Important note on conjunction/disjunction**: The Lukasiewicz encodings (`and = neg(A -> neg B)`, `or = neg A -> B`) are only classically equivalent to the standard definitions. Conjunction elimination and disjunction elimination inherently require classical reasoning. This is NOT an artifact of the encoding -- it is a fundamental logical fact when using only implication and bottom as primitives.

### Phase 3: Parameterize Equivalence.lean

**Current**: Fixed at `PropositionalAxiom`.

**Target**: Generic `AxiomTheory` with axiom requirements.

```lean
def AxiomTheory (Axioms : PL.Proposition Atom -> Prop) : Theory Atom :=
  { phi | Axioms phi }

-- Generic equivalence requiring at least IntPropAxiom-level axioms
theorem hilbert_iff_nd
    {Axioms : PL.Proposition Atom -> Prop}
    (h_K : forall phi psi, Axioms (phi.imp (psi.imp phi)))
    (h_S : forall phi psi chi, Axioms (...))
    (h_EFQ : forall phi, Axioms (Proposition.bot.imp phi))
    {phi : PL.Proposition Atom} :
    Derivable Axioms phi <->
    DerivableIn (AxiomTheory Axioms) (emptyset turnstile phi)
```

This single generic theorem covers both intuitionistic and classical as special cases:
- `hilbert_iff_nd (Axioms := IntPropAxiom) ...` gives the intuitionistic equivalence
- `hilbert_iff_nd (Axioms := PropositionalAxiom) ...` gives the classical equivalence

### Phase 4: Parameterize subst_preserves_axiom

This function pattern-matches on all 4 `PropositionalAxiom` constructors. To generalize, either:
1. Define separate `subst_preserves_axiom` for each axiom type (mechanical)
2. Define a typeclass `SubstPreserving Axioms` with a proof that substitution preserves the axiom predicate
3. Prove it separately for `IntPropAxiom` and `MinPropAxiom`

The most practical approach is option 1 or 3.

### Phase 5: Remove Backward-Compat Aliases

Once all files use the parameterized versions, delete from `Derivation.lean`:
```lean
-- DELETE these:
abbrev ClDerivationTree := @DerivationTree Atom PropositionalAxiom
abbrev ClDeriv := @Deriv Atom PropositionalAxiom
abbrev ClDerivable := @Derivable Atom PropositionalAxiom
def clPropDerivationSystem := propDerivationSystem (@PropositionalAxiom Atom)
```

---

## 5. Impact Analysis

### Files that reference `PropositionalAxiom` directly (outside NaturalDeduction):

| File | Usage | Impact |
|------|-------|--------|
| `ProofSystem/Axioms.lean` | Definition | No change needed |
| `ProofSystem/Derivation.lean` | Aliases (to be removed) | Remove aliases |
| `ProofSystem/Instances.lean` | Classical instances | No change (correctly fixed at classical) |
| `ProofSystem/IntMinInstances.lean` | Int/Min instances | No change |
| `Metalogic/DeductionTheorem.lean` | `HasHilbertTree` instance | Already partially parameterized; the global instance is fixed at `PropositionalAxiom` but `deductionTheorem` itself is generic |
| `Metalogic/Soundness.lean` | Soundness proofs | Fixed at classical (correct) |
| `Metalogic/Completeness.lean` | Completeness proofs | Fixed at classical (correct) |
| `Metalogic/MCS.lean` | MCS framework | Already parameterized |

### Downstream consumers of backward-compat aliases:

**No files use `ClDerivationTree`, `ClDeriv`, `ClDerivable`, or `clPropDerivationSystem`.** The grep shows these names appear ONLY in `Derivation.lean` where they are defined. This means the aliases can be removed with zero downstream impact.

---

## 6. Effort and Risk Assessment

### Effort Estimate

| Phase | Files | Complexity | Estimate |
|-------|-------|-----------|----------|
| Phase 1: Parameterize FromHilbert.lean | 1 | Medium | Straightforward but many definitions |
| Phase 2: Split HilbertDerivedRules.lean | 1 | Medium-High | Need to carefully trace axiom dependencies |
| Phase 3: Parameterize Equivalence.lean | 1 | Medium | Key architectural change |
| Phase 4: Parameterize subst_preserves_axiom | 1 | Low | Mechanical |
| Phase 5: Remove aliases | 1 | Trivial | Delete 4 lines |

**Total estimate**: Medium-sized refactoring. The core challenge is in Phases 1-3.

### Risks

1. **Deduction theorem dependency**: The deduction theorem is already parameterized over `Axioms` with explicit `h_implyK` and `h_implyS` parameters. This is favorable -- the infrastructure is already in place.

2. **`botE` in `ndToHilbert`**: The `ndToHilbert` function's `botE` case currently calls `PL.botE` from FromHilbert.lean, which is fixed at `PropositionalAxiom`. After parameterization, this call would need to take the EFQ axiom proof as a parameter. Since EFQ is required for the equivalence anyway (the ND system has structural `botE`), this is natural.

3. **`HasHilbertTree` global instance**: The global `HasHilbertTree` instance in DeductionTheorem.lean is fixed at `PropositionalAxiom`. The `impI` in FromHilbert.lean uses this. After parameterization, `impI` would either need a local `HasHilbertTree` instance (matching the pattern in `deductionTheorem` itself) or explicit axiom parameters.

4. **Build breakage risk**: LOW. The NaturalDeduction files are leaf modules -- nothing imports them. The only concern is internal consistency within the NaturalDeduction directory.

### Mitigation

- The `deductionTheorem` function already demonstrates the pattern: parameterize over `Axioms` with explicit `h_implyK`/`h_implyS` parameters. Follow this existing pattern.
- The `letI` pattern used in `deductionTheorem` (creating a local `HasHilbertTree` instance) can be reused in `impI`, `hilbertCut`, etc.

---

## 7. Recommendation

**Proceed with the refactoring.** The analysis shows:

1. **The backward-compat aliases are unused** -- they can be deleted immediately with zero impact.

2. **The refactoring is feasible** -- the existing `deductionTheorem` already demonstrates the parameterization pattern needed.

3. **The subsystem decomposition is natural** but with a caveat:
   - **Intuitionistic-Classical split**: Clean and well-motivated. The ND system's structural `botE` makes intuitionistic logic the natural baseline.
   - **Minimal logic**: Not achievable with the current ND inductive type (would need a separate `MinDerivation` type without `botE`). Recommend deferring this to a separate task.

4. **The generic equivalence theorem** (parameterized over any `Axioms` with K, S, EFQ) is the architecturally cleanest approach and covers both intuitionistic and classical as special cases.

### Recommended Approach

1. Define `AxiomTheory (Axioms)` generically
2. Parameterize `FromHilbert.lean` definitions over `Axioms` with explicit axiom requirements
3. Split `HilbertDerivedRules.lean` into intuitionistic and classical layers
4. Prove the generic `hilbert_iff_nd` theorem requiring K, S, EFQ
5. Provide classical and intuitionistic instantiations as corollaries
6. Delete the unused backward-compat aliases
7. Defer minimal logic ND to a separate task (requires new inductive type)

### What NOT to do

- Do NOT try to parameterize the ND system (`Theory.Derivation`) itself -- it is already generic over theories
- Do NOT try to support minimal logic without a new inductive type
- Do NOT introduce typeclasses for axiom requirements (explicit parameters match the existing codebase style better)
