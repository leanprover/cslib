# Research Report: Parameterize Natural Deduction Equivalence

**Task**: 120 -- Parameterize Natural Deduction Equivalence
**Date**: 2026-06-11
**Session**: sess_1781188006_dc2c9d

---

## 1. Summary of Findings

The NaturalDeduction directory contains 5 files, of which 2 are already fully generic (Basic.lean, DerivedRules.lean) and 3 need refactoring (FromHilbert.lean, HilbertDerivedRules.lean, Equivalence.lean). All three are hardcoded to `PropositionalAxiom` (classical). The refactoring is feasible because:

1. The `deductionTheorem` in `DeductionTheorem.lean` is already parameterized over `Axioms` with explicit `h_implyK`/`h_implyS` parameters, providing the exact pattern to follow.
2. The NaturalDeduction files are true leaf modules -- nothing outside the directory imports them.
3. The backward-compat aliases (`ClDerivationTree`, `ClDeriv`, etc.) mentioned in the Derivation.lean docstring were already removed in a prior refactoring -- only the stale docstring reference remains.
4. The ND system's structural `botE` constructor makes intuitionistic logic the natural baseline (minimal logic ND equivalence is out of scope, as stated in the task description).

---

## 2. Current Architecture Analysis

### 2.1 File Dependency Graph

```
Basic.lean <-------------- DerivedRules.lean
    |                         (standalone, no changes needed)
    |
    +--- Equivalence.lean --+
    |                       |
    +--- FromHilbert.lean --+--- HilbertDerivedRules.lean
         (imports DeductionTheorem.lean)
```

External dependencies:
- `FromHilbert.lean` imports `Cslib.Logics.Propositional.Metalogic.DeductionTheorem`
- `HilbertDerivedRules.lean` imports `FromHilbert.lean`
- `Equivalence.lean` imports both `Basic.lean` and `FromHilbert.lean`

Nothing outside the `NaturalDeduction/` directory imports any of these files.

### 2.2 File-by-File Analysis

#### Basic.lean -- Standalone ND System (NO CHANGES NEEDED)

Defines `Theory.Derivation` with 5 constructors: `ax`, `ass`, `impI`, `impE`, `botE`. Parameterized over `T : Theory Atom` (a `Set (Proposition Atom)`). The `botE` constructor is primitive, making the system inherently at least intuitionistic.

Also provides: weakening, cut, substitution, atom transport, equivalence.

#### DerivedRules.lean -- Derived ND Rules (NO CHANGES NEEDED)

Provides derived rules for the standalone ND system. Already properly parameterized:
- **No constraint needed**: `negI`, `negE`, `topI`, `andI`, `orI1`, `orI2`, `iffI`
- **Requires `[IsClassical T]`**: `dne`, `andE1`, `andE2`, `orE`, `iffE1`, `iffE2`

The `IsClassical T` class (from `Defs.lean`) provides `dne (A) : (neg neg A -> A) in T`. This is the correct parameterization for the ND side.

#### FromHilbert.lean -- ND Wrappers for Hilbert System (NEEDS PARAMETERIZATION)

Provides ND-flavored names as wrappers around the Hilbert `DerivationTree`:
- `impI` -- calls `deductionTheorem` with `.implyK`, `.implyS`
- `impE` -- wraps `DerivationTree.modus_ponens`
- `botE` -- uses `DerivationTree.ax [] _ (.efq A)`
- `assume` -- wraps `DerivationTree.assumption`
- `axiomRule` -- wraps `DerivationTree.ax`
- `hilbertCut` -- uses `deductionTheorem`
- `hilbertWeakening` -- wraps `DerivationTree.weakening`
- `subst_preserves_axiom` -- pattern matches on all 4 `PropositionalAxiom` constructors
- `hilbertSubstitution` -- uses `subst_preserves_axiom`
- Deriv-level versions of each

Every definition is hardcoded to `PropositionalAxiom`.

#### HilbertDerivedRules.lean -- Derived Hilbert Rules (NEEDS SPLITTING)

Mirrors DerivedRules.lean but for the Hilbert `DerivationTree`. All hardcoded to `PropositionalAxiom`. Provides:
- `hilbertNegI`, `hilbertNegE`, `hilbertTopI`, `hilbertAndI`, `hilbertOrI1`, `hilbertOrI2`, `hilbertIffI`
- `hilbertDne`, `hilbertAndE1`, `hilbertAndE2`, `hilbertOrE`, `hilbertIffE1`, `hilbertIffE2`
- Deriv-level wrappers for each

#### Equivalence.lean -- Hilbert-ND Equivalence (NEEDS PARAMETERIZATION)

Proves bidirectional equivalence between Hilbert and ND systems:
- `HilbertAxiomTheory` = `{ phi | PropositionalAxiom phi }` (fixed to classical)
- `hilbertToND` : `DerivationTree PropositionalAxiom Gamma.toList phi -> Theory.Derivation HilbertAxiomTheory Gamma phi`
- `ndToHilbert` : reverse direction (noncomputable, uses deduction theorem)
- `hilbert_iff_nd` : top-level equivalence for closed derivability

---

## 3. Axiom Type Class Inventory

### 3.1 Concrete Axiom Predicates (in `ProofSystem/Axioms.lean`)

| Predicate | Constructors | Logic Level |
|-----------|-------------|-------------|
| `MinPropAxiom` | `implyK`, `implyS` | Minimal |
| `IntPropAxiom` | `implyK`, `implyS`, `efq` | Intuitionistic |
| `PropositionalAxiom` | `implyK`, `implyS`, `efq`, `peirce` | Classical |

Subsumption proofs exist:
- `MinPropAxiom.toIntProp : MinPropAxiom phi -> IntPropAxiom phi`
- `IntPropAxiom.toProp : IntPropAxiom phi -> PropositionalAxiom phi`

### 3.2 Abstract Type Classes (in `Foundations/Logic/ProofSystem.lean`)

```
MinimalHilbert S (F := F)
  extends ModusPonens S, HasAxiomImplyK S, HasAxiomImplyS S

IntuitionisticHilbert S (F := F)
  extends MinimalHilbert S, HasAxiomEFQ S

ClassicalHilbert S (F := F)
  extends IntuitionisticHilbert S, HasAxiomPeirce S
```

### 3.3 Tag Types and Instances

| Tag Type | Axiom Predicate | Hilbert Class |
|----------|----------------|---------------|
| `Propositional.HilbertMin` | `MinPropAxiom` | `MinimalHilbert` |
| `Propositional.HilbertInt` | `IntPropAxiom` | `IntuitionisticHilbert` |
| `Propositional.HilbertCl` | `PropositionalAxiom` | `ClassicalHilbert` |

### 3.4 ND-Side Theory Classes (in `Defs.lean`)

| Class | Requirement | Effect |
|-------|------------|--------|
| `IsIntuitionistic T` | `efq (A) : (bot -> A) in T` | Theory contains EFQ |
| `IsClassical T` | `dne (A) : (neg neg A -> A) in T` | Theory contains DNE |

### 3.5 "Intuitionistic" vs "Classical" for the Equivalence

The ND system has structural `botE`, so EFQ is always available on the ND side regardless of the theory. For the Hilbert-ND equivalence:

- **Intuitionistic equivalence**: `IntPropAxiom` on Hilbert side, empty theory on ND side. The ND's structural `botE` matches Hilbert's `efq` axiom.
- **Classical equivalence**: `PropositionalAxiom` on Hilbert side, `HilbertAxiomTheory` (containing Peirce instances) on ND side. The ND `ax` constructor accesses Peirce from the theory.
- **Generic equivalence**: Any `Axioms` with K, S, EFQ on Hilbert side, `AxiomTheory Axioms` on ND side.

---

## 4. Rule-by-Rule Analysis for HilbertDerivedRules

### 4.1 Axiom Dependencies per Rule

| Rule | Uses K | Uses S | Uses EFQ | Uses Peirce | Minimum Axioms |
|------|--------|--------|----------|-------------|----------------|
| `hilbertNegI` | yes (via impI) | yes (via impI) | no | no | K, S |
| `hilbertNegE` | no | no | no | no | none (just MP) |
| `hilbertTopI` | no | no | yes (.efq) | no | EFQ |
| `hilbertAndI` | yes (via impI) | yes (via impI) | no | no | K, S |
| `hilbertOrI1` | yes (via impI + botE) | yes (via impI) | yes (via botE -> .efq) | no | K, S, EFQ |
| `hilbertOrI2` | yes (.implyK) | no | no | no | K |
| `hilbertIffI` | yes (via andI) | yes (via andI) | no | no | K, S |
| `hilbertDne` | yes (.implyK) | yes (.implyS) | yes (.efq) | yes (.peirce) | K, S, EFQ, Peirce |
| `hilbertAndE1` | yes (.implyK) | yes (.implyS) | yes (.efq) | yes (.peirce) | K, S, EFQ, Peirce |
| `hilbertAndE2` | yes (.implyK) | yes (.implyS) | yes (via dne) | yes (via dne) | K, S, EFQ, Peirce |
| `hilbertOrE` | yes (via impI + negI) | yes (via impI + negI) | yes (via botE) | yes (via dne) | K, S, EFQ, Peirce |
| `hilbertIffE1` | (via andE1) | (via andE1) | (via andE1) | (via andE1) | K, S, EFQ, Peirce |
| `hilbertIffE2` | (via andE2) | (via andE2) | (via andE2) | (via andE2) | K, S, EFQ, Peirce |

### 4.2 Proposed Split

**Intuitionistic layer** (requires K, S, EFQ -- equivalent to `IntPropAxiom`):
- `hilbertNegI` (K, S via deduction theorem)
- `hilbertNegE` (no axioms, just MP)
- `hilbertTopI` (EFQ)
- `hilbertAndI` (K, S via deduction theorem)
- `hilbertOrI1` (K, S, EFQ via deduction theorem + botE)
- `hilbertOrI2` (K only, but grouping with other introduction rules)
- `hilbertIffI` (K, S via andI)

**Classical layer** (additionally requires Peirce -- equivalent to `PropositionalAxiom`):
- `hilbertDne` (Peirce, K, S, EFQ)
- `hilbertAndE1` (Peirce, K, S, EFQ)
- `hilbertAndE2` (Peirce via dne)
- `hilbertOrE` (Peirce via dne)
- `hilbertIffE1` (via andE1)
- `hilbertIffE2` (via andE2)

**Rationale**: The intuitionistic/classical split follows the natural boundary. Rules in the intuitionistic layer use only K, S, and EFQ. The classical layer adds Peirce. This matches the Lukasiewicz encoding: introduction rules for conjunction and disjunction are intuitionistically valid, but elimination rules for conjunction (`andE1`, `andE2`), disjunction (`orE`), and biconditional (`iffE1`, `iffE2`) require DNE (which requires Peirce).

---

## 5. Parameterization Strategy

### 5.1 Approach: Explicit Axiom Parameters (Matching Existing Pattern)

The `deductionTheorem` in `DeductionTheorem.lean` already demonstrates the pattern:

```lean
noncomputable def deductionTheorem
    {Axioms : PL.Proposition Atom -> Prop}
    (h_implyK : forall (phi psi : PL.Proposition Atom), Axioms (phi.imp (psi.imp phi)))
    (h_implyS : forall (phi psi chi : PL.Proposition Atom),
      Axioms ((phi.imp (psi.imp chi)).imp ((phi.imp psi).imp (phi.imp chi))))
    (Gamma : List ...) (A B : ...) (d : DerivationTree Axioms (A :: Gamma) B) :
    DerivationTree Axioms Gamma (A.imp B)
```

This uses explicit function parameters rather than type classes. All refactored definitions should follow this pattern for consistency.

### 5.2 FromHilbert.lean Parameterization

Each definition gets parameterized by the axioms it actually needs:

```lean
-- impI: needs K, S for deduction theorem
noncomputable def impI
    {Axioms : PL.Proposition Atom -> Prop}
    (h_K : forall phi psi, Axioms (phi.imp (psi.imp phi)))
    (h_S : forall phi psi chi, Axioms ((phi.imp (psi.imp chi)).imp ((phi.imp psi).imp (phi.imp chi))))
    {Gamma : List ...} {A B : ...}
    (d : DerivationTree Axioms (A :: Gamma) B) :
    DerivationTree Axioms Gamma (A.imp B) :=
  deductionTheorem h_K h_S Gamma A B d

-- impE: no axiom requirements (just modus ponens)
def impE
    {Axioms : PL.Proposition Atom -> Prop}
    {Gamma : List ...} {A B : ...}
    (d1 : DerivationTree Axioms Gamma (A.imp B))
    (d2 : DerivationTree Axioms Gamma A) :
    DerivationTree Axioms Gamma B :=
  DerivationTree.modus_ponens Gamma A B d1 d2

-- botE: needs EFQ axiom
def botE
    {Axioms : PL.Proposition Atom -> Prop}
    (h_EFQ : forall phi, Axioms (Proposition.bot.imp phi))
    {Gamma : List ...} {A : ...}
    (d : DerivationTree Axioms Gamma Proposition.bot) :
    DerivationTree Axioms Gamma A :=
  DerivationTree.modus_ponens Gamma Proposition.bot A
    (DerivationTree.weakening [] Gamma _
      (DerivationTree.ax [] _ (h_EFQ A))
      (fun _ h => nomatch h))
    d

-- assume: no axiom requirements
def assume
    {Axioms : PL.Proposition Atom -> Prop}
    {Gamma : List ...} {phi : ...}
    (h : phi in Gamma) : DerivationTree Axioms Gamma phi :=
  DerivationTree.assumption Gamma phi h

-- axiomRule: no axiom requirements (generic)
def axiomRule
    {Axioms : PL.Proposition Atom -> Prop}
    {Gamma : List ...} {phi : ...}
    (h : Axioms phi) : DerivationTree Axioms Gamma phi :=
  DerivationTree.ax Gamma phi h

-- hilbertCut: needs K, S for deduction theorem
noncomputable def hilbertCut
    {Axioms : PL.Proposition Atom -> Prop}
    (h_K : ...) (h_S : ...)
    {Gamma Delta : List ...} {A B : ...}
    (d1 : DerivationTree Axioms Gamma A)
    (d2 : DerivationTree Axioms (A :: Delta) B) :
    DerivationTree Axioms (Gamma ++ Delta) B := ...

-- hilbertWeakening: no axiom requirements
def hilbertWeakening
    {Axioms : PL.Proposition Atom -> Prop}
    {Gamma Delta : List ...} {phi : ...}
    (d : DerivationTree Axioms Gamma phi) (h : forall x in Gamma, x in Delta) :
    DerivationTree Axioms Delta phi :=
  DerivationTree.weakening Gamma Delta phi d h
```

#### subst_preserves_axiom

This function pattern-matches on all 4 `PropositionalAxiom` constructors. To parameterize, provide separate versions:

```lean
-- For IntPropAxiom
theorem subst_preserves_intAxiom
    {phi : PL.Proposition Atom} (h : IntPropAxiom phi)
    (f : Atom -> PL.Proposition Atom') : IntPropAxiom (phi.subst f) := by
  cases h with
  | implyK a b => exact .implyK (a.subst f) (b.subst f)
  | implyS a b c => exact .implyS (a.subst f) (b.subst f) (c.subst f)
  | efq a => exact .efq (a.subst f)

-- For MinPropAxiom
theorem subst_preserves_minAxiom
    {phi : PL.Proposition Atom} (h : MinPropAxiom phi)
    (f : Atom -> PL.Proposition Atom') : MinPropAxiom (phi.subst f) := by
  cases h with
  | implyK a b => exact .implyK (a.subst f) (b.subst f)
  | implyS a b c => exact .implyS (a.subst f) (b.subst f) (c.subst f)
```

Alternatively, define a generic approach: a typeclass `SubstClosed Axioms` that asserts substitution closure:

```lean
class SubstClosed (Axioms : PL.Proposition Atom -> Prop) where
  subst_preserves {phi} : Axioms phi -> forall (f : Atom -> PL.Proposition Atom'), Axioms (phi.subst f)
```

But this adds infrastructure. The simpler approach of separate proofs per axiom type is recommended.

### 5.3 HilbertDerivedRules.lean Split

Two options:

**Option A: Two sections in one file** (simpler)
```lean
/-! ## Intuitionistic Layer (K, S, EFQ) -/
section Intuitionistic
variable {Axioms : PL.Proposition Atom -> Prop}
variable (h_K : ...) (h_S : ...) (h_EFQ : ...)

def hilbertNegI ... := impI h_K h_S d
def hilbertNegE ... := impE d1 d2
-- etc.

end Intuitionistic

/-! ## Classical Layer (K, S, EFQ, Peirce) -/
section Classical
variable {Axioms : PL.Proposition Atom -> Prop}
variable (h_K : ...) (h_S : ...) (h_EFQ : ...) (h_Peirce : ...)

def hilbertDne ... := ...
def hilbertAndE1 ... := ...
-- etc.

end Classical
```

**Option B: Two files** (cleaner separation)
- `HilbertDerivedRules/Intuitionistic.lean`
- `HilbertDerivedRules/Classical.lean`

**Recommendation**: Option A (two sections in one file). The file is not large enough to warrant splitting into two files, and the dependency structure is clearer with everything in one place.

### 5.4 Equivalence.lean Parameterization

The key change: make `HilbertAxiomTheory` and the equivalence theorem generic.

```lean
-- Generic axiom theory
def AxiomTheory (Axioms : PL.Proposition Atom -> Prop) : Theory Atom :=
  { phi | Axioms phi }

-- Membership simp lemma
@[simp]
theorem mem_axiomTheory {Axioms : PL.Proposition Atom -> Prop} {phi : PL.Proposition Atom} :
    phi in AxiomTheory Axioms <-> Axioms phi := Iff.rfl

-- Backward-compat alias (optional, for transition)
abbrev HilbertAxiomTheory := AxiomTheory (@PropositionalAxiom Atom)

-- Generic Hilbert-to-ND translation
def hilbertToND
    {Axioms : PL.Proposition Atom -> Prop}
    {Gamma : List ...} {phi : ...} :
    DerivationTree Axioms Gamma phi ->
    Theory.Derivation (AxiomTheory Axioms) Gamma.toFinset phi
  | .ax _ _ h_ax => Theory.Derivation.ax (mem_axiomTheory.mpr h_ax)
  | .assumption _ _ h_mem => Theory.Derivation.ass (List.mem_toFinset.mpr h_mem)
  | .modus_ponens _ _ _ d1 d2 => Theory.Derivation.impE (hilbertToND d1) (hilbertToND d2)
  | .weakening _ _ _ d h_sub => Theory.Derivation.weakCtx (...) (hilbertToND d)

-- Generic ND-to-Hilbert translation (requires K, S for impI; EFQ for botE)
noncomputable def ndToHilbert
    {Axioms : PL.Proposition Atom -> Prop}
    (h_K : forall phi psi, Axioms (phi.imp (psi.imp phi)))
    (h_S : forall phi psi chi, Axioms (...))
    (h_EFQ : forall phi, Axioms (Proposition.bot.imp phi))
    {Gamma : Ctx Atom} {phi : ...} :
    Theory.Derivation (AxiomTheory Axioms) Gamma phi ->
    DerivationTree Axioms Gamma.toList phi
  | .ax h_mem => .ax Gamma.toList phi (mem_axiomTheory.mp h_mem)
  | .ass h_mem => .assumption Gamma.toList phi (Finset.mem_toList.mpr h_mem)
  | .impE d1 d2 => .modus_ponens ... (ndToHilbert h_K h_S h_EFQ d1) (ndToHilbert h_K h_S h_EFQ d2)
  | .botE d => botE h_EFQ (ndToHilbert h_K h_S h_EFQ d)
  | .impI d => by
      have ih := ndToHilbert h_K h_S h_EFQ d
      -- (use deductionTheorem with h_K, h_S, bridge lemmas)
      ...

-- Generic equivalence theorem
theorem hilbert_iff_nd
    {Axioms : PL.Proposition Atom -> Prop}
    (h_K : forall phi psi, Axioms (phi.imp (psi.imp phi)))
    (h_S : forall phi psi chi, Axioms (...))
    (h_EFQ : forall phi, Axioms (Proposition.bot.imp phi))
    {phi : PL.Proposition Atom} :
    Derivable Axioms phi <->
    DerivableIn (AxiomTheory Axioms) ((empty : Ctx Atom) turnstile phi)

-- Corollaries
theorem hilbert_iff_nd_int {phi : PL.Proposition Atom} :
    Derivable IntPropAxiom phi <->
    DerivableIn (AxiomTheory IntPropAxiom) ((empty : Ctx Atom) turnstile phi) :=
  hilbert_iff_nd (fun phi psi => .implyK phi psi) (fun phi psi chi => .implyS phi psi chi)
    (fun phi => .efq phi)

theorem hilbert_iff_nd_cl {phi : PL.Proposition Atom} :
    Derivable PropositionalAxiom phi <->
    DerivableIn (AxiomTheory PropositionalAxiom) ((empty : Ctx Atom) turnstile phi) :=
  hilbert_iff_nd (fun phi psi => .implyK phi psi) (fun phi psi chi => .implyS phi psi chi)
    (fun phi => .efq phi)
```

### 5.5 Important Design Decisions

**Why explicit parameters, not type classes?**

The existing `deductionTheorem` uses explicit `h_implyK`/`h_implyS` parameters. This is the established pattern in the codebase. Introducing new type classes (`HasMinAxioms`, etc.) would:
1. Add infrastructure not used elsewhere
2. Diverge from the existing codebase style
3. Create potential diamond issues with the abstract `HasAxiomImplyK`/etc. hierarchy

The explicit parameter approach is simpler and consistent.

**Why `AxiomTheory` instead of keeping `HilbertAxiomTheory`?**

`AxiomTheory Axioms := { phi | Axioms phi }` is the natural generic version. `HilbertAxiomTheory` can be kept as an abbreviation for `AxiomTheory PropositionalAxiom` for backward compatibility if desired, but no consumers exist.

**Why the equivalence requires K, S, AND EFQ (not just K, S)?**

The ND system has `botE` as a primitive. In the `ndToHilbert` translation, the `botE` case must be handled. The only way to derive `A` from `bot` in the Hilbert system is via the EFQ axiom (`bot -> A`). Without EFQ in the axiom set, `ndToHilbert` cannot translate `botE` cases. Therefore, the equivalence inherently requires EFQ.

This is not a limitation -- it is a faithful reflection of the fact that the ND system is inherently at least intuitionistic.

---

## 6. Backward-Compat Aliases to Remove

### Already Removed (stale docstring only)

The `Derivation.lean` docstring at line 28 still mentions:
```
Type aliases `ClDerivationTree`, `ClDeriv`, `ClDerivable`, and `clPropDerivationSystem`
instantiate the parameterized types at `PropositionalAxiom` for backward compatibility.
```

These aliases **no longer exist in the code** -- they were removed in a prior refactoring (task 113). Only the docstring reference remains and should be cleaned up.

### Aliases in This Task's Scope

After parameterization, the following become candidates for removal or deprecation:

1. **`HilbertAxiomTheory`** (Equivalence.lean): Replace with `AxiomTheory PropositionalAxiom` or keep as a convenience alias.

2. **FromHilbert.lean classical-specific definitions**: Once parameterized, the old signatures disappear. No explicit aliases exist -- the definitions themselves are being generalized in place.

3. **`subst_preserves_axiom`** (FromHilbert.lean): Currently pattern-matches on `PropositionalAxiom`. After providing `subst_preserves_intAxiom` and `subst_preserves_minAxiom`, the original can remain as `subst_preserves_axiom` for the classical case.

---

## 7. Dependency Confirmation

### Internal Dependencies (NaturalDeduction/)

```
Basic.lean          -- imports: Defs, InferenceSystem, Mathlib
DerivedRules.lean   -- imports: Basic
FromHilbert.lean    -- imports: DeductionTheorem (which imports Derivation, ListHelpers, DeductionHelpers)
HilbertDerivedRules -- imports: FromHilbert
Equivalence.lean    -- imports: Basic, FromHilbert
```

### External Consumers

**None.** A grep for `import.*NaturalDeduction` outside the directory returns zero results. These are pure leaf modules.

### What FromHilbert.lean Depends On

The critical external dependency is `DeductionTheorem.lean`, which provides:
- `deductionTheorem` -- already parameterized over `Axioms` with explicit `h_implyK`/`h_implyS`
- `deductionWithMem` -- also parameterized
- `prop_has_deduction_theorem` -- also parameterized
- `cl_prop_has_deduction_theorem` -- classical convenience wrapper

The `HasHilbertTree` global instance (line 55 of DeductionTheorem.lean) is fixed at `PropositionalAxiom`, but this is used only for the global instance, not by the parameterized `deductionTheorem` function. The parameterized function uses a local `letI` instance. Our refactored code should follow the same `letI` pattern.

---

## 8. Risks and Considerations

### 8.1 Minimal Risk

- **Leaf module status**: No downstream breakage is possible since nothing imports these files.
- **Established pattern**: The `deductionTheorem` parameterization pattern is battle-tested and can be directly followed.
- **No new infrastructure**: Using explicit parameters avoids adding type classes.

### 8.2 Moderate Considerations

1. **Parameter threading**: Each parameterized definition needs `h_K`, `h_S`, and/or `h_EFQ` parameters threaded through. The HilbertDerivedRules definitions call multiple FromHilbert functions, so parameters must be passed at each call site. This is mechanical but verbose.

2. **`noncomputable` propagation**: `impI` and `hilbertCut` are `noncomputable` because they use `deductionTheorem`. Any function that calls them inherits `noncomputable`. This is already the case and does not change.

3. **Universes**: The current files use `variable {Atom : Type*}` in most places. The `Axioms` parameter should match: `{Axioms : PL.Proposition Atom -> Prop}`.

4. **The `hilbertDne` proof structure**: The current `hilbertDne` uses `.peirce A Proposition.bot` and `.efq A` combined with S and K combinators. When parameterized, the explicit axiom parameters replace the dot-notation constructors: `h_Peirce A Proposition.bot` instead of `.peirce A Proposition.bot`.

### 8.3 Docstring Cleanup

The `Derivation.lean` docstring (lines 28-30) references backward-compat aliases that no longer exist. This should be corrected as part of this task:

```lean
-- Current (stale):
-- Type aliases `ClDerivationTree`, `ClDeriv`, `ClDerivable`, and `clPropDerivationSystem`
-- instantiate the parameterized types at `PropositionalAxiom` for backward compatibility.

-- Should become:
-- The `Deriv`, `Derivable`, and `propDerivationSystem` definitions are parameterized over
-- an arbitrary axiom predicate `Axioms`.
```

---

## 9. Recommended Implementation Order

1. **Phase 1: Parameterize FromHilbert.lean** -- Generalize all definitions over `Axioms` with explicit axiom parameters. Keep the `subst_preserves_axiom` for classical; add `subst_preserves_intAxiom` and `subst_preserves_minAxiom`.

2. **Phase 2: Split HilbertDerivedRules.lean** -- Two sections: intuitionistic (K, S, EFQ parameters) and classical (K, S, EFQ, Peirce parameters). Each rule calls the parameterized FromHilbert functions with the explicit axiom parameters.

3. **Phase 3: Parameterize Equivalence.lean** -- Define `AxiomTheory`, parameterize `hilbertToND` and `ndToHilbert`, prove the generic `hilbert_iff_nd`, add intuitionistic and classical corollaries.

4. **Phase 4: Cleanup** -- Fix the stale docstring in `Derivation.lean`. Verify with `lake build`.

---

## 10. Verification Criteria

After implementation, the following should hold:

1. `lake build` succeeds with zero errors and zero sorries.
2. `hilbert_iff_nd` works for both `IntPropAxiom` and `PropositionalAxiom` as corollaries.
3. All FromHilbert definitions accept any `Axioms` with the appropriate axiom parameters.
4. HilbertDerivedRules separates intuitionistic and classical rules with appropriate axiom constraints.
5. No backward-compat aliases remain (except optionally `HilbertAxiomTheory` as abbreviation).
6. No references to `PropositionalAxiom` constructors appear directly in the parameterized code (all accessed via explicit parameters).
