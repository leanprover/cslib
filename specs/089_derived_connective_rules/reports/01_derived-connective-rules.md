# Research Report: Derived Intro/Elim Rules for Propositional Connectives

**Task**: 89 -- Add derived intro/elim rules for defined propositional connectives in both ND and Hilbert  
**Session**: sess_1781133896_bf151e  
**Date**: 2026-06-10

## 1. Lukasiewicz Encodings

The propositional connectives are defined as `abbrev` reductions in `Cslib/Logics/Propositional/Defs.lean`:

| Connective | Definition | Expanded Form |
|------------|-----------|---------------|
| `neg A` | `A.imp .bot` | `A -> bot` |
| `top` | `.imp .bot .bot` | `bot -> bot` |
| `or A B` | `.imp (.imp A .bot) B` | `(A -> bot) -> B` |
| `and A B` | `.imp (.imp A (.imp B .bot)) .bot` | `(A -> (B -> bot)) -> bot` |

**Note**: There is NO `Proposition.iff` defined in `Cslib/Logics/Propositional/Defs.lean`. The modal logic (`Cslib/Logics/Modal/Basic.lean`) defines `Proposition.iff` as `.and (.imp phi1 phi2) (.imp phi2 phi1)`, but the propositional module does not. If iff rules are desired for propositional logic, `Proposition.iff` must first be added to `Defs.lean`. The `Connectives.lean` foundation layer defines iff-like patterns only through the `LukasiewiczDerived` class (currently uninstantiated).

The Foundations-layer axioms file (`Cslib/Foundations/Logic/Axioms.lean`) provides polymorphic abbreviations `neg'`, `top'`, `conj'`, `disj'` that match these encodings via `HasBot`/`HasImp`.

## 2. Proof Systems Overview

### 2.1 Hilbert System (`DerivationTree`)

Located in `Cslib/Logics/Propositional/ProofSystem/Derivation.lean`.

- **Type**: `DerivationTree : List (PL.Proposition Atom) -> PL.Proposition Atom -> Type`
- **Prop wrapper**: `Deriv Gamma phi := Nonempty (DerivationTree Gamma phi)`
- **Constructors**: `ax`, `assumption`, `modus_ponens`, `weakening`
- **Axioms**: `ImplyK`, `ImplyS`, `EFQ`, `Peirce` (classical)

ND wrappers in `FromHilbert.lean` provide: `impI` (noncomputable, uses deduction theorem), `impE`, `botE`, `assume`, `axiomRule`, `hilbertCut` (noncomputable), `hilbertWeakening`, plus `Deriv`-level versions.

### 2.2 Standalone ND System (`Theory.Derivation`)

Located in `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean`.

- **Type**: `Theory.Derivation : Ctx Atom -> Proposition Atom -> Type u`
- **Context type**: `Ctx Atom = Finset (Proposition Atom)` (not List)
- **Constructors**: `ax` (from theory `T`), `ass` (from context), `impI` (insert into Finset), `impE`, `botE`
- **No classical axiom**: The ND system is parametric over theory `T`. Classical reasoning requires `T` to be `IsClassical`.

### 2.3 Foundations-Layer Generic System

Located in `Cslib/Foundations/Logic/Theorems/Propositional/`.

- **Core.lean**: `lce_imp`, `rce_imp`, `double_negation`, `raa`, `efq_neg`, `lem`, `rcp`, `dni`
- **Connectives.lean**: `iff_intro`, `contrapose_imp`, `contraposition`, `contrapose_iff`, De Morgan laws
- **Combinators.lean**: `imp_trans`, `identity`, `b_combinator`, `flip`, `app1`, `app2`, `pairing`, `dni`, `combine_imp_conj`

These are generic over `[PropositionalHilbert S]` and work at the `DerivableIn S` level. They use raw `HasImp.imp`/`HasBot.bot` encoding (no notation).

## 3. Existing Derived Rules

The following derived rules for connectives ALREADY EXIST in the Foundations layer:

| Rule | Location | What It Proves |
|------|----------|---------------|
| `lce_imp` | Core.lean | `(phi and psi) -> phi` (left conjunction elim) |
| `rce_imp` | Core.lean | `(phi and psi) -> psi` (right conjunction elim) |
| `pairing` | Combinators.lean | `phi -> psi -> (phi and psi)` (conjunction intro) |
| `iff_intro` | Connectives.lean | From `phi -> psi` and `psi -> phi`, derive `phi iff psi` |
| `double_negation` | Core.lean | `neg neg phi -> phi` (DNE) |
| `dni` | Combinators.lean | `phi -> neg neg phi` (DNI) |
| `lem` | Core.lean | `phi or neg phi` (LEM via identity on neg phi) |
| `raa` | Core.lean | `phi -> (neg phi -> psi)` |
| `efq_neg` | Core.lean | `neg phi -> (phi -> psi)` |

**What is MISSING**: These exist only at the generic `[PropositionalHilbert S]` level. They do NOT exist as:
1. Named rules on the Hilbert `DerivationTree` (like `impI`, `impE`, `botE` in `FromHilbert.lean`)
2. Named rules on the standalone ND `Theory.Derivation` (like `cut`, `weak` in `Basic.lean`)

## 4. Rules to Implement

### 4.1 Hilbert System (DerivationTree / Deriv) -- FromHilbert.lean

These wrap the Foundations-layer generic theorems to produce concrete `DerivationTree` and `Deriv` values. The pattern follows `impI`/`impE`/`botE` exactly.

#### Conjunction (and)

**andI**: From `Gamma |- A` and `Gamma |- B`, derive `Gamma |- A and B`.

Since `A and B = (A -> (B -> bot)) -> bot`, we need `Gamma |- (A -> (B -> bot)) -> bot`.

Proof sketch:
1. From `Gamma |- A` and `Gamma |- B`, we need `Gamma |- (A -> (B -> bot)) -> bot`
2. Assume `A -> (B -> bot)` in context: `A :: Gamma |- (A -> (B -> bot)) -> bot` ... but wait, the Hilbert system uses List context and `impI` is the deduction theorem.
3. Better approach: use `impI` to move A into context, apply `impE` twice.
   - From `Gamma |- A`, weaken to get `(A -> (B -> bot)) :: Gamma |- A`
   - From assumption: `(A -> (B -> bot)) :: Gamma |- A -> (B -> bot)`
   - By `impE`: `(A -> (B -> bot)) :: Gamma |- B -> bot`
   - From `Gamma |- B`, weaken to get `(A -> (B -> bot)) :: Gamma |- B`
   - By `impE`: `(A -> (B -> bot)) :: Gamma |- bot`
   - By `impI`: `Gamma |- (A -> (B -> bot)) -> bot`, i.e., `Gamma |- A and B`

**Computability**: **noncomputable** (uses `impI` which depends on the deduction theorem).

**andE1**: From `Gamma |- A and B`, derive `Gamma |- A`.

Since `A and B = (A -> (B -> bot)) -> bot = neg (A -> neg B)`, we need to extract A.

Proof sketch (using the Hilbert axioms directly):
1. Peirce's law with `psi = B -> bot`: `((A -> (B -> bot)) -> A) -> A`
2. `efq_neg` at `A -> (B -> bot)`: `neg(A -> (B -> bot)) -> ((A -> (B -> bot)) -> A)`
3. Compose: `neg(A -> (B -> bot)) -> A`, i.e., `(A and B) -> A`
4. Apply `impE` with the hypothesis.

Alternative: use the existing `lce_imp` from the Foundations layer, but we need to bridge from the generic `InferenceSystem.DerivableIn S` to the concrete `DerivationTree`. Since the Hilbert system has a `PropositionalHilbert` instance, the generic theorems should instantiate. The question is whether there IS a `PropositionalHilbert` instance for the propositional `DerivationTree`.

**Key question**: Is there a `PropositionalHilbert` instance for the propositional Hilbert system? Looking at `DeductionTheorem.lean`, there is a `HasHilbertTree` instance but not directly a `PropositionalHilbert` one. The `propDerivationSystem` in `Derivation.lean` provides a `Metalogic.DerivationSystem` instance. We need to check if there's a bridge.

If no `PropositionalHilbert` instance exists for the concrete system, the derived rules must be constructed manually from the `DerivationTree` constructors.

**Computability**: **computable** (does not use `impI` / deduction theorem).

**andE2**: From `Gamma |- A and B`, derive `Gamma |- B`. Same analysis as `andE1`.

**Computability**: **computable**.

#### Disjunction (or)

**orI1**: From `Gamma |- A`, derive `Gamma |- A or B` (i.e., `Gamma |- (A -> bot) -> B`).

Proof sketch:
1. Need `(A -> bot) :: Gamma |- B`
2. From `Gamma |- A`, weaken: `(A -> bot) :: Gamma |- A`
3. From assumption: `(A -> bot) :: Gamma |- A -> bot`
4. By `impE`: `(A -> bot) :: Gamma |- bot`
5. By `botE`: `(A -> bot) :: Gamma |- B`
6. By `impI`: `Gamma |- (A -> bot) -> B`

**Computability**: **noncomputable** (uses `impI`).

**orI2**: From `Gamma |- B`, derive `Gamma |- A or B` (i.e., `Gamma |- (A -> bot) -> B`).

Proof sketch:
1. K axiom: `B -> ((A -> bot) -> B)` -- this is exactly `ImplyK`!
2. Apply `impE` with the hypothesis.

**Computability**: **computable** (just ImplyK + modus ponens).

**orE**: From `Gamma |- A or B`, `A :: Gamma |- C`, and `B :: Gamma |- C`, derive `Gamma |- C`.

This is the most complex rule. Since `A or B = (A -> bot) -> B`:

Proof sketch:
1. From `A :: Gamma |- C`, by `impI`: `Gamma |- A -> C`
2. From `B :: Gamma |- C`, by `impI`: `Gamma |- B -> C`
3. We have `Gamma |- (A -> bot) -> B` and need `Gamma |- C`.
4. Compose `(A -> bot) -> B` with `B -> C` to get `(A -> bot) -> C`
5. Contrapose `A -> C` to get `neg C -> neg A`, i.e., `(C -> bot) -> (A -> bot)`
6. Compose to get `(C -> bot) -> C`
7. Apply Peirce's law (with psi = bot): `((C -> bot) -> C) -> C`
8. Done.

Alternative (cleaner): Use `classical_merge` from Connectives.lean.
- `A -> C` gives the first argument of classical_merge
- `(A -> bot) -> B` composed with `B -> C` gives `(A -> bot) -> C` = `neg A -> C`
- classical_merge: `(A -> C) -> ((neg A -> C) -> C)` -- this is exactly what we need!

**Computability**: **noncomputable** (uses `impI` twice in steps 1-2).

#### Negation (neg)

**negI**: From `A :: Gamma |- bot`, derive `Gamma |- neg A` (i.e., `Gamma |- A -> bot`).

This is literally `impI` with `B = bot`.

**Computability**: **noncomputable** (IS `impI`).

**negE**: From `Gamma |- neg A` and `Gamma |- A`, derive `Gamma |- bot`.

This is literally `impE` with `B = bot`.

**Computability**: **computable** (IS `impE`).

#### Double Negation Elimination (dne)

**dne**: From `Gamma |- neg neg A`, derive `Gamma |- A`.

Since `neg neg A = (A -> bot) -> bot`, and we have `double_negation : ((A -> bot) -> bot) -> A`:

Proof sketch:
1. Instantiate Peirce(A, bot): `((A -> bot) -> A) -> A`
2. Instantiate EFQ: `bot -> A`
3. B-combinator: compose EFQ with the hypothesis to get `(A -> bot) -> A`
4. Apply Peirce.

This requires building `DerivationTree` versions of these axiom uses. The Hilbert system has Peirce's law directly as an axiom (`PropositionalAxiom.peirce`).

**Computability**: **computable** (no `impI` needed; uses axioms + modus ponens + weakening).

#### Biconditional (iff)

**IMPORTANT**: `Proposition.iff` does NOT exist in `Cslib/Logics/Propositional/Defs.lean`. It must be added first:

```lean
abbrev Proposition.iff (A B : Proposition Atom) : Proposition Atom := (A.imp B).and (B.imp A)
```

Which expands to: `((A -> B) -> ((B -> A) -> bot)) -> bot`.

Once defined:

**iffI**: From `Gamma |- A -> B` and `Gamma |- B -> A`, derive `Gamma |- A iff B`.

This is `andI` applied to `A -> B` and `B -> A`.

**Computability**: **noncomputable** (uses `andI` which uses `impI`).

**iffE1**: From `Gamma |- A iff B`, derive `Gamma |- A -> B`.

This is `andE1` applied to `A -> B` and `B -> A`.

**Computability**: **computable**.

**iffE2**: From `Gamma |- A iff B`, derive `Gamma |- B -> A`.

This is `andE2` applied to `A -> B` and `B -> A`.

**Computability**: **computable**.

#### Top (top)

**topI**: Derive `Gamma |- top` (i.e., `Gamma |- bot -> bot`).

Proof sketch:
1. Axiom EFQ: `bot -> bot` -- wait, EFQ gives `bot -> phi` for any phi. With phi = bot, this is exactly `top`.
2. Weaken to any context Gamma.

Alternative: Use `ImplyK` with `phi = bot, psi = bot`: gives `bot -> (bot -> bot)` -- too strong.

Simplest: EFQ at bot gives `bot -> bot`. Then weaken from `[] |- bot -> bot` to `Gamma |- bot -> bot`.

**Computability**: **computable**.

### 4.2 Standalone ND System (Theory.Derivation) -- Basic.lean

These construct `Theory.Derivation` values using the `ax`, `ass`, `impI`, `impE`, `botE` constructors. The ND system uses `Finset` contexts with `insert` for `impI`.

#### Conjunction

**andI**: From `T-deriv(Gamma |- A)` and `T-deriv(Gamma |- B)`, derive `T-deriv(Gamma |- A and B)`.

Proof sketch:
1. Need `T-deriv(Gamma |- (A -> (B -> bot)) -> bot)`
2. By `impI Gamma`: suffices `T-deriv(insert (A -> (B -> bot)) Gamma |- bot)`
3. Have `T-deriv(insert (A -> (B -> bot)) Gamma |- A -> (B -> bot))` by `ass`
4. Weaken hypothesis: `T-deriv(insert (A -> (B -> bot)) Gamma |- A)` (weaken dA)
5. By `impE`: `T-deriv(insert (A -> (B -> bot)) Gamma |- B -> bot)`
6. Weaken hypothesis: `T-deriv(insert (A -> (B -> bot)) Gamma |- B)` (weaken dB)
7. By `impE`: `T-deriv(insert (A -> (B -> bot)) Gamma |- bot)`

**Note**: The ND system's `impI` is a primitive constructor, NOT the deduction theorem. So this is **computable** in the ND system!

**andE1**: From `T-deriv(Gamma |- A and B)`, derive `T-deriv(Gamma |- A)`.

Since `A and B = (A -> (B -> bot)) -> bot`:
1. We have `T-deriv(Gamma |- (A -> (B -> bot)) -> bot)`
2. Need `T-deriv(Gamma |- A)`
3. This requires classical reasoning (Peirce / DNE). The standalone ND system does NOT have Peirce as a primitive -- it depends on `T`.
4. If `T` is `IsClassical`, then `(neg neg A -> A) in T`, so we can use `ax`.
5. Alternatively, if `T` is `IsIntuitionistic`, we can use EFQ from the theory.

**Critical subtlety**: `andE1` requires `[IsClassical T]` in the ND system! Without classical logic, from `neg(A -> neg B)` we cannot extract `A` intuitionistically. This is because the Lukasiewicz encoding of conjunction is not intuitionistically valid for elimination.

Wait, let me reconsider. Actually, `neg(P) -> ((P) -> Q)` is intuitionistically valid (it's `botE` composed with `impE`). So:
1. We have `(A -> (B -> bot)) -> bot`
2. Suppose we want A. We need to use double negation elimination: `neg neg A -> A`.
3. Can we get `neg neg A` from `neg(A -> neg B)`? 
   - Suppose `neg A` (i.e., `A -> bot`). Then from `A -> bot` and `ImplyK`: `A -> (B -> bot)` (using the K axiom to weaken). But wait -- the ND system doesn't have ImplyK as an axiom. It only has `impI` and `impE`.
   - Actually in ND: assume `neg A`. Then assume `A`. From `neg A` and `A`, get `bot` by `impE`. From `bot`, get `B -> bot` by... hmm, we need `botE` or `impI + botE`.
   - Assume `neg A`. Assume `A`. Get `bot`. By `botE`, get any formula. In particular, get `B -> bot`... no, `botE` gives us any formula from `bot`, but we need to get back to `A -> (B -> bot)`.
   - Path: assume `neg A`. By `impI`, to show `A -> (B -> bot)`, assume `A`, assume `B`, from `neg A` and `A` get `bot`. So: `insert B (insert A (insert (neg A) Gamma)) |- bot` by `impE(ass(neg A), ass(A))`, then `impI` for B, `impI` for A. This gives `insert (neg A) Gamma |- A -> (B -> bot)`. 
   - Then `impE` with hypothesis: `insert (neg A) Gamma |- bot`.
   - Then `impI`: `Gamma |- neg A -> bot`, i.e., `Gamma |- neg neg A`.
   - Then DNE (requires `IsClassical T`): `Gamma |- A`.

So `andE1` in the ND system DOES require `[IsClassical T]` to use DNE.

But wait -- looking more carefully, this is the standard issue with Lukasiewicz conjunction. In intuitionistic logic with Lukasiewicz encoding, conjunction ELIMINATION is NOT valid. The encoding `neg(A -> neg B)` for `A and B` is only classically equivalent to standard conjunction. So all elimination rules for `and` require classical reasoning.

Actually, I should reconsider. Intuitionistic ND can still prove `neg(A -> neg B) -> A` using a slightly different route that involves only `botE` and `impI`. Let me think again...

In pure intuitionistic logic, from `neg(P -> Q)` we can derive `P` and `neg Q`:
- For `P`: Assume `neg P`. Then by `impI` over A, from `neg P` and A, get bot, get Q by `botE`. So `neg P |- P -> Q`. Then `neg(P -> Q)` and `P -> Q` give `bot`. So `neg P -> bot`, i.e., `neg neg P`. Then DNE... which requires classical!

OK so in fact, from `neg(A -> neg B)`, extracting `A` DOES require DNE (classical). The standard trick works in classical logic only.

However, the Hilbert system already has Peirce's law as a primitive axiom, making it classical. For the ND system, we'll need `[IsClassical T]`.

**andE2**: Same analysis. Requires `[IsClassical T]` for the ND system.

#### Disjunction

**orI1**: From `T-deriv(Gamma |- A)`, derive `T-deriv(Gamma |- A or B)`.

`A or B = (A -> bot) -> B`. Need `Gamma |- (A -> bot) -> B`.
1. `impI`: suffices `insert (A -> bot) Gamma |- B`
2. `ass`: `insert (A -> bot) Gamma |- A -> bot`
3. Weaken: `insert (A -> bot) Gamma |- A`
4. `impE`: `insert (A -> bot) Gamma |- bot`
5. `botE`: `insert (A -> bot) Gamma |- B`

Requires `[IsIntuitionistic T]` for `botE` (since `botE` is a constructor but semantically requires EFQ, which is always available as a constructor).

Wait -- looking at the ND system definition: `botE` IS a constructor of `Theory.Derivation`. It's available without any theory assumption! So `orI1` is available for ALL theories.

**Computability**: computable (in ND, `impI` is a constructor, not the deduction theorem).

**orI2**: From `T-deriv(Gamma |- B)`, derive `T-deriv(Gamma |- A or B)`.

`A or B = (A -> bot) -> B`. Need `Gamma |- (A -> bot) -> B`.
1. `impI`: suffices `insert (A -> bot) Gamma |- B`
2. Weaken: `insert (A -> bot) Gamma |- B`
Done.

**Computability**: computable.

**orE**: From `T-deriv(Gamma |- A or B)`, `T-deriv(insert A Gamma |- C)`, `T-deriv(insert B Gamma |- C)`, derive `T-deriv(Gamma |- C)`.

Proof sketch:
1. From `insert B Gamma |- C`, by `impI`: `Gamma |- B -> C`
2. From `Gamma |- (A -> bot) -> B` and `Gamma |- B -> C`, compose via `cut` or manual construction to get `Gamma |- (A -> bot) -> C`
3. From `insert A Gamma |- C`, by `impI`: `Gamma |- A -> C`
4. We have `Gamma |- A -> C` and `Gamma |- (A -> bot) -> C`
5. Need `Gamma |- C` from these two.
6. Use classical reasoning: Peirce(C, bot): `((C -> bot) -> C) -> C`
7. From `A -> C`, contrapose: `(C -> bot) -> (A -> bot)`. Then compose with `(A -> bot) -> C` to get `(C -> bot) -> C`. Apply Peirce to get C.

This requires classical reasoning (contraposition + Peirce). In the ND system, this means `[IsClassical T]`.

Alternatively, use the ND `cut` rule which is already available.

**Computability**: computable (in ND, all steps use constructors, no deduction theorem metatheorem).

But requires `[IsClassical T]` for DNE/Peirce.

#### Negation

**negI**: From `T-deriv(insert A Gamma |- bot)`, derive `T-deriv(Gamma |- neg A)`.

This is literally `impI Gamma` applied to `insert A Gamma |- bot`.

**Computability**: computable (constructor application).

**negE**: From `T-deriv(Gamma |- neg A)` and `T-deriv(Gamma |- A)`, derive `T-deriv(Gamma |- bot)`.

This is literally `impE`.

**Computability**: computable.

#### DNE

**dne**: From `T-deriv(Gamma |- neg neg A)`, derive `T-deriv(Gamma |- A)`.

Requires `[IsClassical T]`. Use `T.dne A` to get `neg neg A -> A` as a theory axiom, then `impE`.

**Computability**: computable.

#### Top

**topI**: Derive `T-deriv(Gamma |- top)`.

`top = bot -> bot`. By `impI`, suffices `insert bot Gamma |- bot`. By `ass`.

**Computability**: computable.

### 4.3 Foundations-Layer Generic Rules

Several rules already exist here (see Section 3). What's still needed:

| Rule | Status | Notes |
|------|--------|-------|
| `andI` (pairing) | EXISTS as `pairing` | `phi -> psi -> (phi and psi)` |
| `andE1` | EXISTS as `lce_imp` | `(phi and psi) -> phi` |
| `andE2` | EXISTS as `rce_imp` | `(phi and psi) -> psi` |
| `orI1` | MISSING | `phi -> phi or psi` |
| `orI2` | MISSING | `psi -> phi or psi` |
| `orE` (classical_merge) | EXISTS | `(phi -> chi) -> ((neg phi -> chi) -> chi)` |
| `negI` | trivial | Same as `impI` conceptually |
| `negE` | trivial | Same as `impE` conceptually |
| `dne` | EXISTS as `double_negation` | `neg neg phi -> phi` |
| `topI` | EXISTS as `derivationTop` / `identity` | `top` |
| `iffI` | EXISTS as `iff_intro` | From `phi -> psi` and `psi -> phi` |
| `iffE1` | PARTIALLY as `lce_imp` applied | Composition needed |
| `iffE2` | PARTIALLY as `rce_imp` applied | Composition needed |

Missing at this layer: `orI1`, `orI2` as standalone theorems, and clean `iffE1`/`iffE2` wrappers.

## 5. Computability Analysis

### 5.1 Hilbert System (`DerivationTree`)

| Rule | Computable? | Reason |
|------|-------------|--------|
| `andI` | NO | Uses `impI` (deduction theorem) |
| `andE1` | YES | Axioms + modus ponens only |
| `andE2` | YES | Axioms + modus ponens only |
| `orI1` | NO | Uses `impI` (deduction theorem) |
| `orI2` | YES | Just ImplyK + modus ponens |
| `orE` | NO | Uses `impI` twice |
| `negI` | NO | IS `impI` |
| `negE` | YES | IS `impE` |
| `dne` | YES | Peirce + EFQ + modus ponens + weakening |
| `iffI` | NO | Uses `andI` which uses `impI` |
| `iffE1` | YES | Uses `andE1` |
| `iffE2` | YES | Uses `andE2` |
| `topI` | YES | EFQ axiom + weakening |

**Pattern**: A rule is noncomputable iff it introduces an implication (needs the deduction theorem). Elimination rules are generally computable.

### 5.2 Standalone ND System (`Theory.Derivation`)

ALL rules are computable in the ND system because `impI` is a primitive constructor (not the deduction theorem). However, several rules require typeclass constraints:

| Rule | Constraint | Reason |
|------|-----------|--------|
| `andI` | none | `impI` + `impE` + `ass` + `weakCtx` |
| `andE1` | `[IsClassical T]` | Needs DNE to extract from Lukasiewicz encoding |
| `andE2` | `[IsClassical T]` | Same |
| `orI1` | none | `impI` + `impE` + `botE` + `ass` + `weakCtx` |
| `orI2` | none | `impI` + `weakCtx` |
| `orE` | `[IsClassical T]` | Needs Peirce / contraposition |
| `negI` | none | Literally `impI` |
| `negE` | none | Literally `impE` |
| `dne` | `[IsClassical T]` | Theory axiom `T.dne A` |
| `iffI` | none | Via `andI` |
| `iffE1` | `[IsClassical T]` | Via `andE1` |
| `iffE2` | `[IsClassical T]` | Via `andE2` |
| `topI` | none | `impI` + `ass` |

## 6. File Organization Recommendation

### Option A: Two New Files (Recommended)

**File 1**: `Cslib/Logics/Propositional/NaturalDeduction/DerivedRules.lean`
- All derived rules for the standalone ND system (`Theory.Derivation`)
- Imports `Basic.lean`
- Contains `andI`, `andE1`, `andE2`, `orI1`, `orI2`, `orE`, `negI`, `negE`, `dne`, `iffI`, `iffE1`, `iffE2`, `topI`

**File 2**: `Cslib/Logics/Propositional/NaturalDeduction/HilbertDerivedRules.lean`  
(or extend `FromHilbert.lean`)
- All derived rules for the Hilbert system (`DerivationTree` / `Deriv`)
- Imports `FromHilbert.lean`
- Contains the same set of rules

**Prerequisite**: Add `Proposition.iff` to `Defs.lean` (if iff rules are desired).

### Option B: Extend Existing Files

- Add ND rules directly to `Basic.lean`
- Add Hilbert rules directly to `FromHilbert.lean`

Option A is better for maintainability, as the existing files are already substantial.

### Foundations Layer

- Add `orI1`, `orI2` standalone theorems to `Core.lean` or `Connectives.lean`
- Add clean `iffE1`, `iffE2` wrappers to `Connectives.lean`

These may or may not be needed if the concrete system rules are built directly.

## 7. Key Challenges and Subtleties

### 7.1 Classical Requirement for Elimination Rules

The Lukasiewicz encoding `A and B = neg(A -> neg B)` is only classically equivalent to standard conjunction. The elimination rules `andE1` and `andE2` require double negation elimination, which is classical. This means:
- In the Hilbert system: no issue (Peirce's law is a primitive axiom)
- In the ND system: requires `[IsClassical T]` constraint
- Intuitionistic provers cannot use `andE1`/`andE2` for Lukasiewicz conjunction

### 7.2 `orE` Complexity

Disjunction elimination is the most complex rule. The standard proof uses:
1. Two applications of `impI` (one for each case)
2. Composition / cut
3. Classical reasoning (Peirce's law or `classical_merge`)

The existing `classical_merge` theorem at the Foundations layer provides the core pattern.

### 7.3 Missing `Proposition.iff`

The propositional `Defs.lean` does NOT define `iff`. The modal logic does. If iff rules are desired, add to `Defs.lean`:

```lean
/-- Biconditional as a derived connective: A <-> B := (A -> B) /\ (B -> A) -/
abbrev Proposition.iff (A B : Proposition Atom) : Proposition Atom := (A.imp B).and (B.imp A)
```

And add notation:

```lean
@[inherit_doc] scoped infix:30 " ↔ " => Proposition.iff
```

### 7.4 `PropositionalHilbert` Instance Gap

There may not be a `PropositionalHilbert` instance connecting the concrete `DerivationTree` to the generic Foundations-layer theorems. If one exists, the Hilbert system rules can simply delegate to the generic theorems. If not, one should be created, which would automatically provide access to all existing Foundations-layer theorems.

### 7.5 Pattern Consistency

The existing `FromHilbert.lean` uses the pattern:
- Type-level: `def ruleName : DerivationTree Gamma Conclusion := ...`
- Prop-level: `theorem ruleNameDeriv : Deriv Gamma Conclusion := ...`

New rules should follow this pattern, with `noncomputable` annotations where needed.

### 7.6 ND System Context Difference

The Hilbert system uses `List` contexts while the ND system uses `Finset` contexts. This means:
- Hilbert: weakening via `forall x in Gamma, x in Delta`
- ND: weakening via `Gamma <= Delta` (Finset subset)
- Hilbert `impI`: `A :: Gamma |- B` implies `Gamma |- A -> B`
- ND `impI`: `insert A Gamma |- B` implies `Gamma |- A -> B`

These are important for getting the proof terms right.

## 8. Implementation Priority

Recommended order:
1. **Add `Proposition.iff`** to `Defs.lean` (prerequisite for iff rules)
2. **ND system rules** (all computable, cleaner proofs) in a new `DerivedRules.lean`
3. **Hilbert system rules** (mix of computable/noncomputable) extending `FromHilbert.lean`
4. **Foundations-layer additions** (`orI1`, `orI2`, `iffE1`, `iffE2`) if generic versions are desired

## 9. Tactic Survey Results

Not applicable -- this is pure research; no proofs were attempted. The implementation phase should use `lean_multi_attempt` to test whether `simp`, `grind`, or `aesop` can close any of the proof goals automatically, given that many of these rules have fairly mechanical proofs from the existing combinators.
