# Research Report: ND-Hilbert Equivalence (Task 87)

**Session**: sess_1781131486_ede82a
**Date**: 2026-06-10

## 1. Executive Summary

The codebase contains two completely unconnected propositional proof systems:

1. **Hilbert system** (`DerivationTree`): List-based contexts, 4 constructors (ax, assumption, modus_ponens, weakening), baked-in `PropositionalAxiom` schemata (K, S, EFQ, Peirce).
2. **Natural deduction** (`Theory.Derivation`): Finset-based contexts, 5 constructors (ax, ass, impI, impE, botE), parameterized over a `Theory T : Set (Proposition Atom)`.

A third file, `NaturalDeduction/FromHilbert.lean`, provides ND-flavored *wrappers* around the Hilbert `DerivationTree` (using the deduction theorem) but does NOT connect to the standalone ND system. The task is to formally bridge the two systems.

## 2. System Definitions

### 2.1 Hilbert System (`DerivationTree`)

**File**: `Cslib/Logics/Propositional/ProofSystem/Derivation.lean`

```lean
inductive DerivationTree : List (PL.Proposition Atom) → PL.Proposition Atom → Type _ where
  | ax (Γ : List ...) (φ : ...) (h : PropositionalAxiom φ) : DerivationTree Γ φ
  | assumption (Γ : ...) (φ : ...) (h : φ ∈ Γ) : DerivationTree Γ φ
  | modus_ponens (Γ : ...) (φ ψ : ...)
      (d₁ : DerivationTree Γ (φ.imp ψ)) (d₂ : DerivationTree Γ φ) : DerivationTree Γ ψ
  | weakening (Γ Δ : ...) (φ : ...) (d : DerivationTree Γ φ)
      (h : ∀ x ∈ Γ, x ∈ Δ) : DerivationTree Δ φ
```

**Axiom schemata** (`PropositionalAxiom`):
- `implyK`: `φ → (ψ → φ)`
- `implyS`: `(φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))`
- `efq`: `⊥ → φ`
- `peirce`: `((φ → ψ) → φ) → φ`

**Prop wrapper**: `Deriv Γ φ := Nonempty (DerivationTree Γ φ)`
**Empty-context derivability**: `Derivable φ := Deriv [] φ`

### 2.2 Natural Deduction (`Theory.Derivation`)

**File**: `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean`

```lean
inductive Theory.Derivation {T : Theory Atom} : Ctx Atom → Proposition Atom → Type u where
  | ax {Γ} {A} (_ : A ∈ T) : Derivation Γ A
  | ass {Γ} {A} (_ : A ∈ Γ) : Derivation Γ A
  | impI {A B} (Γ) : Derivation (insert A Γ) B → Derivation Γ (A → B)
  | impE {Γ} {A B} : Derivation Γ (A → B) → Derivation Γ A → Derivation Γ B
  | botE {Γ} {A} : Derivation Γ ⊥ → Derivation Γ A
```

where `Ctx Atom := Finset (Proposition Atom)` and `Theory Atom := Set (Proposition Atom)`.

**Inference system**: `T⇓(Γ ⊢ A)` = `T.Derivation Γ A`; `T⇓A` = `T.Derivation ∅ A`.
**Derivability**: `DerivableIn T (Γ ⊢ A)` = `Nonempty (T.Derivation Γ A)`.

### 2.3 ND Wrappers (`FromHilbert.lean`)

**File**: `Cslib/Logics/Propositional/NaturalDeduction/FromHilbert.lean`

This file provides ND-style names (`impI`, `impE`, `botE`, `assume`, `axiomRule`) as functions on `DerivationTree`, NOT on `Theory.Derivation`. It imports `Metalogic.DeductionTheorem` (the Hilbert side) and does NOT import `NaturalDeduction/Basic.lean`. These are purely syntactic wrappers, not a bridge.

## 3. Gap Analysis

### 3.1 What Needs to Be Proved

Two translation functions (at the `Type` level) or their `Prop`-level equivalents:

**Direction 1: ND to Hilbert**
```
ndToHilbert : T.Derivation Γ φ → DerivationTree (Γ.toList) φ
```
(with appropriate handling of the `T` parameter)

**Direction 2: Hilbert to ND**
```
hilbertToND : DerivationTree Γ φ → T.Derivation (Γ.toFinset) φ
```
(with appropriate theory `T` containing the Hilbert axioms)

**Or, extensional equivalence at Prop level:**
```
Derivable φ ↔ DerivableIn T (∅ ⊢ φ)
```
for the right choice of `T`.

### 3.2 Key Mismatches

| Dimension | Hilbert (`DerivationTree`) | ND (`Theory.Derivation`) |
|-----------|---------------------------|--------------------------|
| Context type | `List (Proposition Atom)` | `Finset (Proposition Atom)` |
| Axiom source | `PropositionalAxiom φ` (baked in) | `A ∈ T` (parameterized `Theory T`) |
| Classical reasoning | Peirce's law as axiom | Only in theory if `T` includes it |
| Implication intro | Not primitive (derived via deduction theorem) | Primitive constructor `impI` |
| Bottom elimination | EFQ axiom + MP | Primitive constructor `botE` |
| Weakening | Primitive constructor | Derived rule |
| Structural rules | Explicit (weakening constructor) | Implicit (Finset handles contraction/exchange) |

### 3.3 Theory Parameter Alignment

The Hilbert system bakes in axioms K, S, EFQ, and Peirce. The ND system is parameterized over an arbitrary `Theory T`. For equivalence, we need:

- **ND to Hilbert**: The theory `T` must be empty (`MPL`) or at least not assume anything beyond what the Hilbert axioms provide. With `T = MPL` (empty theory), ND derivation uses only structural rules (impI, impE, botE, ass), with no theory axioms. The Hilbert system has EFQ and Peirce baked in, but the ND system with `T = MPL` already has `botE` as a primitive (giving EFQ) but no classical reasoning.

- **Hilbert to ND**: We need a theory `T` that makes all `PropositionalAxiom` instances provable. Define:
  ```
  T_Hilbert := { φ | PropositionalAxiom φ }
  ```
  Then every Hilbert axiom `PropositionalAxiom φ` gives `φ ∈ T_Hilbert`, which provides `T_Hilbert.Derivation.ax`.

**Important observation**: The ND system with empty theory (`T = MPL`) is *intuitionistic* minimal logic plus EFQ (since `botE` is primitive). It does NOT include Peirce's law or DNE. Therefore:

- `Derivable φ` (Hilbert, with Peirce) is strictly stronger than `DerivableIn MPL (∅ ⊢ φ)` (ND minimal+EFQ)
- For full equivalence, we need `T` to include Peirce-like axioms, or we restrict to the common fragment

The cleanest approach is:
1. Define `HilbertAxiomTheory := { φ | PropositionalAxiom φ }` as the ND theory
2. Show `Derivable φ ↔ DerivableIn HilbertAxiomTheory (∅ ⊢ φ)`

### 3.4 Context Conversion

The `List ↔ Finset` mismatch is the main structural challenge.

**List to Finset**: `List.toFinset` (requires `DecidableEq`, which `Proposition Atom` has via `deriving DecidableEq`)
- Key lemma: `List.mem_toFinset : a ∈ l.toFinset ↔ a ∈ l` (in Mathlib)

**Finset to List**: `Finset.toList`
- Key lemma: `Finset.mem_toList : a ∈ s.toList ↔ a ∈ s` (in Mathlib)

The conversions preserve membership, which is the only property both systems care about. This means:

- For ND→Hilbert: given `Γ : Finset`, work with `Γ.toList : List`, and translate membership via `Finset.mem_toList`
- For Hilbert→ND: given `Γ : List`, work with `Γ.toFinset : Finset`, and translate membership via `List.mem_toFinset`

**Complication for impI**: The ND `impI` uses `insert A Γ` (Finset insert), while the Hilbert `deductionTheorem` uses `A :: Γ` (List cons). We need:
```
Finset.insert A Γ ↔ (A :: Γ.toList).toFinset  -- not exact, but membership-equivalent
```
Actually, `(insert A Γ).toList` and `A :: Γ.toList` are NOT the same list, but they have the same membership. Since `DerivationTree` has a `weakening` constructor that only cares about membership inclusion, this is manageable.

## 4. Recommended Approach

### 4.1 Primary Approach: Extensional Equivalence at Prop Level

Given the context mismatch, the cleanest first goal is **extensional equivalence for the empty context** (theorems, not contextual derivability):

```lean
def HilbertAxiomTheory : Theory Atom :=
  { φ | PropositionalAxiom φ }

theorem hilbert_iff_nd (φ : PL.Proposition Atom) :
    Derivable φ ↔ DerivableIn HilbertAxiomTheory (∅ ⊢ φ)
```

This sidesteps the `List/Finset` context issue entirely (both are empty).

**Direction 1: Hilbert → ND** (`Derivable φ → DerivableIn HilbertAxiomTheory (∅ ⊢ φ)`)

Induction on `DerivationTree [] φ`:
- `ax [] φ h_ax`: Use `Derivation.ax (show φ ∈ HilbertAxiomTheory from h_ax)`
- `assumption [] φ h_mem`: Impossible (`h_mem : φ ∈ []`)
- `modus_ponens`: Use `Derivation.impE` on IH results
- `weakening Γ' [] φ d h_sub`: Since `∀ x ∈ Γ', x ∈ []`, we have `Γ' = []` (effectively), so recurse

Actually the weakening case is more subtle since `Γ'` might be non-empty but subset of `[]` -- which forces `Γ'` to be empty. We would need:

```lean
have : Γ' = [] := List.eq_nil_of_forall_not_mem (fun x hx => List.not_mem_nil x (h_sub x hx))
```

Wait, `h_sub : ∀ x ∈ Γ', x ∈ []` implies `Γ' = []` only if we can show no element is in `[]`. Actually `∀ x ∈ Γ', x ∈ []` means `Γ'` must be empty, since nothing is in `[]`. So we can rewrite. But there's a subtlety: `DerivationTree` with `weakening` to the empty context means the sub-derivation `d` is from `Γ'` where all elements of `Γ'` are in `[]`, so `Γ'` is empty. The IH on `d : DerivationTree Γ' φ` with empty `Γ'` gives us what we need.

Actually this won't work directly by induction because the `DerivationTree` can have arbitrary internal contexts. We need to handle non-empty contexts internally. The cleaner approach:

**Define the translation for arbitrary contexts:**

```lean
def hilbertToND (Γ : List (Proposition Atom)) (φ : Proposition Atom)
    (d : DerivationTree Γ φ) : HilbertAxiomTheory.Derivation Γ.toFinset φ
```

by induction on `d`:
- `ax Γ φ h_ax`: `Derivation.ax h_ax` (since `PropositionalAxiom φ` implies `φ ∈ HilbertAxiomTheory`)
- `assumption Γ φ h_mem`: `Derivation.ass (List.mem_toFinset.mpr h_mem)`
- `modus_ponens Γ φ ψ d₁ d₂`: `Derivation.impE (hilbertToND _ _ d₁) (hilbertToND _ _ d₂)`
- `weakening Γ Δ φ d h_sub`:
  ```
  (hilbertToND Γ φ d).weakCtx (by
    intro x hx
    rw [List.mem_toFinset] at hx ⊢
    exact h_sub x hx)
  ```

This is actually straightforward!

**Direction 2: ND → Hilbert** (`DerivableIn HilbertAxiomTheory (∅ ⊢ φ) → Derivable φ`)

```lean
def ndToHilbert (Γ : Finset (Proposition Atom)) (φ : Proposition Atom)
    (d : HilbertAxiomTheory.Derivation Γ φ) : DerivationTree Γ.toList φ
```

by induction on `d`:
- `ax h_mem_T`: `h_mem_T : φ ∈ HilbertAxiomTheory` means `PropositionalAxiom φ`, so use `DerivationTree.ax _ _ h_mem_T`
- `ass h_mem_Γ`: `DerivationTree.assumption _ _ (Finset.mem_toList.mpr h_mem_Γ)`
- `impE d₁ d₂`: `DerivationTree.modus_ponens _ _ _ (ndToHilbert _ _ d₁) (ndToHilbert _ _ d₂)`
- `botE d`: Need `DerivationTree` for EFQ. Use `DerivationTree.ax _ _ (.efq φ)` and then MP with `ndToHilbert _ _ d`.
  ```
  DerivationTree.modus_ponens _ ⊥ φ
    (DerivationTree.ax _ _ (.efq φ))
    (ndToHilbert _ _ d)
  ```
  Wait, the `ax` constructor gives `DerivationTree Γ.toList (⊥.imp φ)` -- but we need to weaken it to the right context. Actually, `ax` takes *any* context, so `DerivationTree.ax Γ.toList _ (.efq φ)` gives us `DerivationTree Γ.toList (⊥ → φ)` directly.

- **`impI Γ d`**: This is the hard case. We have `d : Derivation (insert A Γ) B` and need `DerivationTree Γ.toList (A.imp B)`.
  By IH: `ndToHilbert (insert A Γ) B d : DerivationTree (insert A Γ).toList B`
  We need: `DerivationTree Γ.toList (A → B)`

  The key insight: `(insert A Γ).toList` is membership-equivalent to `A :: Γ.toList` (up to duplicates). We can use:
  1. Weaken the IH to `A :: Γ.toList`: since `∀ x ∈ (insert A Γ).toList, x ∈ A :: Γ.toList` (because `Finset.mem_toList` and `List.mem_cons` and `Finset.mem_insert`)
  2. Apply the deduction theorem: `deductionTheorem Γ.toList A B`

  This requires the already-proven `deductionTheorem` from the Hilbert side. This is noncomputable (due to Classical.propDecidable) but that's acceptable.

### 4.2 Implementation Structure

**New file**: `Cslib/Logics/Propositional/NaturalDeduction/Equivalence.lean`

```lean
import Cslib.Logics.Propositional.NaturalDeduction.Basic
import Cslib.Logics.Propositional.Metalogic.DeductionTheorem

-- The theory of Hilbert axiom instances
def HilbertAxiomTheory : Theory Atom :=
  { φ | PropositionalAxiom φ }

-- Direction 1: Hilbert → ND (computable)
def hilbertToND (Γ : List ...) (φ : ...) :
    DerivationTree Γ φ → HilbertAxiomTheory.Derivation Γ.toFinset φ

-- Direction 2: ND → Hilbert (noncomputable, uses deduction theorem)
noncomputable def ndToHilbert (Γ : Finset ...) (φ : ...) :
    HilbertAxiomTheory.Derivation Γ φ → DerivationTree Γ.toList φ

-- Extensional equivalence (empty context)
theorem hilbert_iff_nd (φ : Proposition Atom) :
    Derivable φ ↔ DerivableIn HilbertAxiomTheory (∅ ⊢ φ)
```

### 4.3 Key Technical Lemmas Needed

1. **Context membership bridges**:
   - `List.mem_toFinset` (Mathlib, already available)
   - `Finset.mem_toList` (Mathlib, already available)
   - `Finset.insert_toList_mem`: `∀ x ∈ (insert A Γ).toList, x ∈ A :: Γ.toList`
   - Converse: `∀ x ∈ A :: Γ.toList, x ∈ (insert A Γ).toList`

2. **Deduction theorem** (already proven):
   - `deductionTheorem : DerivationTree (A :: Γ) B → DerivationTree Γ (A.imp B)`
   - This is the key enabler for translating `impI` in the ND→Hilbert direction

3. **ND weakening** (already proven):
   - `Theory.Derivation.weakCtx : (hCtx : Γ ⊆ Δ) → T⇓(Γ ⊢ A) → T⇓(Δ ⊢ A)`
   - Needed for the Hilbert→ND `weakening` constructor case

4. **Empty context equivalences**:
   - `([] : List _).toFinset = (∅ : Finset _)` -- should be definitionally true or simp lemma
   - `(∅ : Finset _).toList = []` -- should be available

### 4.4 Estimated Complexity

| Component | Difficulty | Lines (est.) |
|-----------|-----------|-------------|
| `HilbertAxiomTheory` definition | Trivial | 5 |
| `hilbertToND` (Hilbert → ND) | Easy | 20-30 |
| `ndToHilbert` (ND → Hilbert) | Medium | 30-50 |
| Context membership lemmas | Easy-Medium | 15-25 |
| `hilbert_iff_nd` (top-level) | Easy (corollary) | 10 |
| **Total** | | ~80-120 |

The hardest part is the `impI` case of `ndToHilbert`, which requires:
1. IH gives `DerivationTree (insert A Γ).toList B`
2. Weaken to `DerivationTree (A :: Γ.toList) B`
3. Apply `deductionTheorem` to get `DerivationTree Γ.toList (A → B)`

Step 2 requires showing `(insert A Γ).toList ⊆ A :: Γ.toList` and `A :: Γ.toList ⊆ (insert A Γ).toList` (as membership predicates), then using `DerivationTree.weakening`.

## 5. Secondary Goal: Contextual Equivalence

After the empty-context equivalence, a natural follow-up is:

```lean
theorem hilbert_iff_nd_ctx (Γ_list : List ...) (Γ_finset : Finset ...) (φ : ...)
    (h_eq : ∀ x, x ∈ Γ_list ↔ x ∈ Γ_finset) :
    Deriv Γ_list φ ↔ DerivableIn HilbertAxiomTheory (Γ_finset ⊢ φ)
```

This would follow directly from `hilbertToND` and `ndToHilbert` with the membership equivalence.

## 6. Potential Blockers

1. **`insert` vs `cons` for `impI`**: The `impI` translation requires showing that `(Finset.insert A Γ).toList` and `A :: Γ.toList` have the same membership. This should be straightforward with `Finset.mem_toList` and `Finset.mem_insert`, but may require some finesse with `Finset.toList` ordering.

2. **Noncomputability**: The `deductionTheorem` is `noncomputable` (uses `Classical.propDecidable`), so `ndToHilbert` will also be `noncomputable`. This is acceptable since the goal is a logical equivalence, not a computable translation.

3. **DecidableEq requirement**: The ND system requires `[DecidableEq Atom]` (for Finset operations). The Hilbert system does not. The equivalence theorems will need `[DecidableEq Atom]`.

4. **Universe polymorphism**: The ND system uses `Type u`; the Hilbert system uses `Type*`. Need to ensure universe compatibility. Both are in universe `u` ultimately, so this should work.

## 7. Alternative Approaches (Considered and Rejected)

### 7.1 Direct mutual induction

Defining both translations simultaneously by mutual recursion. Rejected: unnecessary complexity, the translations are independent.

### 7.2 Via semantics (soundness + completeness)

Proving both systems sound and complete w.r.t. the same semantics, then concluding equivalence. Rejected: much more work, and completeness for the ND system is not yet proven. The direct syntactic translation is simpler.

### 7.3 Via the existing `InferenceSystem` typeclass

Both systems have `InferenceSystem` instances. However, they use different tag types (the ND system uses `T : Theory Atom` as the tag, while the Hilbert system uses `Propositional.HilbertCl`). Unifying through the typeclass would require showing that the two `InferenceSystem` instances agree, which is essentially the same as the direct translation.

## 8. Dependencies

- `Cslib.Logics.Propositional.NaturalDeduction.Basic` (ND system)
- `Cslib.Logics.Propositional.Metalogic.DeductionTheorem` (deduction theorem for Hilbert)
- `Mathlib.Data.Finset.Dedup` (for `Finset.mem_toList`, `List.mem_toFinset`)
- `Mathlib.Data.Finset.Insert` (already imported by ND Basic)

## 9. Recommended Plan Structure

**Phase 1**: Define `HilbertAxiomTheory`, prove context membership lemmas
**Phase 2**: Implement `hilbertToND` (easier direction)
**Phase 3**: Implement `ndToHilbert` (harder direction, needs deduction theorem)
**Phase 4**: Prove `hilbert_iff_nd` extensional equivalence
**Phase 5**: (Optional) Prove contextual equivalence `hilbert_iff_nd_ctx`
