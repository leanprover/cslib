# Research Report: Classical Propositional Soundness and Completeness

**Task**: 114 -- Define bivalent truth-value semantics and prove soundness and completeness for classical propositional logic (HilbertCl).
**Date**: 2026-06-10
**Status**: Research complete

## Executive Summary

Task 114 creates three new files implementing bivalent truth-value semantics, soundness, and completeness for classical propositional logic. The existing codebase provides all required infrastructure: `PL.Proposition` (atoms/bot/imp), `DerivationTree` (4 constructors, hardcoded to `PropositionalAxiom`), and comprehensive MCS properties (`prop_lindenbaum`, `prop_closed_under_derivation`, `prop_implication_property`, `prop_negation_complete`, `prop_mcs_bot_not_mem`, `prop_mcs_neg_of_not_mem`, `prop_mcs_mem_iff_neg_not_mem`). The propositional case is dramatically simpler than the modal case because: (1) no box constructor eliminates the entire box/accessibility apparatus, (2) the propositional `DerivationTree` is monomorphic (hardcoded to `PropositionalAxiom`), eliminating all explicit axiom hypothesis threading, (3) the MCS API is already specialized with `prop_*` wrappers that require no axiom callbacks.

## Literature Proof Structure

**Source**: CZ Chapter 5 Section 5.1 (Henkin construction), CZ Theorem 1.16 (soundness and completeness of Cl)

**Strategy**: Standard Henkin completeness via canonical model (MCS) construction, adapted to bivalent truth-value semantics for propositional logic.

### Step Map

1. Define bivalent valuation as `Atom -> Prop` -- CZ implicit in valuation definition
2. Define recursive evaluation of propositions under a valuation -- CZ Section 1.2 (truth tables)
3. Define tautology as truth under all valuations -- CZ Definition 1.5
4. Prove each axiom schema is a tautology (4 cases) -- CZ Theorem 1.16 (=>)
5. Prove soundness by induction on `DerivationTree` (4 cases) -- CZ Theorem 1.16 (=>)
6. Define canonical valuation from MCS: `v(p) = (atom p in S)` -- CZ Section 5.1 / Theorem 5.4
7. Prove truth lemma: `phi in S <-> Evaluate v phi` (3 cases: atom/bot/imp) -- CZ Theorem 5.4
8. Prove completeness: tautology implies derivable -- CZ Theorem 1.16 (<=), via contraposition

### Dependencies

- Steps 4-5 depend on Steps 1-3 (semantic definitions)
- Steps 6-8 depend on Steps 1-3 (semantic definitions) and MCS infrastructure (task 108)
- Step 8 depends on Step 7

### Potential Formalization Challenges

- **Step 4 (Peirce's law)**: Requires `Classical.byContradiction` or `Classical.em` -- straightforward
- **Step 7 (imp case, forward direction)**: Most complex case; must prove `phi -> psi in S` from `Evaluate v phi -> Evaluate v psi` via contraposition and MCS properties. This is the propositional simplification of KCompleteness.lean lines 192-244
- **Step 8**: The contraposition argument needs careful construction of `{neg phi}` as a consistent set, extending to MCS via Lindenbaum, then applying truth lemma -- follows k_completeness pattern (lines 269-323)

## Semantic Definitions Analysis

### Valuation Type

```lean
/-- A (bivalent) propositional valuation assigns a truth value to each atom. -/
abbrev Valuation (Atom : Type*) := Atom -> Prop
```

**Design decision**: Use `Atom -> Prop` rather than a structure. This matches the modal `Model.v : World -> Atom -> Prop` pattern (specialized to a single "world"). Using `abbrev` rather than `def` ensures definitional transparency for `simp` and `rfl` proofs.

### Evaluate Function

```lean
/-- Evaluate a proposition under a valuation. -/
def Evaluate (v : Valuation Atom) : PL.Proposition Atom -> Prop
  | .atom x => v x
  | .bot => False
  | .imp a b => Evaluate v a -> Evaluate v b
```

**Design decision**: This directly mirrors `Modal.Satisfies` (lines 98-103 of Basic.lean) but without the `box` case. The function is structurally recursive on `Proposition`, which Lean handles automatically.

**Key property**: `Evaluate v (.neg phi) = (Evaluate v phi -> False)` holds definitionally since `.neg phi = .imp phi .bot`.

### Tautology Definition

```lean
/-- A proposition is a tautology iff it is true under every valuation. -/
def Tautology (phi : PL.Proposition Atom) : Prop :=
  forall (v : Valuation Atom), Evaluate v phi
```

## Soundness Proof Structure

### prop_axiom_sound

Each of the 4 axiom schemata must be shown to be valid under all valuations. This directly follows the `k_axiom_sound` pattern (KSoundness.lean lines 41-60) but with 4 cases instead of 5:

```lean
theorem prop_axiom_sound {phi : PL.Proposition Atom}
    (h_ax : PropositionalAxiom phi) (v : Valuation Atom) :
    Evaluate v phi := by
  cases h_ax with
  | implyK phi psi => intro h_phi _; exact h_phi
  | implyS phi psi chi => intro h1 h2 h3; exact h1 h3 (h2 h3)
  | efq phi => intro h; exact absurd h id
  | peirce phi psi => intro h; by_contra h_not; exact h_not (h (fun h_phi => absurd h_phi h_not))
```

**Risk**: None. These are simple propositional reasoning steps. The Peirce case needs `Classical.byContradiction` (via `by_contra`), same as the modal case.

### prop_soundness

By structural recursion (match) on `DerivationTree`. 4 cases:

```lean
theorem prop_soundness
    {Gamma : List (PL.Proposition Atom)} {phi : PL.Proposition Atom}
    (d : DerivationTree Gamma phi)
    (v : Valuation Atom)
    (h_ctx : forall psi, psi in Gamma -> Evaluate v psi) :
    Evaluate v phi := by
  match d with
  | .ax _ psi h_ax => exact prop_axiom_sound h_ax v
  | .assumption _ psi h_mem => exact h_ctx psi h_mem
  | .modus_ponens _ psi chi d1 d2 =>
    exact prop_soundness d1 v h_ctx (prop_soundness d2 v h_ctx)
  | .weakening Gamma' Delta psi d' h_sub =>
    exact prop_soundness d' v (fun x hx => h_ctx x (h_sub x hx))
```

**Key simplification vs. modal**: No `.necessitation` case. The propositional `DerivationTree` has exactly 4 constructors.

### prop_soundness_derivable

Wrapper for the empty-context case:

```lean
theorem prop_soundness_derivable {phi : PL.Proposition Atom}
    (h : Derivable phi) (v : Valuation Atom) : Evaluate v phi
```

This follows `soundness_derivable` (Soundness.lean lines 110-117).

### Tautology-level wrapper

```lean
theorem soundness_tautology {phi : PL.Proposition Atom}
    (h : Derivable phi) : Tautology phi
```

## Completeness Proof Structure

### canonicalValuation

```lean
/-- The canonical valuation from a maximally consistent set. -/
def canonicalValuation (S : Set (PL.Proposition Atom)) : Valuation Atom :=
  fun p => Proposition.atom p in S
```

This is the propositional specialization of `CanonicalModel.v` (Completeness.lean line 60): `v := fun S p => Proposition.atom p in S.val`. Here we work with a single MCS `S` rather than a type of canonical worlds.

### prop_truth_lemma

The key lemma. For an MCS `S` and its canonical valuation `v`:

```lean
theorem prop_truth_lemma
    {S : Set (PL.Proposition Atom)} (h_mcs : PropSetMaximalConsistent S)
    (phi : PL.Proposition Atom) :
    Evaluate (canonicalValuation S) phi <-> phi in S
```

**Proof by structural recursion on `phi`** (3 cases, vs. 4 in the modal version):

**Case `.atom p`**: By definition, `Evaluate v (.atom p) = v p = (Proposition.atom p in S)`. Both directions are `id`.

**Case `.bot`**: 
- Forward: `Evaluate v .bot = False`, so the implication is vacuous.
- Backward: `bot in S` contradicts `prop_mcs_bot_not_mem h_mcs`.

**Case `.imp phi psi`**: This is the most complex case. There are two directions:

*Forward* (`Evaluate v (phi.imp psi) -> phi.imp psi in S`):
- By `prop_negation_complete h_mcs (phi.imp psi)`, either `phi.imp psi in S` (done) or `neg (phi.imp psi) in S`.
- If `neg (phi.imp psi) in S`, derive `phi in S` via:
  - From `neg (phi.imp psi) in S`, derive `phi` from `[(phi.imp psi).imp .bot]` using EFQ + Peirce (same derivation as KCompleteness.lean lines 198-217).
  - Then use `prop_closed_under_derivation` to get `phi in S`.
- By inductive hypothesis (backward), `Evaluate v phi`.
- By the assumption `Evaluate v (phi.imp psi)`, get `Evaluate v psi`.
- By inductive hypothesis (forward), `psi in S`.
- But also derive `neg psi in S` from `neg (phi.imp psi) in S` (using implyK to get `psi -> phi.imp psi`, then modus ponens with `neg (phi.imp psi)` -- same pattern as KCompleteness.lean lines 228-240).
- Apply `prop_implication_property` with `neg psi` and `psi` to get `bot in S`, contradicting `prop_mcs_bot_not_mem`.

*Backward* (`phi.imp psi in S -> Evaluate v phi -> Evaluate v psi`):
- Assume `phi.imp psi in S` and `Evaluate v phi`.
- By inductive hypothesis (forward), `phi in S`.
- By `prop_implication_property h_mcs h_mem h_phi_S`, `psi in S`.
- By inductive hypothesis (backward), `Evaluate v psi`.

**Critical simplification vs. KCompleteness**: No `.box` case at all. The modal truth lemma has a 4th case (`.box phi`) requiring the existence lemma (`k_mcs_box_witness`), accessibility relation construction, and canonical world infrastructure. All of this is absent in the propositional version.

**Another simplification**: The propositional MCS API (`prop_closed_under_derivation`, `prop_implication_property`, `prop_negation_complete`) takes NO explicit axiom hypothesis arguments. In the modal truth lemma (KCompleteness.lean line 168), every call to `modal_closed_under_derivation`, `modal_implication_property`, etc. requires threading `h_implyK`, `h_implyS` explicitly. This is eliminated entirely.

### prop_completeness

The main completeness theorem:

```lean
theorem prop_completeness (phi : PL.Proposition Atom)
    (h_taut : Tautology phi) : Derivable phi
```

**Proof by contraposition** (follows k_completeness, lines 269-323):

1. Assume `not (Derivable phi)`, i.e., `not (Deriv [] phi)`.
2. Show `{Proposition.neg phi}` is `PropSetConsistent`:
   - If not, some `L` with all elements in `{neg phi}` derives `bot`.
   - Weaken to `[neg phi] |- bot`.
   - Apply deduction theorem to get `[] |- neg phi -> bot`.
   - Build `[] |- phi` using EFQ + implyS + Peirce (same derivation chain as k_completeness lines 288-306, but using the propositional `DerivationTree` and `PropositionalAxiom` directly).
   - This contradicts `not (Derivable phi)`.
3. By `prop_lindenbaum`, extend `{neg phi}` to an MCS `M`.
4. `neg phi in M` (since `{neg phi} subset M`).
5. Let `v = canonicalValuation M`.
6. By `prop_truth_lemma` (backward), `Evaluate v (neg phi)`, i.e., `Evaluate v phi -> False`.
7. But `h_taut` gives `Evaluate v phi` -- contradiction.

**Key derivation in step 2**: The chain `[] |- neg phi -> bot` to `[] |- phi` is:
```
d_dne  : [] |- neg phi -> bot        (from deduction theorem)
efq_ax : [] |- bot -> phi            (from PropositionalAxiom.efq)
-- implyK: bot -> phi entails neg_phi -> (bot -> phi)
-- implyS: (neg_phi -> (bot -> phi)) -> ((neg_phi -> bot) -> (neg_phi -> phi))
-- MP chain: [] |- (neg_phi -> bot) -> (neg_phi -> phi)
-- MP with d_dne: [] |- neg_phi -> phi
-- Peirce: ((phi -> bot) -> phi) -> phi
-- MP: [] |- phi
```

This is identical to the k_completeness derivation (lines 288-306) but using `PropositionalAxiom.efq`, `.implyK`, `.implyS`, `.peirce` directly instead of passing axiom constructors as callbacks.

## How Modal K Completeness Simplifies

### Eliminated Concepts (not needed for propositional logic)

| Modal Concept | Lines in KCompleteness.lean | Propositional Equivalent |
|---------------|---------------------------|-------------------------|
| `CanonicalWorld` (subtype of MCS) | Completeness.lean 50-51 | Just `Set (PL.Proposition Atom)` with MCS hypothesis |
| `CanonicalModel` (worlds + accessibility + valuation) | Completeness.lean 57-61 | Just `canonicalValuation : Set -> Valuation` |
| Accessibility relation `R S T` | Completeness.lean 59 | Eliminated entirely |
| `k_mcs_box_witness` (existence lemma) | KCompleteness.lean 132-161 | Eliminated entirely |
| `k_derive_box_from_inconsistency` | KCompleteness.lean 51-124 | Eliminated entirely |
| `.box` case in truth lemma | KCompleteness.lean 249-261 | Eliminated entirely |
| `h_K` axiom hypothesis threading | Throughout | Eliminated entirely |
| Explicit axiom hypothesis threading (`h_implyK`, `h_implyS`, `h_efq`, `h_peirce`) | Throughout | Eliminated (propositional MCS API is monomorphic) |

### Preserved Structure

| Concept | Modal Location | Propositional Analog |
|---------|---------------|---------------------|
| `Satisfies` recursive definition | Basic.lean 98-103 | `Evaluate` (3 cases vs. 4) |
| Truth lemma `.atom` case | KCompleteness.lean 182-185 | Identical |
| Truth lemma `.bot` case | KCompleteness.lean 186-189 | Identical |
| Truth lemma `.imp` case | KCompleteness.lean 190-248 | Same structure, uses `prop_*` API |
| Completeness by contraposition | KCompleteness.lean 269-323 | Same structure, uses `prop_*` API |
| Consistency of `{neg phi}` | KCompleteness.lean 274-307 | Same derivation chain |
| Lindenbaum extension | KCompleteness.lean 308 | Uses `prop_lindenbaum` |

### Line Count Estimate

- KCompleteness.lean: ~160 lines (168-323 for truth lemma + completeness)
- Expected propositional completeness: ~80-100 lines (truth lemma + completeness)
- The elimination of the box case, existence lemma, and axiom hypothesis threading roughly halves the code.

## Per-File Specifications

### File 1: `Cslib/Logics/Propositional/Semantics/Basic.lean`

**Purpose**: Bivalent truth-value semantics for propositional logic.

**Import**: `Cslib.Logics.Propositional.Defs`

**Namespace**: `Cslib.Logic.PL`

**Definitions**:
1. `Valuation (Atom : Type*) := Atom -> Prop` (abbrev)
2. `Evaluate (v : Valuation Atom) : PL.Proposition Atom -> Prop` (recursive def, 3 cases)
3. `Tautology (phi : PL.Proposition Atom) : Prop := forall v, Evaluate v phi` (def)

**Optional helper lemmas** (useful for downstream proofs):
- `evaluate_neg : Evaluate v (.neg phi) <-> not (Evaluate v phi)`
- `evaluate_and : Evaluate v (.and phi psi) <-> Evaluate v phi /\ Evaluate v psi`
- `evaluate_or : Evaluate v (.or phi psi) <-> Evaluate v phi \/ Evaluate v psi`

These mirror `Satisfies.neg_iff`, `Satisfies.and_iff`, `Satisfies.or_iff` from Modal/Basic.lean.

**Estimated size**: ~40-60 lines

### File 2: `Cslib/Logics/Propositional/Metalogic/Soundness.lean`

**Purpose**: Soundness theorem for classical propositional logic.

**Import**: `Cslib.Logics.Propositional.Semantics.Basic` (for `Evaluate`, `Tautology`)
- This transitively imports `Defs.lean` and `Derivation.lean` via the Semantics import chain. Actually, `Semantics/Basic.lean` only imports `Defs.lean`. We also need `DerivationTree`, so we need to import `Cslib.Logics.Propositional.ProofSystem.Derivation` directly.

**Actual Imports**:
```lean
public import Cslib.Logics.Propositional.Semantics.Basic
public import Cslib.Logics.Propositional.ProofSystem.Derivation
```

**Namespace**: `Cslib.Logic.PL`

**Theorems**:
1. `prop_axiom_sound` -- 4-case match on `PropositionalAxiom` (K, S, EFQ, Peirce)
2. `prop_soundness` -- match on `DerivationTree` (4 cases: ax, assumption, modus_ponens, weakening)
3. `prop_soundness_derivable` -- wrapper for empty context
4. `soundness_tautology` -- `Derivable phi -> Tautology phi` wrapper

**Estimated size**: ~50-70 lines

### File 3: `Cslib/Logics/Propositional/Metalogic/Completeness.lean`

**Purpose**: Completeness theorem for classical propositional logic.

**Imports**:
```lean
public import Cslib.Logics.Propositional.Semantics.Basic
public import Cslib.Logics.Propositional.Metalogic.MCS
```

Note: `MCS.lean` already imports `DeductionTheorem.lean` which imports `Derivation.lean`, so we get the full proof system transitively.

**Namespace**: `Cslib.Logic.PL`

**Definitions and Theorems**:
1. `canonicalValuation (S : Set (PL.Proposition Atom)) : Valuation Atom` -- `fun p => .atom p in S`
2. `prop_truth_lemma` -- 3-case structural recursion (atom/bot/imp)
3. `prop_completeness` -- by contraposition: `Tautology phi -> Derivable phi`
4. `completeness_tautology` -- biconditional wrapper: `Tautology phi <-> Derivable phi`

**Estimated size**: ~100-130 lines

## Import Chain Analysis

```
Defs.lean
  |
  +-- Semantics/Basic.lean (NEW)  [Valuation, Evaluate, Tautology]
  |     |
  |     +-- Metalogic/Soundness.lean (NEW)  [prop_axiom_sound, prop_soundness]
  |     |     (also imports ProofSystem/Derivation.lean)
  |     |
  |     +-- Metalogic/Completeness.lean (NEW)  [canonicalValuation, prop_truth_lemma, prop_completeness]
  |           (also imports Metalogic/MCS.lean)
  |
  +-- ProofSystem/Axioms.lean
  |     |
  |     +-- ProofSystem/Derivation.lean  [DerivationTree, Deriv, Derivable, propDerivationSystem]
  |           |
  |           +-- ProofSystem/Instances.lean  [HilbertCl instances]
  |           |
  |           +-- Metalogic/DeductionTheorem.lean  [deductionTheorem, prop_has_deduction_theorem]
  |                 |
  |                 +-- Metalogic/MCS.lean  [prop_lindenbaum, prop_closed_under_derivation, ...]
```

**No circular imports**: `Semantics/Basic.lean` depends only on `Defs.lean`. `Soundness.lean` depends on `Semantics/Basic.lean` and `Derivation.lean`. `Completeness.lean` depends on `Semantics/Basic.lean` and `MCS.lean`.

**No conflicts**: The new files are in `Cslib/Logics/Propositional/` while modal soundness/completeness are in `Cslib/Logics/Modal/`. Names like `prop_soundness`, `prop_completeness`, `prop_truth_lemma` are prefixed with `prop_` to avoid any ambiguity, and they live in the `Cslib.Logic.PL` namespace (vs. `Cslib.Logic.Modal`).

## Risk Areas

### Low Risk

1. **Semantics/Basic.lean**: Purely definitional, no proof obligations. Straightforward.
2. **Soundness**: Direct pattern match, each case is a few lines. The modal version is a reliable template.
3. **Completeness `.atom` and `.bot` cases**: Trivial by definition / `prop_mcs_bot_not_mem`.

### Medium Risk

4. **Completeness `.imp` forward direction**: This is the most complex case (~30-40 lines). It requires:
   - Building explicit `DerivationTree` terms for EFQ + Peirce derivation (to extract `phi` from `neg (phi.imp psi) in S`)
   - Building explicit `DerivationTree` terms for `psi -> phi.imp psi` derivation (to derive `neg psi` from `neg (phi.imp psi) in S`)
   - Both derivations are already proven in KCompleteness.lean (lines 198-240) but using the modal `DerivationTree Axioms`. The propositional version uses `DerivationTree` (no `Axioms` parameter) with `PropositionalAxiom` hardcoded, so the syntax will differ slightly.
   - **Mitigation**: The derivation terms are structurally identical. The only change is removing the `Axioms` type parameter and using `PropositionalAxiom.efq` directly instead of `h_efq phi`.

5. **Completeness consistency argument**: The derivation chain showing `{neg phi}` is consistent (~20 lines). Same pattern as k_completeness but with `PropositionalAxiom.*` constructors.
   - **Mitigation**: Direct copy-adaptation from k_completeness lines 274-307.

### Potential Blockers

6. **`propDerivationSystem.Deriv` vs `Deriv`**: The MCS API uses `propDerivationSystem.Deriv` while `DerivationTree` proofs produce `Nonempty (DerivationTree ...)`. The completeness proof must bridge between these via `Deriv` (which is `Nonempty (DerivationTree ...)`). This is handled by wrapping `DerivationTree` terms with `Nonempty.intro` / angle brackets. The MCS file already demonstrates this pattern (e.g., `prop_mcs_bot_not_mem` at MCS.lean line 97-98).

7. **Universe polymorphism**: `Proposition` is universe-polymorphic (`Type u`). The `Valuation` type must match: `Valuation (Atom : Type u) := Atom -> Prop`. The `Tautology` quantification `forall (v : Valuation Atom)` should work at any universe since `Prop` is universe-polymorphic. No issues expected.

## Tactic Survey Results

The proofs in this task are primarily explicit term-mode or match-based, not tactic-heavy. Key tactics needed:

| Proof Step | Expected Tactics | Notes |
|-----------|-----------------|-------|
| `prop_axiom_sound` cases | `intro`, `exact`, `absurd`, `by_contra` | Same as k_axiom_sound |
| `prop_soundness` recursion | `match`, `exact` | Structural recursion, mostly term-mode |
| `prop_truth_lemma` atom/bot | `constructor`, `intro`, `exact`, `absurd` | Trivial cases |
| `prop_truth_lemma` imp | `constructor`, `intro`, `rcases`, `exfalso`, `apply`, `simp` | Complex case |
| `prop_completeness` | `by_contra`, `intro`, `have`, `obtain`, `exact` | Contraposition pattern |
| Derivation tree construction | Explicit term construction (`.ax`, `.modus_ponens`, `.weakening`) | No tactics for these |

`simp` may be useful for `List.mem_cons` simplifications in derivation tree assumptions. `omega` and `aesop` are unlikely to be needed.

## Summary of Answers to Research Questions

1. **Evaluate signature**: `Evaluate (v : Valuation Atom) : PL.Proposition Atom -> Prop` where `Valuation Atom := Atom -> Prop`. Use `abbrev` for `Valuation`.

2. **Soundness by induction on DerivationTree**: Match on 4 constructors (ax -> `prop_axiom_sound`, assumption -> context lookup, modus_ponens -> recursive calls, weakening -> recursive call with subset). No necessitation case.

3. **Canonical valuation construction**: `fun p => Proposition.atom p in S` where `S` is the MCS extending `{neg phi}`. Single `Set`, not a subtype like `CanonicalWorld`.

4. **Truth lemma key cases**: atom is definitional, bot uses `prop_mcs_bot_not_mem`, imp forward uses `prop_negation_complete` + `prop_closed_under_derivation` + explicit derivation trees + `prop_implication_property` to reach contradiction, imp backward uses `prop_implication_property` + recursive calls.

5. **How KCompleteness simplifies**: No box case, no accessibility relation, no canonical model structure, no existence lemma, no axiom hypothesis threading. Roughly halves the code.

6. **Name conflicts**: None. Propositional versions use `prop_` prefix and live in `Cslib.Logic.PL` namespace. Modal versions are in `Cslib.Logic.Modal`.

7. **Imports**: Semantics/Basic.lean imports Defs.lean. Soundness.lean imports Semantics/Basic.lean + Derivation.lean. Completeness.lean imports Semantics/Basic.lean + MCS.lean. No circular dependencies.
