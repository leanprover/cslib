# Research Report: Parameterize DerivationTree over Axiom Predicate

**Task**: 92 — Parameterize DerivationTree over an axiom predicate for modal cube expansion
**Date**: 2026-06-10
**Status**: Researched

---

## 1. Current Structure Map

### 1.1 ModalAxiom (DerivationTree.lean:55-79)

`ModalAxiom` is an inductive predicate `Proposition Atom -> Prop` with 8 constructors, bundling all S5 axioms in one type:

**Propositional (4)**:
- `implyK`: weakening `phi -> (psi -> phi)`
- `implyS`: distribution `(phi -> (psi -> chi)) -> ((phi -> psi) -> (phi -> chi))`
- `efq`: ex falso `bot -> phi`
- `peirce`: Peirce's law `((phi -> psi) -> phi) -> phi`

**Modal (4)**:
- `modalK`: K distribution `box(phi -> psi) -> (box phi -> box psi)`
- `modalT`: reflexivity `box phi -> phi`
- `modalFour`: transitivity `box phi -> box(box phi)`
- `modalB`: symmetry `phi -> box(diamond phi)`

### 1.2 DerivationTree (DerivationTree.lean:95-112)

```lean
inductive DerivationTree : List (Proposition Atom) -> Proposition Atom -> Type _ where
  | ax (Gamma) (phi) (h : ModalAxiom phi) : DerivationTree Gamma phi
  | assumption (Gamma) (phi) (h : phi in Gamma) : DerivationTree Gamma phi
  | modus_ponens (Gamma) (phi psi) (d1 : DT Gamma (phi.imp psi)) (d2 : DT Gamma phi) : DT Gamma psi
  | necessitation (phi) (d : DT [] phi) : DT [] (Proposition.box phi)
  | weakening (Gamma Delta) (phi) (d : DT Gamma phi) (h : forall x in Gamma, x in Delta) : DT Delta phi
```

Key observation: The `ax` constructor takes `(h : ModalAxiom phi)`, hardcoding the S5 axiom set. **This is the single point that needs parameterization.**

### 1.3 Derived Definitions (DerivationTree.lean:121-186)

- `DerivationTree.height`: Computable Nat-valued height, pattern matches on all 5 constructors
- Height ordering theorems: `height_modus_ponens_left`, `height_modus_ponens_right`, `height_weakening`
- `Deriv Gamma phi := Nonempty (DerivationTree Gamma phi)` -- Prop wrapper
- `Derivable phi := Deriv [] phi` -- empty-context derivability
- `mp_deriv`, `weakening_deriv`, `assumption_deriv` -- combinators
- `modalDerivationSystem : Metalogic.DerivationSystem (Proposition Atom)` -- connects to generic MCS

### 1.4 HasHilbertTree Instance (DeductionTheorem.lean:57-63)

```lean
noncomputable instance : HasHilbertTree (Proposition Atom) where
  Tree := fun Gamma phi => DerivationTree Gamma phi
  implyK := fun phi psi => .ax [] _ (.implyK phi psi)
  implyS := fun phi psi chi => .ax [] _ (.implyS phi psi chi)
  assumption := fun h => .assumption _ _ h
  mp := fun d1 d2 => .modus_ponens _ _ _ d1 d2
  weakening := fun d h => .weakening _ _ _ d h
```

This instance references `ModalAxiom.implyK` and `ModalAxiom.implyS` directly. After parameterization, these must come from whatever axiom predicate is passed, requiring a mechanism to ensure the axiom predicate includes at least the propositional axioms.

---

## 2. Typeclass Hierarchy (ProofSystem.lean)

### 2.1 Existing Hierarchy

```
MinimalHilbert (K, S, MP)
  |
IntuitionisticHilbert (+EFQ)
  |
ClassicalHilbert (+Peirce)
  |
ModalHilbert (+Necessitation, +AxiomK)
  |
ModalS5Hilbert (+T, +4, +B)
  |
BimodalTMHilbert (+TemporalBXHilbert, +MF)
```

Individual axiom typeclasses: `HasAxiomK`, `HasAxiomT`, `HasAxiom4`, `HasAxiomB`, `HasAxiom5`, `HasAxiomD`.

### 2.2 Tag Types (ProofSystem.lean:349-369)

Already defined:
- `Modal.HilbertK : Type := Empty` (opaque)
- `Modal.HilbertS5 : Type := Empty` (opaque)

Missing (need to add):
- `Modal.HilbertT`
- `Modal.HilbertD`
- `Modal.HilbertS4`

### 2.3 Missing Bundled Classes

The task requires adding:
- `ModalTHilbert` (K + T)
- `ModalDHilbert` (K + D)
- `ModalS4Hilbert` (K + T + 4)

And refactoring `ModalS5Hilbert` to extend `ModalS4Hilbert` + `HasAxiomB`.

---

## 3. Template: Temporal Logic Parameterization Pattern

The Temporal logic provides the best template for how to parameterize a derivation tree.

### Temporal Pattern

```lean
-- FrameClass is an enumeration used to gate which axioms are available
inductive FrameClass where | Base | Dense | Discrete

-- Each axiom constructor has a minFrameClass field
inductive Axiom : Formula Atom -> Type u where
  | imp_k (phi psi chi) : Axiom (...)
  ...

-- DerivationTree is parameterized by FrameClass
inductive DerivationTree (fc : FrameClass) : Context Atom -> Formula Atom -> Type u where
  | axiom (Gamma) (phi) (h : Axiom phi) (h_fc : h.minFrameClass <= fc) : DT fc Gamma phi
  ...
```

### Why Not Frame Classes for Modal?

The temporal pattern uses a *partial order* on frame classes with `<=` gating. For modal logic, the "modal cube" has 15 logics in a lattice that doesn't decompose into a simple linear order or even a clean partial order on frame classes. Instead, the task description recommends a simpler predicate-based approach: parameterize over `Axioms : Proposition Atom -> Prop`.

---

## 4. Recommended Parameterization Design

### 4.1 Per-System Axiom Predicates

Define propositional axioms shared by all systems, then per-system modal axiom predicates:

```lean
-- Propositional axioms (shared by ALL normal modal logics)
inductive PropAxiom : Proposition Atom -> Prop where
  | implyK (phi psi) : PropAxiom (phi.imp (psi.imp phi))
  | implyS (phi psi chi) : PropAxiom (...)
  | efq (phi) : PropAxiom (Proposition.bot.imp phi)
  | peirce (phi psi) : PropAxiom (...)

-- K-level modal axiom (just distribution)
inductive AxiomK : Proposition Atom -> Prop where
  | modalK (phi psi) : AxiomK (...)

-- Per-system predicates combine what they need
def AxiomT (phi : Proposition Atom) : Prop := AxiomK phi \/ ModalT phi
  -- where ModalT is the T schema: box phi -> phi

-- Or more cleanly, define each as a separate inductive:
inductive ModalTAxiom : Proposition Atom -> Prop where
  | modalT (phi) : ModalTAxiom ((Proposition.box phi).imp phi)

inductive ModalFourAxiom : Proposition Atom -> Prop where
  | modalFour (phi) : ModalFourAxiom ((Proposition.box phi).imp (Proposition.box (Proposition.box phi)))

inductive ModalBAxiom : Proposition Atom -> Prop where
  | modalB (phi) : ModalBAxiom (phi.imp (Proposition.box (Proposition.diamond phi)))

inductive ModalDAxiom : Proposition Atom -> Prop where
  | modalD (phi) : ModalDAxiom ((Proposition.box phi).imp (Proposition.diamond phi))
```

### 4.2 Parameterized DerivationTree

```lean
inductive DerivationTree (Axioms : Proposition Atom -> Prop) :
    List (Proposition Atom) -> Proposition Atom -> Type _ where
  | ax (Gamma) (phi) (h : Axioms phi) : DerivationTree Axioms Gamma phi
  | assumption ... | modus_ponens ... | necessitation ... | weakening ...
```

### 4.3 System-Specific Axiom Bundles

```lean
-- The S5 axiom set (backward-compatible alias)
def S5Axiom : Proposition Atom -> Prop :=
  fun phi => PropAxiom phi \/ AxiomK phi \/ ModalTAxiom phi \/ ModalFourAxiom phi \/ ModalBAxiom phi

-- Existing ModalAxiom becomes an alias
abbrev ModalAxiom := @S5Axiom  -- or just rename/alias for backward compat
```

### 4.4 Alternative: Single Axiom Inductive with Filter

A cleaner approach (matching the task description more closely):

```lean
-- Keep existing ModalAxiom as-is (it becomes the S5 axiom set)
-- Define per-system axiom predicates as subsets
def KAxioms (phi : Proposition Atom) : Prop :=
  exists h : ModalAxiom phi, match h with
  | .implyK .. | .implyS .. | .efq .. | .peirce .. | .modalK .. => True
  | _ => False

-- Or define separate small inductives per system
inductive AxiomSetK : Proposition Atom -> Prop where
  | implyK ... | implyS ... | efq ... | peirce ... | modalK ...
```

**Recommendation**: Use separate inductive types per modal axiom, with a `PropAxiom` base and a disjunction-based combinator. This is the cleanest approach that scales to the full modal cube.

### 4.5 Necessary Constraint: PropAxiom Inclusion

The deduction theorem requires `implyK` and `implyS`. The `HasHilbertTree` instance needs these. Therefore any `Axioms` parameter must include at least the propositional axioms. Two approaches:

**Option A: Typeclass constraint**
```lean
class HasPropAxioms (Axioms : Proposition Atom -> Prop) where
  implyK : forall phi psi, Axioms (phi.imp (psi.imp phi))
  implyS : forall phi psi chi, Axioms (...)
  efq : ...
  peirce : ...
```

**Option B: Structural inclusion**
```lean
def NormalModalAxioms (ModalSpecific : Proposition Atom -> Prop) : Proposition Atom -> Prop :=
  fun phi => PropAxiom phi \/ AxiomK phi \/ ModalSpecific phi
```

**Recommendation**: Option B is simpler and composes well. Every normal modal logic includes propositional axioms + K + necessitation. The `ModalSpecific` part varies per system.

---

## 5. File-by-File Impact Analysis

### 5.1 DerivationTree.lean (HIGH impact)

- `ModalAxiom`: Keep as `S5Axiom` alias or refactor into components
- `DerivationTree`: Add `Axioms` parameter
- `height`: Trivially adapts (never inspects axiom payload)
- Height theorems: Trivially adapt
- `Deriv`, `Derivable`: Add `Axioms` parameter
- `mp_deriv`, `weakening_deriv`, `assumption_deriv`: Add `Axioms` parameter
- `modalDerivationSystem`: Parameterize, possibly create `modalDerivationSystem (Axioms)` function

### 5.2 DeductionTheorem.lean (MEDIUM impact -- mechanical)

The deduction theorem **never inspects axiom payload**. The `ax` case just wraps it with `deductionAxiom`, which uses `implyK`. All that matters is that `Axioms` includes `implyK` and `implyS`.

- `HasHilbertTree` instance: Parameterize by `Axioms`, require `HasPropAxioms` or use structural approach
- `deductionWithMem`: Add `Axioms` parameter (no logic changes)
- `deductionTheorem`: Add `Axioms` parameter (no logic changes)
- `modal_has_deduction_theorem`: Parameterize

The task description correctly notes this is "mechanical, DT never inspects axiom payload."

### 5.3 MCS.lean (MEDIUM-HIGH impact)

**Generic lemmas** (parameterize mechanically):
- `Modal.SetConsistent`, `Modal.SetMaximalConsistent`: Parameterize
- `modal_lindenbaum`: Parameterize
- `modal_closed_under_derivation`: Parameterize
- `modal_implication_property`: Parameterize
- `modal_negation_complete`: Parameterize
- `mcs_mp_axiom`: Parameterize (takes any `h_ax : Axioms (phi.imp psi)`)
- `mcs_bot_not_mem`: Generic (uses `assumption` only)

**S5-specific lemmas** (require explicit axiom assumptions):
- `mcs_box_closure` (line 110-113): Uses `ModalAxiom.modalT` -- needs `AxiomT`-assumption
- `mcs_box_box` (line 116-119): Uses `ModalAxiom.modalFour` -- needs `Axiom4`-assumption
- `mcs_box_diamond` (line 123-127): Uses `ModalAxiom.modalB` -- needs `AxiomB`-assumption
- `mcs_box_mp` (line 130-135): Uses `ModalAxiom.modalK` -- needs `AxiomK`-assumption (generic to all normal modal logics)
- `mcs_neg_of_not_mem` (line 140-145): Generic
- `mcs_not_mem_of_neg` (line 148-152): Generic
- `mcs_mem_iff_neg_not_mem` (line 155-162): Generic
- `iteratedDeduction` (line 169-190): Uses `mcs_box_mp` which needs K -- generic for normal modal logics
- `derive_box_from_box_context` (line 197-211): Uses `iteratedDeduction` -- generic for normal modal logics
- `derive_box_from_inconsistency` (line 223-289): Uses `mcs_box_closure` (T-specific) -- S5-specific
- `mcs_box_witness` (line 300-322): Uses `derive_box_from_inconsistency` and `mcs_not_mem_of_neg` -- S5-specific

**Summary of MCS decomposition**:
- Generic (all normal modal logics): lindenbaum, closed_under_derivation, implication_property, negation_complete, mcs_bot_not_mem, mcs_neg_of_not_mem, mcs_not_mem_of_neg, mcs_mem_iff_neg_not_mem, mcs_box_mp, iteratedDeduction, derive_box_from_box_context
- T-dependent: mcs_box_closure
- 4-dependent: mcs_box_box
- B-dependent: mcs_box_diamond
- S5-dependent (uses T): derive_box_from_inconsistency, mcs_box_witness

### 5.4 Soundness.lean (MEDIUM impact)

- `axiom_sound`: Currently pattern-matches on all 8 `ModalAxiom` constructors. Needs to be parameterized: the soundness proof strategy depends on which axioms are in the set and which frame conditions are assumed.
- `soundness`: Parameterize `DerivationTree` type. The `ax` case dispatches to `axiom_sound`.
- `soundness_derivable`: Parameterize.

For different modal systems, soundness requires different frame conditions (reflexive for T, transitive for 4, serial for D, etc.). The soundness theorem will need either:
- A generic `axiom_sound` that takes a proof each axiom in `Axioms` is valid under the given frame conditions, OR
- Per-system soundness theorems

### 5.5 Completeness.lean (MEDIUM-HIGH impact)

The completeness proof is deeply S5-specific:
- `CanonicalWorld`: Parameterize by `Axioms`
- `CanonicalModel`: Parameterize
- `canonical_refl`: Uses `mcs_box_closure` (T)
- `canonical_trans`: Uses `mcs_box_box` (4)
- `canonical_eucl`: Uses `mcs_box_box` (4), `mcs_neg_of_not_mem`, `mcs_box_diamond` (B)
- `truth_lemma`: Uses `mcs_box_witness` (S5-specific) and various MCS properties
- `completeness`: Uses everything

**Recommendation**: Keep the completeness proof S5-specific for now (it's the most complex part). Parameterize the infrastructure (DerivationTree, DT, MCS basics) first. Per-system completeness proofs are a separate task.

### 5.6 ProofSystem.lean (MEDIUM impact)

- Add `ModalTHilbert`, `ModalDHilbert`, `ModalS4Hilbert` bundled classes
- Refactor `ModalS5Hilbert` to extend `ModalS4Hilbert` with `HasAxiomB`
- Add tag types: `Modal.HilbertT`, `Modal.HilbertD`, `Modal.HilbertS4`

### 5.7 Other Files (LOW impact)

- `Cslib/Logics/Modal/Basic.lean`: No changes (defines semantics, independent of proof system)
- `Cslib/Logics/Modal/Cube.lean`: No changes (defines semantic logics)
- `Cslib/Logics/Modal/Denotation.lean`: No changes
- `Cslib/Logics/Modal/FromPropositional.lean`: No changes
- `Cslib.lean` (root module): No changes (just imports)
- Bimodal: Independent (uses its own formula type and derivation system)
- Temporal: Independent

---

## 6. Complete Reference List of Affected Definitions

### Direct references to `ModalAxiom` (grep results):

| File | Line | Usage |
|------|------|-------|
| DerivationTree.lean | 55 | Definition of `ModalAxiom` |
| DerivationTree.lean | 98 | `ax` constructor takes `ModalAxiom phi` |
| MCS.lean | 91 | `mcs_mp_axiom` takes `ModalAxiom (phi.imp psi)` |
| Soundness.lean | 51 | `axiom_sound` takes `ModalAxiom phi` |

### Direct references to `DerivationTree` (within Modal):

| File | Lines | Definitions |
|------|-------|-------------|
| DerivationTree.lean | 95-145 | Definition + height |
| DeductionTheorem.lean | 57-63 | `HasHilbertTree` instance |
| DeductionTheorem.lean | 72-108 | `deductionWithMem` |
| DeductionTheorem.lean | 128-176 | `deductionTheorem` |
| MCS.lean | 88-97 | `mcs_mp_axiom` builds derivation trees |
| MCS.lean | 100-107 | `mcs_bot_not_mem` builds derivation tree |
| MCS.lean | 169-211 | `iteratedDeduction`, `derive_box_from_box_context` |
| MCS.lean | 223-289 | `derive_box_from_inconsistency` |
| Soundness.lean | 103-125 | `soundness` recurses on DT |
| Completeness.lean | 115-255 | Multiple places build derivation trees directly |

### References to `modalDerivationSystem`:

| File | Line | Usage |
|------|------|-------|
| MCS.lean | 50, 54 | `SetConsistent`, `SetMaximalConsistent` abbrevs |
| MCS.lean | 62, 68, 70, 77, 84, 94, 106 | Various lemma proofs |
| Completeness.lean | 167, 186 | Truth lemma proof |
| DeductionTheorem.lean | 185, 187 | `modal_has_deduction_theorem` |

---

## 7. Backward Compatibility Strategy

### 7.1 Type Alias Approach

```lean
-- After parameterization, create backward-compat aliases:
abbrev S5DerivationTree := DerivationTree S5Axioms
abbrev S5Deriv := Deriv S5Axioms
abbrev S5Derivable := Derivable S5Axioms
def modalDerivationSystem := derivationSystem S5Axioms
```

### 7.2 Namespace Strategy

Keep existing names in `Cslib.Logic.Modal` namespace. The parameterized versions can live alongside:
- `DerivationTree Axioms Gamma phi` (new, general)
- Legacy names point to S5 instantiation

### 7.3 Completeness/Soundness

These are inherently S5-specific. Parameterize the infrastructure but keep S5 assumptions explicit:
```lean
theorem completeness [HasAxiomT Axioms] [HasAxiom4 Axioms] [HasAxiomB Axioms] ...
```

---

## 8. Feasibility Assessment

### 8.1 Per-System Axiom Inductive Types

**Feasible**: Each is a small inductive with 1-2 constructors. The `PropAxiom` + `AxiomK` base is shared. Disjunction-based composition is standard Lean 4.

### 8.2 DerivationTree Parameterization

**Feasible**: Adding one type parameter `(Axioms : Proposition Atom -> Prop)` is straightforward. The `ax` constructor changes from `(h : ModalAxiom phi)` to `(h : Axioms phi)`. All other constructors are unchanged.

### 8.3 Deduction Theorem Generalization

**Feasible**: The deduction theorem never inspects axiom payload. It only needs `implyK` and `implyS`, which are propositional axioms present in every normal modal logic.

### 8.4 MCS Generalization

**Feasible with care**: Most MCS lemmas are generic. The modal-specific ones (`mcs_box_closure`, `mcs_box_box`, `mcs_box_diamond`) need explicit hypotheses about which axioms are available. The box witness theorem is S5-specific and should remain S5-specific.

### 8.5 Risk: Universe Polymorphism

`DerivationTree` currently lives in `Type _` (auto-inferred universe). Adding an `Axioms` parameter (which is `Prop`-valued) should not cause universe issues since `Axioms phi : Prop` fits in any universe.

### 8.6 Risk: Build Regression

The main regression risk is in the `HasHilbertTree` instance and downstream deduction theorem. If the `Axioms` parameter doesn't carry proof that it includes `implyK`/`implyS`, the instance won't typecheck. The structural inclusion approach (`NormalModalAxioms` wrapping propositional axioms) avoids this cleanly.

---

## 9. Recommended Implementation Order

1. **ProofSystem.lean**: Add `ModalTHilbert`, `ModalDHilbert`, `ModalS4Hilbert` classes and tag types. Refactor `ModalS5Hilbert` to extend `ModalS4Hilbert`.

2. **DerivationTree.lean**: Define per-system axiom inductives. Parameterize `DerivationTree`, `height`, `Deriv`, `Derivable`, `modalDerivationSystem`. Create S5 aliases.

3. **DeductionTheorem.lean**: Parameterize `HasHilbertTree` instance, `deductionWithMem`, `deductionTheorem`, `modal_has_deduction_theorem`. (Mechanical -- no logic changes.)

4. **MCS.lean**: Parameterize abbreviations, generic lemmas, and add explicit axiom hypotheses to modal-specific lemmas. Keep S5-specific box witness under S5 axiom assumptions.

5. **Soundness.lean**: Parameterize, adding per-system frame condition hypotheses.

6. **Completeness.lean**: Parameterize infrastructure, keep S5-specific proofs with explicit S5 axiom assumptions.

7. **Final verification**: `lake build` to confirm zero regressions.

---

## 10. Key Design Decisions (for planner)

| Decision | Recommendation | Rationale |
|----------|---------------|-----------|
| Axiom parameter type | `Axioms : Proposition Atom -> Prop` | Matches task spec, simple, composable |
| Propositional axiom inclusion | Structural wrapper `NormalModalAxioms` | Avoids typeclass overhead, ensures implyK/implyS |
| Per-system axiom types | Separate small inductives + disjunction | Scales to modal cube, clean separation |
| Backward compatibility | Type aliases pointing to S5 instantiation | Zero-regression guarantee |
| Completeness scope | Keep S5-specific, parameterize infrastructure only | Completeness for other systems is a separate task |
| HasHilbertTree | Parameterize with proof that Axioms includes prop axioms | Needed for deduction theorem |
