# Research Report: Task #23 -- Temporal Semantics on Linear Orders

**Task**: 23 -- Define standalone temporal semantics on linear orders
**Date**: 2026-06-08
**Session**: sess_1780980276_702f7c_23
**Type**: lean4

---

## 1. Executive Summary

Task 23 requires creating standalone temporal semantics for `Cslib.Logic.Temporal.Formula` on linear orders. This is new infrastructure -- not a port from the bimodal semantics (`TaskFrame`/`WorldHistory`/`truth_at`). The temporal module currently has syntax (Formula, Context), a proof system (Axioms, DerivationTree, Derivable, Instances), derived theorems (TemporalDerived), and frame condition typeclasses (FrameConditions), but no semantic evaluation. This task fills that gap.

Key design decisions identified through research:

1. **Model**: Simple `structure TemporalModel` with just `LinearOrder D` + valuation `D -> Atom -> Prop` (no task relation, no world histories, no accessibility relation)
2. **Satisfies**: Recursive definition on formula constructors, matching the bimodal `truth_at` convention for untl/snce argument order (event, guard)
3. **Validity**: Quantified over all linear orders, all models, all time points
4. **Frame conditions**: Leverage the existing `FrameConditions.lean` typeclasses (LinearTemporalFrame, SerialFrame, DenseTemporalFrame, DiscreteTemporalFrame)

---

## 2. Codebase Analysis

### 2.1 Existing Temporal Module Structure

```
Cslib/Logics/Temporal/
  Syntax/
    Formula.lean         -- Formula inductive {atom, bot, imp, untl, snce}
    Context.lean         -- Context = List (Formula Atom)
    Subformulas.lean     -- Subformula relation
    BigConj.lean         -- Big conjunction
  ProofSystem/
    Axioms.lean          -- 26 BX axioms + FrameClass inductive
    Derivation.lean      -- DerivationTree (Type-valued)
    Derivable.lean       -- Prop-valued wrapper
    Instances.lean       -- TemporalBXHilbert instance registration
  ProofSystem.lean       -- Barrel import
  Theorems/
    FrameConditions.lean -- Frame condition typeclasses (Linear, Serial, Dense, Discrete)
    TemporalDerived.lean -- 20+ derived theorems (G/H distribution, etc.)
  Theorems.lean          -- Barrel import
  Semantics/             -- DOES NOT EXIST (target of this task)
```

### 2.2 Existing Bimodal Semantics (Reference Pattern)

The bimodal module provides a complete semantics stack:

| File | Definition | Purpose |
|------|-----------|---------|
| `TaskFrame.lean` | `TaskFrame D` | Frame with WorldState type + task_rel + axioms |
| `WorldHistory.lean` | `WorldHistory F` | Domain + states + task constraint |
| `TaskModel.lean` | `TaskModel Atom F` | Frame + valuation on WorldState |
| `Truth.lean` | `truth_at M Omega tau t phi` | Truth evaluation (recursive on formula) |
| `Validity.lean` | `valid phi` | Universal quantification over all components |

**Key differences from what we need**:
- Bimodal has `WorldState` type, `task_rel`, `WorldHistory`, `ShiftClosed` sets -- all unnecessary for standalone temporal
- Bimodal requires `AddCommGroup D`, `IsOrderedAddMonoid D` (for time-shift algebra) -- we only need `LinearOrder D`
- Bimodal atoms are existentially qualified by `domain t` membership -- temporal atoms are unconditional
- Bimodal has `box` constructor quantifying over world histories -- temporal has no box

### 2.3 Modal Semantics Pattern (Secondary Reference)

`Cslib/Logics/Modal/Basic.lean` provides a clean pattern:

```lean
structure Model (World : Type*) (Atom : Type*) where
  r : World -> World -> Prop
  v : World -> Atom -> Prop

def Satisfies (m : Model World Atom) (w : World) : Proposition Atom -> Prop
  | .atom p => m.v w p
  | .bot => False
  | .imp phi1 phi2 => Satisfies m w phi1 -> Satisfies m w phi2
  | .box phi => forall w', m.r w w' -> Satisfies m w' phi
```

This is the cleanest pattern to follow -- structure + recursive satisfaction.

### 2.4 Temporal Formula Convention

The `Formula` type in `Syntax/Formula.lean` uses the Burgess convention:
- `untl phi1 phi2` = `phi1 U phi2` where phi1 is EVENT, phi2 is GUARD
- `some_future phi = untl phi top` (event=phi, guard=trivial)
- `snce phi1 phi2` = `phi1 S phi2` where phi1 is EVENT, phi2 is GUARD
- `some_past phi = snce phi top`

The bimodal `truth_at` (Truth.lean lines 64-69) confirms:
```lean
| Formula.untl phi psi =>
    exists s, t < s /\ truth_at M Omega tau s phi /\    -- phi at witness (EVENT)
      forall r, t < r -> r < s -> truth_at M Omega tau r psi  -- psi between (GUARD)
```

### 2.5 Frame Condition Typeclasses (Already Exist)

`FrameConditions.lean` already defines:

```lean
class LinearTemporalFrame (D : Type) [AddCommGroup D] [LinearOrder D]
    [IsOrderedAddMonoid D] : Prop

class SerialFrame (D : Type) [AddCommGroup D] [LinearOrder D]
    [IsOrderedAddMonoid D] [Nontrivial D] [NoMaxOrder D] [NoMinOrder D] : Prop

class DenseTemporalFrame (D : Type) [AddCommGroup D] [LinearOrder D]
    [IsOrderedAddMonoid D] [Nontrivial D] [NoMaxOrder D] [NoMinOrder D]
    [DenselyOrdered D] : Prop

class DiscreteTemporalFrame (D : Type) [AddCommGroup D] [LinearOrder D]
    [IsOrderedAddMonoid D] [Nontrivial D] [NoMaxOrder D] [NoMinOrder D]
    [SuccOrder D] [PredOrder D] [IsSuccArchimedean D] : Prop
```

**Issue**: These typeclasses require `AddCommGroup D` and `IsOrderedAddMonoid D`, which is more structure than `LinearOrder D` alone. However, this is fine for frame conditions -- the standalone semantics (`Satisfies`) only requires `LinearOrder D`, while frame-conditioned validity can add extra constraints.

---

## 3. Design Decisions

### 3.1 Model Structure

```lean
structure TemporalModel (D : Type*) [LinearOrder D] (Atom : Type*) where
  valuation : D -> Atom -> Prop
```

**Rationale**: A temporal model on a linear order is just a valuation assigning truth to atoms at each time point. No accessibility relation (that's modal), no task relation (that's bimodal), no world histories. The linear order on D already provides the temporal structure.

**Alternative considered**: Using `structure TemporalFrame (D : Type*)` with `[LinearOrder D]` bundled separately, then `TemporalModel` extending it. Rejected because a temporal frame on a linear order IS the linear order -- there is nothing else to add. The frame IS D with its order. The model adds valuation.

### 3.2 Satisfaction Relation

```lean
def Temporal.Satisfies (M : TemporalModel D Atom) (t : D) :
    Temporal.Formula Atom -> Prop
  | .atom p => M.valuation t p
  | .bot => False
  | .imp phi psi => Satisfies M t phi -> Satisfies M t psi
  | .untl phi psi =>                           -- phi U psi: phi=EVENT, psi=GUARD
      exists s, t < s /\ Satisfies M s phi /\  -- phi at witness
        forall r, t < r -> r < s -> Satisfies M r psi  -- psi between
  | .snce phi psi =>                           -- phi S psi: phi=EVENT, psi=GUARD
      exists s, s < t /\ Satisfies M s phi /\
        forall r, s < r -> r < t -> Satisfies M r psi
```

This exactly mirrors the bimodal `truth_at` but without the WorldHistory/domain/Omega machinery. Atoms are just `M.valuation t p` (no domain membership check needed since every time point is in the model).

### 3.3 Validity Definitions

Three levels needed, matching the bimodal pattern and aligned with FrameClass:

1. **Valid on all linear orders (Base)**:
```lean
def Temporal.Valid (phi : Formula Atom) : Prop :=
  forall (D : Type) [LinearOrder D] [Nontrivial D]
    (M : TemporalModel D Atom) (t : D),
    Temporal.Satisfies M t phi
```

2. **Valid on dense linear orders**:
```lean
def Temporal.ValidDense (phi : Formula Atom) : Prop :=
  forall (D : Type) [LinearOrder D] [Nontrivial D] [DenselyOrdered D]
    (M : TemporalModel D Atom) (t : D),
    Temporal.Satisfies M t phi
```

3. **Valid on discrete linear orders**:
```lean
def Temporal.ValidDiscrete (phi : Formula Atom) : Prop :=
  forall (D : Type) [LinearOrder D] [Nontrivial D]
    [SuccOrder D] [PredOrder D] [IsSuccArchimedean D]
    (M : TemporalModel D Atom) (t : D),
    Temporal.Satisfies M t phi
```

**Note**: Using `Type` (not `Type*`) to avoid universe polymorphism issues, matching the bimodal `valid` pattern.

**Seriality**: The bimodal validity requires `Nontrivial D` to ensure the temporal type is non-degenerate. For standalone temporal, seriality (NoMaxOrder + NoMinOrder) may be needed for certain axioms (BX1 serial_future requires exists s > t for all t). We should expose both:
- `Valid` with just `Nontrivial D` -- minimal
- `ValidSerial` with `NoMaxOrder D` and `NoMinOrder D` -- for BX1/BX1'

### 3.4 Semantic Consequence

```lean
def Temporal.SemanticConsequence (Gamma : Context Atom) (phi : Formula Atom) : Prop :=
  forall (D : Type) [LinearOrder D] [Nontrivial D]
    (M : TemporalModel D Atom) (t : D),
    (forall psi in Gamma, Temporal.Satisfies M t psi) ->
    Temporal.Satisfies M t phi
```

### 3.5 Satisfiability

```lean
def Temporal.Satisfiable (phi : Formula Atom) : Prop :=
  exists (D : Type) (_ : LinearOrder D)
    (M : TemporalModel D Atom) (t : D),
    Temporal.Satisfies M t phi
```

### 3.6 Notation

Following the bimodal pattern: `|= phi` for validity, `Gamma |= phi` for consequence.

### 3.7 Basic Lemmas

The following truth lemmas should be included (mirroring bimodal Truth.lean):

1. `bot_false`: `not (Satisfies M t Formula.bot)`
2. `imp_iff`: `Satisfies M t (imp phi psi) <-> (Satisfies M t phi -> Satisfies M t psi)`
3. `atom_iff`: `Satisfies M t (atom p) <-> M.valuation t p`
4. `some_future_iff`: `Satisfies M t (some_future phi) <-> exists s, t < s /\ Satisfies M s phi`
5. `some_past_iff`: `Satisfies M t (some_past phi) <-> exists s, s < t /\ Satisfies M s phi`
6. `all_future_iff`: `Satisfies M t (all_future phi) <-> forall s, t < s -> Satisfies M s phi`
7. `all_past_iff`: `Satisfies M t (all_past phi) <-> forall s, s < t -> Satisfies M s phi`

Plus validity reduction lemmas:
8. `valid_implies_valid_dense`: `Valid phi -> ValidDense phi`
9. `valid_implies_valid_discrete`: `Valid phi -> ValidDiscrete phi`
10. `valid_iff_empty_consequence`: `Valid phi <-> SemanticConsequence [] phi`
11. `consequence_monotone`: `Gamma <= Delta -> SemanticConsequence Gamma phi -> SemanticConsequence Delta phi`

---

## 4. File Plan

### File 1: `Cslib/Logics/Temporal/Semantics/Model.lean` (~60-80 lines)

- `TemporalModel D Atom` structure
- Example models: `all_false`, `all_true`, `constant_model`
- Namespace: `Cslib.Logic.Temporal`

### File 2: `Cslib/Logics/Temporal/Semantics/Satisfies.lean` (~200-250 lines)

- `Temporal.Satisfies` recursive definition
- Truth lemmas (bot_false, imp_iff, atom_iff, some_future_iff, etc.)
- Notation for `M, t |= phi`
- Namespace: `Cslib.Logic.Temporal`

### File 3: `Cslib/Logics/Temporal/Semantics/Validity.lean` (~150-200 lines)

- `Temporal.Valid`, `Temporal.ValidDense`, `Temporal.ValidDiscrete`
- `Temporal.ValidSerial` (with NoMaxOrder + NoMinOrder)
- `Temporal.SemanticConsequence`
- `Temporal.Satisfiable`, `Temporal.FormulaSatisfiable`
- Validity reduction lemmas
- Validity/consequence relationship lemmas
- Notation: `|= phi`, `Gamma |= phi`
- Namespace: `Cslib.Logic.Temporal`

### Estimated Total: 410-530 lines (within 400-600 target)

---

## 5. Import Dependencies

### Model.lean imports:
```lean
import Cslib.Logics.Temporal.Syntax.Formula
import Mathlib.Order.Defs.LinearOrder
```

### Satisfies.lean imports:
```lean
import Cslib.Logics.Temporal.Semantics.Model
```

### Validity.lean imports:
```lean
import Cslib.Logics.Temporal.Semantics.Satisfies
import Cslib.Logics.Temporal.Syntax.Context   -- for SemanticConsequence
```

No dependency on bimodal modules. No dependency on ProofSystem modules (soundness is a follow-up). No dependency on FrameConditions.lean (validity uses raw Mathlib typeclasses).

---

## 6. Key Mathlib Dependencies

| Mathlib concept | Usage | Module |
|----------------|-------|--------|
| `LinearOrder` | Core ordering for time domain | `Mathlib.Order.Defs.LinearOrder` |
| `Nontrivial` | Non-degenerate time domain | (in Lean core or `Mathlib.Logic.Nontrivial.Defs`) |
| `DenselyOrdered` | Dense validity | `Mathlib.Order.Defs.Dense` |
| `SuccOrder` / `PredOrder` | Discrete validity | `Mathlib.Order.SuccPred.Basic` |
| `IsSuccArchimedean` | Discrete archimedean | `Mathlib.Order.SuccPred.Archimedean` |
| `NoMaxOrder` / `NoMinOrder` | Serial validity | `Mathlib.Order.Defs.Unbundled` |
| `exists_gt` / `exists_lt` | Seriality proofs | `Mathlib.Order.Defs.Unbundled` |

---

## 7. Namespace and Convention Alignment

### Namespace: `Cslib.Logic.Temporal`

This matches the existing temporal module namespace. The new files will add:
- `Cslib.Logic.Temporal.TemporalModel`
- `Cslib.Logic.Temporal.Satisfies` (the function)
- `Cslib.Logic.Temporal.Valid`, `ValidDense`, `ValidDiscrete`
- `Cslib.Logic.Temporal.SemanticConsequence`

### Convention Alignment with Bimodal

| Bimodal | Temporal Standalone | Notes |
|---------|-------------------|-------|
| `TaskFrame D` | (none -- LinearOrder IS the frame) | Simplification |
| `TaskModel Atom F` | `TemporalModel D Atom` | Same pattern |
| `WorldHistory F` | (none) | Not needed |
| `truth_at M Omega tau t phi` | `Satisfies M t phi` | Simplified |
| `valid phi` | `Valid phi` | Same quantification pattern |
| `semantic_consequence` | `SemanticConsequence` | Same pattern |
| `satisfiable` | `Satisfiable` | Same pattern |

### Convention: `expose` attribute

The bimodal semantics uses `@[expose] public section`. The temporal module should follow the same pattern for API visibility.

---

## 8. Potential Challenges

### 8.1 Universe Polymorphism

The bimodal `valid` uses `Type` (not `Type*`) to avoid universe issues. We should follow suit. The quantification `forall (D : Type)` is standard.

### 8.2 Seriality Requirements

Some BX axioms (serial_future, serial_past) require `NoMaxOrder`/`NoMinOrder` to be valid. The base `Valid` definition should use minimal constraints (`Nontrivial`), with `ValidSerial` adding seriality. The soundness proof (future task) will need to match axiom frame classes to validity definitions.

### 8.3 No Recursive Termination Issues

`Satisfies` is structurally recursive on the formula, so Lean will accept it without termination proofs.

### 8.4 Classical vs Constructive

The bimodal semantics uses classical reasoning (material conditional for imp). Our `Satisfies` for `imp` is `Satisfies M t phi -> Satisfies M t psi`, which is already the standard Prop-level implication -- this is fine in Lean's classical logic foundation.

---

## 9. Relationship to Downstream Tasks

- **Temporal soundness** (future task): `Derivable fc [] phi -> Valid phi` (or frame-class-specific variants). This task provides the semantic side; soundness connects it to the proof system.
- **Bimodal embedding** (future): Show that bimodal `truth_at` restricted to a single history is equivalent to temporal `Satisfies`. This is not required now but the convention alignment ensures it will work.
- **Task 6 (Bimodal Soundness)**: Independent -- uses bimodal semantics, not temporal.

---

## 10. Recommendations

1. **Implement in the order**: Model.lean -> Satisfies.lean -> Validity.lean
2. **Keep it simple**: No frame structure beyond LinearOrder. No accessibility relation. No world histories.
3. **Match bimodal conventions exactly**: Same untl/snce argument order, same truth conditions (just simplified)
4. **Include basic lemmas**: The truth lemmas (bot_false, imp_iff, etc.) are essential for downstream soundness proofs
5. **Use `Type` not `Type*`** in validity quantifiers to avoid universe issues
6. **Do not depend on FrameConditions.lean**: Use raw Mathlib typeclasses directly in validity definitions. This avoids circular dependencies and keeps semantics independent.
