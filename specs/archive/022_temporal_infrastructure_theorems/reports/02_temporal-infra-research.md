# Research Report: Task #22 -- Temporal Infrastructure and Theorems

**Task**: 22 -- Build temporal proof system infrastructure and port temporal theorems
**Date**: 2026-06-08
**Session**: sess_1780970224_ba1435_22
**Builds on**: 01_seed-research.md

---

## Executive Summary

This report provides a detailed source-to-target mapping for porting temporal proof system infrastructure from BimodalLogic to cslib. The analysis covers all eight components identified in the seed report, with exact axiom inventories, typeclass designs, and structural challenges.

Key findings:
- **20 new temporal axiom abbrevs** needed in Axioms.lean (currently only 2 exist: SerialFuture, SerialPast)
- **20 new HasAxiom* typeclasses** needed in ProofSystem.lean
- **TemporalBXHilbert** must extend all 20 temporal HasAxiom* classes (currently extends only PropositionalHilbert + empty TemporalNecessitation)
- **TemporalNecessitation** must become non-empty with actual derivation rule
- **Critical bug**: cslib's `ModalFuture` axiom formula is incorrect relative to the BimodalLogic source
- **Diamond-avoidance** for BimodalTMHilbert compatibility requires careful typeclass design
- **788 lines** of TemporalDerived theorems must be translated to generic typeclass style
- **220 lines** of frame condition typeclasses already exist in BimodalLogic and can be adapted

---

## 1. Axiom Inventory: Exact Mapping

### 1.1 Existing Axiom Abbrevs in cslib (2)

| cslib Abbrev | BimodalLogic Axiom | Status |
|---|---|---|
| `SerialFuture` | `serial_future` | Exists, correct |
| `SerialPast` | `serial_past` | Exists, correct |

### 1.2 New Temporal Axiom Abbrevs Needed (20)

Each abbrev should be added to `Cslib/Foundations/Logic/Axioms.lean` in the `Temporal` section, parameterized over `[HasBot F] [HasImp F] [HasUntil F] [HasSince F]`.

| # | cslib Name (proposed) | BimodalLogic Constructor | Formula (Burgess convention) | Params |
|---|---|---|---|---|
| 1 | `LeftMonoUntilG` | `left_mono_until_G` | `G(phi -> chi) -> (psi U phi -> psi U chi)` | `phi chi psi` |
| 2 | `LeftMonoSinceH` | `left_mono_since_H` | `H(phi -> chi) -> (psi S phi -> psi S chi)` | `phi chi psi` |
| 3 | `RightMonoUntil` | `right_mono_until` | `G(phi -> psi) -> (phi U chi -> psi U chi)` | `phi psi chi` |
| 4 | `RightMonoSince` | `right_mono_since` | `H(phi -> psi) -> (phi S chi -> psi S chi)` | `phi psi chi` |
| 5 | `ConnectFuture` | `connect_future` | `phi -> G(P(phi))` | `phi` |
| 6 | `ConnectPast` | `connect_past` | `phi -> H(F(phi))` | `phi` |
| 7 | `EnrichmentUntil` | `enrichment_until` | `p /\ (psi U phi) -> (psi /\ S(p,phi)) U phi` | `phi psi p` |
| 8 | `EnrichmentSince` | `enrichment_since` | `p /\ (psi S phi) -> (psi /\ U(p,phi)) S phi` | `phi psi p` |
| 9 | `SelfAccumUntil` | `self_accum_until` | `U(psi,phi) -> U(psi, phi /\ U(psi,phi))` | `phi psi` |
| 10 | `SelfAccumSince` | `self_accum_since` | `S(psi,phi) -> S(psi, phi /\ S(psi,phi))` | `phi psi` |
| 11 | `AbsorbUntil` | `absorb_until` | `U(phi /\ U(psi,phi), phi) -> U(psi,phi)` | `phi psi` |
| 12 | `AbsorbSince` | `absorb_since` | `S(phi /\ S(psi,phi), phi) -> S(psi,phi)` | `phi psi` |
| 13 | `LinearUntil` | `linear_until` | `U(psi,phi) /\ U(theta,chi) -> ...` (3-way disjunction) | `phi psi chi theta` |
| 14 | `LinearSince` | `linear_since` | `S(psi,phi) /\ S(theta,chi) -> ...` (3-way disjunction) | `phi psi chi theta` |
| 15 | `UntilF` | `until_F` | `U(psi,phi) -> F(psi)` | `phi psi` |
| 16 | `SinceP` | `since_P` | `S(psi,phi) -> P(psi)` | `phi psi` |
| 17 | `TempLinearity` | `temp_linearity` | `F(phi) /\ F(psi) -> F(phi/\psi) \/ F(phi/\F(psi)) \/ F(F(phi)/\psi)` | `phi psi` |
| 18 | `TempLinearityPast` | `temp_linearity_past` | `P(phi) /\ P(psi) -> ...` (past mirror) | `phi psi` |
| 19 | `FUntilEquiv` | `F_until_equiv` | `F(phi) -> U(phi, top)` | `phi` |
| 20 | `PSinceEquiv` | `P_since_equiv` | `P(phi) -> S(phi, top)` | `phi` |

**Note on parameter order**: BimodalLogic uses `(phi chi psi)` for some axioms (e.g., `left_mono_until_G`). The cslib abbrevs should preserve the same parameter order to avoid confusion during porting.

**Note on encoding**: Each abbrev must be written in terms of `HasImp.imp`, `HasBot.bot`, `HasUntil.untl`, `HasSince.snce` -- the raw connective typeclasses. The derived temporal operators (F, G, P, H) are NOT available at the Axioms.lean level since they are defined on specific formula types, not on the connective typeclasses. This means:
- `F(phi) = untl (imp bot bot) phi` (i.e., `top U phi`)
- `G(phi) = neg (F (neg phi))` = `imp (untl (imp bot bot) (imp phi bot)) bot`
- `P(phi) = snce (imp bot bot) phi`
- `H(phi) = imp (snce (imp bot bot) (imp phi bot)) bot`

### 1.3 Critical Bug: ModalFuture Axiom Mismatch

**BimodalLogic** `modal_future`: `box(phi) -> box(all_future(phi))` -- "necessary truths remain necessary in the future" (`□phi -> □Gphi`)

**cslib** `ModalFuture`: `box(untl top phi) -> untl top (box phi)` -- "□Fphi -> F□phi"

These are **completely different axioms**. The cslib version is not the standard MF axiom from the BimodalLogic proof system. This discrepancy must be corrected as part of this task or flagged as a prerequisite fix.

**Recommendation**: Fix `ModalFuture` in Axioms.lean to match BimodalLogic:
```lean
protected abbrev ModalFuture (φ : F) : F :=
  HasImp.imp (HasBox.box φ) (HasBox.box (... all_future encoding ...))
```

However, `all_future` requires both `HasUntil` and `HasImp` and `HasBot` to encode. The current `ModalFuture` section has `[HasBox F] [HasUntil F]` -- it would additionally need `[HasSince F]` if we want `all_future` (which uses `neg` which uses `bot`). Actually, `all_future` only needs `HasUntil`, `HasImp`, and `HasBot` (not `HasSince`). Let me verify:

`G(phi) = neg(F(neg phi)) = imp (untl (imp bot bot) (imp phi bot)) bot`

This requires `HasBot`, `HasImp`, `HasUntil` -- all of which are already in scope in the Interaction section. So the fix is:

```lean
protected abbrev ModalFuture (φ : F) : F :=
  let top := HasImp.imp (HasBot.bot : F) HasBot.bot
  let neg_φ := HasImp.imp φ HasBot.bot
  let G_φ := HasImp.imp (HasUntil.untl top neg_φ) HasBot.bot
  HasImp.imp (HasBox.box φ) (HasBox.box G_φ)
```

This fixes the MF axiom to match BimodalLogic's `□φ → □Gφ`.

---

## 2. HasAxiom* Typeclasses

### 2.1 New Typeclasses Needed (20)

Each new axiom abbrev needs a corresponding `HasAxiom*` typeclass in `ProofSystem.lean`. Pattern:

```lean
class HasAxiomLeftMonoUntilG where
  leftMonoUntilG {φ χ ψ : F} :
    InferenceSystem.DerivableIn S (Axioms.LeftMonoUntilG φ χ ψ)
```

Full list:

| # | Typeclass Name | Axiom Abbrev | Type Params |
|---|---|---|---|
| 1 | `HasAxiomLeftMonoUntilG` | `LeftMonoUntilG` | `{phi chi psi : F}` |
| 2 | `HasAxiomLeftMonoSinceH` | `LeftMonoSinceH` | `{phi chi psi : F}` |
| 3 | `HasAxiomRightMonoUntil` | `RightMonoUntil` | `{phi psi chi : F}` |
| 4 | `HasAxiomRightMonoSince` | `RightMonoSince` | `{phi psi chi : F}` |
| 5 | `HasAxiomConnectFuture` | `ConnectFuture` | `{phi : F}` |
| 6 | `HasAxiomConnectPast` | `ConnectPast` | `{phi : F}` |
| 7 | `HasAxiomEnrichmentUntil` | `EnrichmentUntil` | `{phi psi p : F}` |
| 8 | `HasAxiomEnrichmentSince` | `EnrichmentSince` | `{phi psi p : F}` |
| 9 | `HasAxiomSelfAccumUntil` | `SelfAccumUntil` | `{phi psi : F}` |
| 10 | `HasAxiomSelfAccumSince` | `SelfAccumSince` | `{phi psi : F}` |
| 11 | `HasAxiomAbsorbUntil` | `AbsorbUntil` | `{phi psi : F}` |
| 12 | `HasAxiomAbsorbSince` | `AbsorbSince` | `{phi psi : F}` |
| 13 | `HasAxiomLinearUntil` | `LinearUntil` | `{phi psi chi theta : F}` |
| 14 | `HasAxiomLinearSince` | `LinearSince` | `{phi psi chi theta : F}` |
| 15 | `HasAxiomUntilF` | `UntilF` | `{phi psi : F}` |
| 16 | `HasAxiomSinceP` | `SinceP` | `{phi psi : F}` |
| 17 | `HasAxiomTempLinearity` | `TempLinearity` | `{phi psi : F}` |
| 18 | `HasAxiomTempLinearityPast` | `TempLinearityPast` | `{phi psi : F}` |
| 19 | `HasAxiomFUntilEquiv` | `FUntilEquiv` | `{phi : F}` |
| 20 | `HasAxiomPSinceEquiv` | `PSinceEquiv` | `{phi : F}` |

### 2.2 Typeclass Dependencies

All temporal `HasAxiom*` typeclasses require: `[HasBot F] [HasImp F] [HasUntil F] [HasSince F] [InferenceSystem S F]`

The variable section should be:
```lean
variable (S : Type*) [HasBot F] [HasImp F] [HasUntil F] [HasSince F] [InferenceSystem S F]
```

Note: `HasSince` is needed even for future-direction axioms because the `all_future` encoding uses `imp` + `untl` + `bot` (no since), but some axioms like `ConnectFuture` use `some_past` which needs `snce`, and `EnrichmentUntil` explicitly uses both `untl` and `snce`.

### 2.3 Existing Temporal HasAxiom Typeclasses

Currently in cslib (2 axiom typeclasses exist, but are folded into `HasAxiomSerialFuture`/`HasAxiomSerialPast` -- actually these DON'T exist. The SerialFuture/SerialPast abbrevs have no corresponding HasAxiom* typeclasses). So we need 22 total (20 new BX + 2 serial).

Wait -- checking again: cslib has NO temporal HasAxiom* typeclasses at all. The TemporalBXHilbert just extends PropositionalHilbert + TemporalNecessitation. So we need HasAxiom* for all 22 temporal axioms including serial.

Updated count: **22 new HasAxiom* typeclasses** (20 BX + 2 serial: `HasAxiomSerialFuture`, `HasAxiomSerialPast`).

---

## 3. TemporalBXHilbert Restructuring

### 3.1 Current State (Shell)

```lean
class TemporalBXHilbert (S : Type*) [HasBot F] [HasImp F] [HasUntil F]
    [HasSince F] [InferenceSystem S F]
    extends PropositionalHilbert S (F := F),
            TemporalNecessitation S (F := F)
```

This is architecturally incomplete: any `PropositionalHilbert S` trivially satisfies `TemporalBXHilbert` since `TemporalNecessitation` is an empty marker class.

### 3.2 Target State (Full)

```lean
class TemporalBXHilbert (S : Type*) [HasBot F] [HasImp F] [HasUntil F]
    [HasSince F] [InferenceSystem S F]
    extends PropositionalHilbert S (F := F),
            TemporalNecessitation S (F := F),
            HasAxiomSerialFuture S (F := F),
            HasAxiomSerialPast S (F := F),
            HasAxiomLeftMonoUntilG S (F := F),
            HasAxiomLeftMonoSinceH S (F := F),
            HasAxiomRightMonoUntil S (F := F),
            HasAxiomRightMonoSince S (F := F),
            HasAxiomConnectFuture S (F := F),
            HasAxiomConnectPast S (F := F),
            HasAxiomEnrichmentUntil S (F := F),
            HasAxiomEnrichmentSince S (F := F),
            HasAxiomSelfAccumUntil S (F := F),
            HasAxiomSelfAccumSince S (F := F),
            HasAxiomAbsorbUntil S (F := F),
            HasAxiomAbsorbSince S (F := F),
            HasAxiomLinearUntil S (F := F),
            HasAxiomLinearSince S (F := F),
            HasAxiomUntilF S (F := F),
            HasAxiomSinceP S (F := F),
            HasAxiomTempLinearity S (F := F),
            HasAxiomTempLinearityPast S (F := F),
            HasAxiomFUntilEquiv S (F := F),
            HasAxiomPSinceEquiv S (F := F)
```

### 3.3 Lean 4 Class Extension Limit Concern

Lean 4 has a practical limit on the number of `extends` clauses in a class definition. With 24 parent classes (PropositionalHilbert + TemporalNecessitation + 22 HasAxiom*), we might hit performance or compilation issues. The FormalizedFormalLogic/Foundation project handles this by using 15+ extends without issue, but 24 is pushing it.

**Mitigation options**:
1. Group related axioms into intermediate bundle classes (e.g., `HasBXMonotonicity` extending the 4 mono axioms)
2. Proceed with flat extends and measure compilation time
3. Use instance fields instead of extends for some axioms

**Recommendation**: Start with flat extends (option 2). If compilation is problematic, switch to intermediate bundles (option 1).

---

## 4. TemporalNecessitation

### 4.1 Current State (Empty Marker)

```lean
class TemporalNecessitation (S : Type*) [HasUntil F] [HasSince F]
    [InferenceSystem S F]
```

This is an empty class with no fields.

### 4.2 Target State (With Derivation Rules)

```lean
class TemporalNecessitation (S : Type*) [HasBot F] [HasImp F]
    [HasUntil F] [HasSince F] [InferenceSystem S F] where
  /-- Temporal necessitation: from S |- phi, derive S |- G(phi). -/
  tempNec {φ : F} :
    InferenceSystem.DerivableIn S φ →
    InferenceSystem.DerivableIn S (... G(phi) encoding ...)
  /-- Temporal duality: from S |- phi, derive S |- swap_temporal(phi). -/
  tempDual {φ : F} :
    InferenceSystem.DerivableIn S φ →
    InferenceSystem.DerivableIn S (... swap encoding ...)
```

**Design challenge**: The `swap_temporal` operation is defined on concrete formula types (`Temporal.Formula`, `Bimodal.Formula`), not on the generic connective typeclasses. To state temporal duality generically, we need either:

(a) A `HasSwapTemporal` typeclass:
```lean
class HasSwapTemporal (F : Type*) where
  swap_temporal : F -> F
```

(b) Derive `H(phi)` necessitation separately (past necessitation) instead of temporal duality

(c) Only include `tempNec` (G-necessitation) and derive H-necessitation as a theorem via duality at the concrete formula level

**Recommendation**: Option (c) is cleanest -- TemporalNecessitation provides `tempNec` (G-necessitation) only. Past necessitation (`⊢ phi` implies `⊢ H(phi)`) is derived at the concrete formula level using the temporal duality rule, exactly as in BimodalLogic's `Theorems/GeneralizedNecessitation.lean`.

However, option (c) means temporal duality is NOT part of the generic typeclass interface but is only available for concrete formula types. This matches BimodalLogic's architecture where temporal duality is a concrete DerivationTree constructor, not a typeclass method.

**Encoding of G(phi)**: We need to express `G(phi)` generically. Using raw connectives:
```
G(phi) = neg(F(neg phi)) = imp (untl (imp bot bot) (imp phi bot)) bot
```

So:
```lean
class TemporalNecessitation (S : Type*) [HasBot F] [HasImp F]
    [HasUntil F] [HasSince F] [InferenceSystem S F] where
  tempNec {φ : F} :
    InferenceSystem.DerivableIn S φ →
    InferenceSystem.DerivableIn S
      (HasImp.imp
        (HasUntil.untl (HasImp.imp HasBot.bot HasBot.bot)
          (HasImp.imp φ HasBot.bot))
        HasBot.bot)
```

This encodes `G(phi)` at the typeclass level. Note that `HasSince` is NOT needed for this encoding, but is retained as a parameter since temporal proof systems inherently have both until and since.

**Note**: The current `TemporalNecessitation` signature requires `[HasUntil F] [HasSince F]` but NOT `[HasBot F] [HasImp F]`. These additional constraints must be added.

---

## 5. BimodalTMHilbert Diamond-Avoidance

### 5.1 The Diamond Problem

If `BimodalTMHilbert` extends both `ModalS5Hilbert` and `TemporalBXHilbert`, we get a diamond:

```
      PropositionalHilbert
       /              \
ModalS5Hilbert   TemporalBXHilbert
       \              /
     BimodalTMHilbert
```

Lean 4 handles class diamonds by requiring all paths to the shared parent to produce the same instance. This works automatically if `extends` is used consistently.

### 5.2 The BimodalConnectives Pattern

cslib already uses this pattern for connectives:

```lean
class BimodalConnectives (F : Type*) extends ModalConnectives F, HasUntil F, HasSince F
```

Note: `BimodalConnectives` does NOT extend `TemporalConnectives`. Instead, it extends `ModalConnectives` and adds `HasUntil`/`HasSince` directly. This avoids the diamond through `PropositionalConnectives`.

### 5.3 Recommended BimodalTMHilbert Design

**Option A: Extend TemporalBXHilbert directly (diamond path)**

```lean
class BimodalTMHilbert (S : Type*) ...
    extends ModalS5Hilbert S (F := F),
            TemporalBXHilbert S (F := F),
            HasAxiomMF S (F := F)
```

Lean 4 should handle this diamond automatically since both paths to PropositionalHilbert go through `extends`.

**Option B: Mirror the BimodalConnectives pattern (diamond avoidance)**

```lean
class BimodalTMHilbert (S : Type*) ...
    extends ModalS5Hilbert S (F := F),
            TemporalNecessitation S (F := F),
            HasAxiomMF S (F := F),
            -- All 22 temporal HasAxiom* directly
            HasAxiomSerialFuture S (F := F),
            HasAxiomSerialPast S (F := F),
            ...
```

Then provide a manual instance:
```lean
instance [BimodalTMHilbert S (F := F)] : TemporalBXHilbert S (F := F) := { ... }
```

**Option C: Extend ModalS5Hilbert + TemporalNecessitation + individual temporal axioms (current structure)**

The current `BimodalTMHilbert` extends `ModalS5Hilbert + TemporalNecessitation + HasAxiomMF`. Once `TemporalBXHilbert` is filled with axioms, `BimodalTMHilbert` should extend `TemporalBXHilbert` (or at minimum include all of its axiom classes).

**Recommendation**: Option A (extend TemporalBXHilbert directly). Lean 4's class inheritance mechanism handles diamonds through `extends` properly. If compilation issues arise, fall back to Option B. The seed report's recommendation of Option B was conservative; modern Lean 4 handles this well.

If Option A is chosen, `BimodalTMHilbert` becomes:

```lean
class BimodalTMHilbert (S : Type*) [HasBot F] [HasImp F] [HasBox F]
    [HasUntil F] [HasSince F] [InferenceSystem S F]
    extends ModalS5Hilbert S (F := F),
            TemporalBXHilbert S (F := F),
            HasAxiomMF S (F := F)
```

This is clean, expresses the mathematical intent directly, and Lean 4 will unify the two `PropositionalHilbert` paths.

---

## 6. Temporal DerivationTree

### 6.1 Source: BimodalLogic DerivationTree

BimodalLogic's `DerivationTree` (385 lines) has 7 rules:
1. `axiom` (with FrameClass gating)
2. `assumption`
3. `modus_ponens`
4. `necessitation` (modal: `⊢ phi` implies `⊢ □phi`)
5. `temporal_necessitation` (`⊢ phi` implies `⊢ G(phi)`)
6. `temporal_duality` (`⊢ phi` implies `⊢ swap_temporal(phi)`)
7. `weakening`

### 6.2 Target: Temporal.DerivationTree

For cslib's temporal logic (no box), we need 5 rules (drop necessitation and modal axioms):
1. `axiom` -- temporal axiom schema instances
2. `assumption` -- formulas from context
3. `modus_ponens` -- standard MP
4. `temporal_necessitation` -- `⊢ phi` implies `⊢ G(phi)`
5. `temporal_duality` -- `⊢ phi` implies `⊢ swap_temporal(phi)`
6. `weakening` -- adding unused assumptions

### 6.3 Axiom Inductive for Temporal

We need a `Temporal.Axiom` inductive type with constructors for all 26 axioms (4 propositional + 22 temporal). This mirrors BimodalLogic's `Axiom` type but without the modal (5) and interaction (1) layers. Frame class parameterization should be included.

**Estimated size**: ~300 lines (axiom inductive + FrameClass + minFrameClass function).

### 6.4 Instance: TemporalBXHilbert (Temporal.HilbertBX)

Once the DerivationTree and Derivable wrapper are defined, we register:
```lean
instance : InferenceSystem Temporal.HilbertBX (Temporal.Formula Atom) := ...
instance : TemporalBXHilbert Temporal.HilbertBX (F := Temporal.Formula Atom) := ...
```

Each `HasAxiom*` instance is satisfied by constructing the appropriate `Derivable` from the axiom constructor.

---

## 7. TemporalDerived Theorems

### 7.1 Source Analysis (788 lines)

The BimodalLogic `TemporalDerived.lean` contains 30+ theorems organized into:

**Category A: G/H Distribution (4 noncomputable)**
- `G_distribution` (temp_k_dist_derived), `H_distribution`, `G_transitivity` (temp_4_derived), `H_transitivity`

**Category B: Temporal Monotonicity (4 computable + 2 aliases)**
- `F_mono`, `P_mono`, `G_mono` (alias), `H_mono` (alias)

**Category C: Duality and Contraposition (4)**
- `F_neg_G`, `P_neg_H`, `G_contrapose`, `H_contrapose`

**Category D: Future-Past Chains (4 noncomputable)**
- `connect_future_G`, `connect_past_H`, `connect_future_chain`, `connect_past_chain`

**Category E: Until/Since Structural (4 computable)**
- `until_mono_guard`, `since_mono_guard`, `until_mono_event`, `since_mono_event`

**Direct axiom wrappers (6)**
- `connect_future_thm`, `connect_past_thm`, `until_implies_some_future`, `since_implies_some_past`, `until_imp_F`, `since_imp_P`

**Conjunction Elimination (8)**
- `always_to_present`, `present_to_sometimes`, `weak_future_left/right`, `weak_past_left/right`, `always_imp_all_future`, `always_imp_all_past`

**Helpers (2)**
- `contrapositive`, `formula_or_comm`

### 7.2 Translation Strategy

All theorems in TemporalDerived are currently written against BimodalLogic's concrete `DerivationTree` type. For cslib, they must be translated to the generic `[TemporalBXHilbert S]` typeclass style.

**Key translation patterns**:

BimodalLogic (concrete):
```lean
def F_mono (φ ψ : Formula) :
    ⊢ (φ.imp ψ).all_future.imp (φ.some_future.imp ψ.some_future) :=
  DerivationTree.axiom [] _ (Axiom.right_mono_until φ ψ Formula.top) trivial
```

cslib (generic):
```lean
theorem F_mono {φ ψ : F} :
    InferenceSystem.DerivableIn S
      (HasImp.imp
        (... G(phi -> psi) encoding ...)
        (HasImp.imp (... F(phi) encoding ...) (... F(psi) encoding ...))) :=
  HasAxiomRightMonoUntil.rightMonoUntil  -- direct axiom application
```

**Challenge**: The raw `HasImp.imp`/`HasUntil.untl` encoding makes theorem statements very verbose. BimodalLogic uses `Formula.all_future`, `Formula.some_future` etc. which are much more readable. At the generic level, we must expand these to raw connective applications.

**Mitigation**: Define local abbreviations within the theorem module:
```lean
private abbrev someFuture (φ : F) [HasBot F] [HasImp F] [HasUntil F] : F :=
  HasUntil.untl (HasImp.imp HasBot.bot HasBot.bot) φ

private abbrev allFuture (φ : F) [HasBot F] [HasImp F] [HasUntil F] : F :=
  HasImp.imp (someFuture (HasImp.imp φ HasBot.bot)) HasBot.bot
```

### 7.3 Dependency Graph

The TemporalDerived theorems have internal dependencies:

```
Level 0 (direct axiom wrappers):
  F_mono, P_mono, until_mono_guard, since_mono_guard,
  until_mono_event, since_mono_event, F_neg_G, P_neg_H,
  connect_future_thm, connect_past_thm,
  until_implies_some_future, since_implies_some_past

Level 1 (derived from Level 0 + propositional):
  G_distribution (temp_k_dist_derived)  -- needs: right_mono_until + contraposition
  G_transitivity (temp_4_derived)       -- needs: right_mono_until + absorb_until + DNE

Level 2 (derived from Level 1):
  H_distribution   -- needs: G_distribution + temporal duality
  H_transitivity   -- needs: G_transitivity + temporal duality
  G_contrapose     -- needs: G_distribution
  G_and_intro      -- needs: G_distribution
  G_imp_trans      -- needs: G_distribution

Level 3 (derived from Level 2):
  H_contrapose     -- needs: H_distribution
  H_and_intro      -- needs: H_distribution
  H_imp_trans      -- needs: H_distribution
  connect_future_G -- needs: G_distribution
  connect_past_H   -- needs: H_distribution

Level 4 (deep chains):
  connect_future_chain -- needs: connect_future_G + connect_past_thm
  connect_past_chain   -- needs: connect_past_H + connect_future_thm
```

**Critical observation**: `H_distribution` and `H_transitivity` require temporal duality. In BimodalLogic, this is a concrete DerivationTree constructor. For the generic cslib setting, the H-distribution/H-transitivity theorems either:
(a) Require `TemporalBXHilbert` to include past-direction axiom versions (which it does via HasAxiomLeftMonoSinceH, HasAxiomRightMonoSince, etc.)
(b) Can be derived directly from the past-direction axioms without temporal duality

Looking at the source code, `H_distribution` (past_k_dist) is derived by applying temporal duality to `G_distribution`. But at the generic typeclass level, we can instead derive it directly from `HasAxiomRightMonoSince` (BX3') using the same proof pattern as G_distribution but with since instead of until. This avoids the need for temporal duality at the generic level.

**Recommendation**: Prove H-variants directly from past-direction axioms (BX2H, BX3', etc.) rather than via temporal duality. This is cleaner for the generic typeclass setting and avoids the swap_temporal dependency.

---

## 8. Frame Condition Typeclasses

### 8.1 Source: BimodalLogic FrameConditions (220 lines)

BimodalLogic's `FrameConditions/FrameClass.lean` already defines:
- `LinearTemporalFrame`
- `SerialFrame`
- `DenseTemporalFrame`
- `DiscreteTemporalFrame`

Plus standard instances for `Int`.

### 8.2 Target: Adapt for cslib

These typeclasses are generic (parameterized over ordered groups) and do NOT depend on BimodalLogic's formula type. They can be adapted to cslib almost verbatim. The only changes needed:

1. Namespace: `Bimodal.FrameConditions` -> `Cslib.Logic.Temporal.FrameConditions` (or similar)
2. Imports: Use cslib's Mathlib dependency instead of BimodalLogic's

**Note**: These frame condition typeclasses are used by temporal semantics (Task 23) and bimodal soundness. They should be placed in `Cslib/Logics/Temporal/FrameConditions/` to be available for both temporal and bimodal semantics.

### 8.3 Additional Frame-Specific Axioms

BimodalLogic has frame-class-specific axiom constructors:
- **Discrete (8)**: discrete_symm_fwd/bwd, discrete_propagate_fwd/bwd, discrete_box_necessity, prior_UZ, prior_SZ, z1
- **Dense (2)**: density, dense_indicator

These are NOT part of the base BX system but are extensions. For Task 22, we should:
1. Define the base BX axioms and HasAxiom* classes (22 axioms, as listed above)
2. Leave discrete and dense extension axioms for future tasks (or include as optional HasAxiom* classes that are NOT part of TemporalBXHilbert)

**Recommendation**: Include HasAxiom* for discrete and dense axioms but do NOT extend TemporalBXHilbert with them. They should be optional extensions used by DenseTemporalBXHilbert / DiscreteTemporalBXHilbert bundles if needed later.

---

## 9. Structural Challenges

### 9.1 Generic vs. Concrete Encoding

The biggest challenge is translating BimodalLogic's concrete formula-level proofs to cslib's generic typeclass-level proofs. Key differences:

| Aspect | BimodalLogic | cslib |
|--------|-------------|-------|
| Formula type | Concrete `Bimodal.Syntax.Formula` | Generic `F` with connective typeclasses |
| Proof objects | `DerivationTree fc Gamma phi` | `InferenceSystem.DerivableIn S phi` |
| Temporal operators | `Formula.all_future`, `Formula.some_future` | Raw `HasImp.imp (HasUntil.untl ...)` encoding |
| Duality | `swap_temporal` constructor | Not available generically |
| Computability | Mix of `def` and `noncomputable def` | All `noncomputable` (via `Nonempty` wrapper) |

### 9.2 Temporal Duality at Generic Level

BimodalLogic's `temporal_duality` rule (`⊢ phi` implies `⊢ swap_temporal(phi)`) is essential for deriving H-variants from G-variants. At the generic typeclass level, swap_temporal is not available.

**Solutions**:
1. Include past-direction axioms in the typeclass (already planned: BX2H, BX3', etc.)
2. Prove H-variants directly from past axioms (avoids duality)
3. Add `HasSwapTemporal` typeclass (adds complexity)

Since the BX system already includes past-direction axioms as separate constructors, solution (1+2) is natural: use the past axioms directly.

### 9.3 Propositional Infrastructure Reuse

cslib's propositional theorems (Task 20) provide: `imp_trans`, `identity`, `b_combinator`, `theorem_flip`, `theorem_app1`, `theorem_app2`, `pairing`, `dni`, `double_negation`, `contrapose_imp`, `contraposition`, `lce_imp`, `rce_imp`, `classical_merge`, `efq_axiom`, `peirce_axiom`, `raa`, `efq_neg`, `rcp`.

All of these are generic over `[PropositionalHilbert S]` and can be reused directly in temporal theorem proofs since `TemporalBXHilbert` extends `PropositionalHilbert`.

### 9.4 NonComputable Cascade

In BimodalLogic, `G_distribution` is noncomputable because it involves multiple proof term compositions. In cslib, all `InferenceSystem.DerivableIn` proofs are Prop-valued (`Nonempty`), so everything is naturally noncomputable. This is not a problem -- it just means all temporal theorems will be `noncomputable theorem` declarations.

---

## 10. Implementation Ordering

### Phase 1: Foundation (Axioms + Typeclasses)
1. Fix `ModalFuture` axiom in Axioms.lean
2. Add 20 temporal axiom abbrevs to Axioms.lean
3. Add 22 HasAxiom* typeclasses to ProofSystem.lean
4. Restructure TemporalBXHilbert to extend all 22 + TemporalNecessitation
5. Make TemporalNecessitation non-empty (add tempNec field)
6. Update BimodalTMHilbert to extend TemporalBXHilbert (or add compatibility instance)

### Phase 2: Concrete DerivationTree
7. Define `Temporal.Axiom` inductive in `Cslib/Logics/Temporal/ProofSystem/`
8. Define `Temporal.DerivationTree` with 6 rules
9. Define `Temporal.Derivable` (Prop wrapper)
10. Register `InferenceSystem` and `TemporalBXHilbert` instances

### Phase 3: Derived Theorems
11. Port Level 0 theorems (direct axiom wrappers)
12. Port Level 1 theorems (G_distribution, G_transitivity)
13. Port Level 2 theorems (H-variants, G_contrapose, G_and_intro)
14. Port Level 3+ theorems (chains, conjunction elimination)

### Phase 4: Frame Conditions
15. Adapt FrameClass typeclasses to cslib namespace

### Phase 5: BimodalCompat
16. BimodalTMHilbert -> TemporalBXHilbert compatibility instance

---

## 11. Line Count Estimates

| Component | Estimated Lines | Notes |
|-----------|----------------|-------|
| Axioms.lean additions | ~200 | 20 new abbrevs with docstrings |
| ProofSystem.lean additions | ~250 | 22 HasAxiom* + TemporalBXHilbert restructure + TemporalNecessitation update |
| Temporal.Axiom inductive | ~250 | 26 constructors + FrameClass + minFrameClass |
| Temporal.DerivationTree | ~150 | 6 rules + height + lift |
| Temporal.Derivable | ~100 | Prop wrapper + lemmas |
| TemporalDerived theorems | ~600 | 30+ theorems (less verbose than BimodalLogic's 788 due to typeclass reuse) |
| Frame conditions | ~130 | Adapted from BimodalLogic |
| BimodalCompat instance | ~50 | Compatibility layer |
| ModalFuture fix | ~5 | Bug fix |
| **Total** | **~1,735** | Slightly above seed estimate of ~1,500 |

---

## 12. Risk Assessment

| Risk | Severity | Mitigation |
|------|----------|------------|
| ModalFuture axiom bug | HIGH | Fix as first action in Phase 1 |
| Lean 4 class extends limit (24 parents) | MEDIUM | Monitor; fall back to intermediate bundles |
| Raw connective encoding verbosity | LOW | Local abbreviations for F/G/P/H |
| H-variant proofs without temporal duality | LOW | Use past-direction axioms directly |
| BimodalTMHilbert diamond | LOW | Lean 4 handles extends diamonds |
| Compilation time with large typeclass hierarchy | MEDIUM | Incremental building; `lake build Module.Name` |

---

## References

- BimodalLogic source: `/home/benjamin/Projects/BimodalLogic/Theories/Bimodal/`
  - `ProofSystem/Axioms.lean` (484 lines) -- 42 axiom constructors
  - `ProofSystem/Derivation.lean` (385 lines) -- DerivationTree with 7 rules
  - `ProofSystem/Derivable.lean` (221 lines) -- Prop wrapper
  - `Theorems/TemporalDerived.lean` (788 lines) -- 30+ temporal theorems
  - `Theorems/GeneralizedNecessitation.lean` (240 lines) -- past_necessitation, past_k_dist
  - `FrameConditions/FrameClass.lean` (220 lines) -- Frame condition typeclasses
- cslib target: `/home/benjamin/Projects/cslib/Cslib/`
  - `Foundations/Logic/Axioms.lean` (138 lines) -- 2 temporal abbrevs
  - `Foundations/Logic/ProofSystem.lean` (194 lines) -- Typeclass hierarchy
  - `Foundations/Logic/Connectives.lean` (98 lines) -- Connective typeclasses
  - `Foundations/Logic/Theorems/` -- Propositional theorems (Task 20)
  - `Logics/Temporal/Syntax/Formula.lean` (549 lines) -- Temporal formula type
