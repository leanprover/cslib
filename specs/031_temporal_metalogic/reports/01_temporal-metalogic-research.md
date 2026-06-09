# Research Report: Task 31 -- Standalone Temporal Metalogic

## 1. Existing Temporal Infrastructure Audit

### Files in `Cslib/Logics/Temporal/`

| Module | Lines | Contents |
|--------|-------|----------|
| `Syntax/Formula.lean` | ~550 | `Formula Atom` inductive with 5 constructors (`atom`, `bot`, `imp`, `untl`, `snce`). Derived operators: `neg`, `top`, `or`, `and`, `some_future` (F), `all_future` (G), `some_past` (P), `all_past` (H), `next`, `prev`, `release`, `trigger`, `weak_until`, `weak_since`, `strong_release`, `strong_trigger`, `always`, `sometimes`. Countable/Infinite/Denumerable instances. `swap_temporal` involution. `atoms` function. BEq instances. Complexity/temporal-depth measures. |
| `Syntax/Context.lean` | ~130 | `Context Atom := List (Formula Atom)` with `map`, `isEmpty`, `singleton`. |
| `Syntax/Subformulas.lean` | ~220 | `subformulas` function, self-membership, transitivity, component membership lemmas. |
| `Syntax/BigConj.lean` | ~55 | `bigconj` and `neg_bigconj` over formula lists. |
| `ProofSystem/Axioms.lean` | ~217 | `FrameClass` (`Base`, `Dense`, `Discrete`) with `PartialOrder` instance. `Axiom` inductive with 26 constructors (4 propositional + 22 BX temporal). `minFrameClass` function (all return `Base`). |
| `ProofSystem/Derivation.lean` | ~95 | `DerivationTree fc Gamma phi` with **6 constructors**: `axiom`, `assumption`, `modus_ponens`, `temporal_necessitation`, `temporal_duality`, `weakening`. Parametrized by `FrameClass`. `lift` for frame class monotonicity. |
| `ProofSystem/Derivable.lean` | ~96 | `Temporal.Derivable fc Gamma p := Nonempty (DerivationTree fc Gamma p)`. Constructor-mirroring lemmas: `ax`, `assume`, `mp`, `temp_nec`, `temp_dual`, `weaken`, `lift`. |
| `ProofSystem/Instances.lean` | ~210 | `InferenceSystem`, `ModusPonens`, `PropositionalHilbert`, `TemporalNecessitation`, all 22 `HasAxiom*`, and `TemporalBXHilbert` instances for `Temporal.HilbertBX`. |
| `Semantics/Model.lean` | ~60 | `TemporalModel D Atom` with `valuation : D -> Atom -> Prop`. Linear order on `D` via typeclass. |
| `Semantics/Satisfies.lean` | ~183 | `Satisfies M t phi` recursive definition. `untl` uses strict future existential with guard; `snce` uses strict past existential with guard. Simp lemmas for all constructors and derived operators. |
| `Semantics/Validity.lean` | ~199 | `Valid`, `ValidSerial`, `ValidDense`, `ValidDiscrete`. `SemanticConsequence`, `Satisfiable`. Reduction lemmas, modus ponens preservation, etc. |
| `Theorems/FrameConditions.lean` | ~84 | Frame condition marker typeclasses: `LinearTemporalFrame`, `SerialFrame`, `DenseTemporalFrame`, `DiscreteTemporalFrame`. `Int` instances. |
| `Theorems/TemporalDerived.lean` | ~270 | Generic derived theorems via `[TemporalBXHilbert S]`: G/H distribution, F/P monotonicity, contraposition under G/H, conjunction intro under G/H, implication transitivity under G/H, future-past interaction chains. |

**Summary**: The temporal infrastructure is complete and mature. Syntax, proof system, semantics, and derived theorems are all in place. The `Metalogic/` directory does **not** yet exist -- this task creates it.

## 2. Dependency Status

### Task 22: Temporal Infrastructure
- **Status**: Completed (infrastructure files above are the output)
- **Provides**: All syntax, proof system, semantics, and derived theorem modules

### Task 23: Temporal Semantics
- **Status**: Completed
- **Provides**: `TemporalModel`, `Satisfies`, `Valid`/`ValidSerial`/`ValidDense`/`ValidDiscrete`, `SemanticConsequence`, `Satisfiable`, along with all simp lemmas for truth evaluation

### Task 29: Generic MCS Infrastructure
- **Status**: Completed
- **Provides**: `DerivationSystem F`, `SetConsistent`, `SetMaximalConsistent`, `ConsistentSupersets`, `set_lindenbaum` (Lindenbaum's lemma via Zorn), `HasDeductionTheorem`, `closed_under_derivation`, `implication_property`, `negation_complete`
- **Location**: `Cslib/Foundations/Logic/Metalogic/Consistency.lean`

### Task 32: Dependency in state.json
- **Status**: Unknown/unrelated -- listed as a dependency but the description does not mention it. May be a reference to temporal-specific derived lemmas or something else. Not a blocker since all the needed infrastructure (syntax, semantics, proof system, generic MCS) exists.

**All critical dependencies are satisfied.** No blockers.

## 3. DerivationTree Constructor Analysis

The temporal `DerivationTree` has **6 constructors** (vs. 5 for modal):

| # | Constructor | Signature | Empty Context? | Notes |
|---|-------------|-----------|----------------|-------|
| 1 | `axiom` | `Gamma, phi, (h : Axiom phi), (h_fc : h.minFrameClass <= fc)` | No (any context) | Gated by frame class |
| 2 | `assumption` | `Gamma, phi, (h : phi in Gamma)` | No | Standard |
| 3 | `modus_ponens` | `Gamma, phi, psi, d1 : DT fc Gamma (phi.imp psi), d2 : DT fc Gamma phi` | No | Standard |
| 4 | `temporal_necessitation` | `phi, d : DT fc [] phi` | Yes (empty only) | Produces `phi.all_future` |
| 5 | `temporal_duality` | `phi, d : DT fc [] phi` | Yes (empty only) | Produces `phi.swap_temporal` |
| 6 | `weakening` | `Gamma, Delta, phi, d : DT fc Gamma phi, h : Gamma subseteq Delta` | No | Standard |

**Key differences from modal:**
- Constructor 4 uses `all_future` (temporal G) instead of `box`
- Constructor 5 (`temporal_duality`) is unique to temporal logic -- swaps future/past operators
- Both constructors 4 and 5 require empty context, which means in the deduction theorem, when the context is non-empty (A :: Gamma), these cases are vacuously impossible

**Impact on deduction theorem**: The deduction theorem proof must handle 6 cases. Constructors 4 and 5 are both impossible when `A :: Gamma` is the context (since it is non-empty), making these trivial cases. The structure closely mirrors the modal deduction theorem.

## 4. Bimodal Metalogic Patterns (Reference Template)

The Modal metalogic in `Cslib/Logics/Modal/Metalogic/` provides the pattern:

### 4.1 DerivationTree.lean (Modal)
- Defines `DerivationTree`, `height` function, height lemmas for well-founded recursion
- Defines `Deriv` (Prop wrapper), `Derivable`
- Defines `modalDerivationSystem : Metalogic.DerivationSystem (Proposition Atom)`

### 4.2 DeductionTheorem.lean (Modal)
- `removeAll` helper for list manipulation
- Helper functions: `deduction_axiom`, `deduction_imp_self`, `deduction_assumption_other`, `deduction_mp`
- `deduction_with_mem` -- core helper for weakening case
- `deduction_theorem` -- main theorem by well-founded recursion on `d.height`
- `modal_has_deduction_theorem` -- wraps for generic framework

### 4.3 MCS.lean (Modal)
- Abbreviations: `Modal.SetConsistent`, `Modal.SetMaximalConsistent`
- Instantiated generic properties: `modal_lindenbaum`, `modal_closed_under_derivation`, `modal_implication_property`, `modal_negation_complete`
- Modal-specific: `mcs_bot_not_mem`, `mcs_box_closure` (axiom T), `mcs_box_box` (axiom 4), `mcs_box_diamond` (axiom B), `mcs_box_mp` (axiom K)
- Not-in-MCS lemmas: `mcs_neg_of_not_mem`, `mcs_not_mem_of_neg`, `mcs_mem_iff_neg_not_mem`
- `mcs_box_witness` -- key lemma for completeness truth lemma

### 4.4 Soundness.lean (Modal)
- `axiom_sound` -- each axiom valid over S5 frames
- `soundness` -- structural induction on `DerivationTree`
- `soundness_derivable` -- empty-context specialization

### 4.5 Completeness.lean (Modal)
- `CanonicalWorld` -- MCS as worlds
- `CanonicalModel` -- accessibility + valuation
- Canonical frame properties (refl, trans, eucl)
- `truth_lemma` -- structural induction on formula
- `completeness` -- contrapositive argument

## 5. Temporal Metalogic Design

### 5.1 DerivationTree Setup (`Metalogic/DerivationTree.lean`, ~100 lines)

Mirrors the modal pattern but adapted for temporal:

```lean
-- Height function for the 6-constructor DerivationTree
def DerivationTree.height : DerivationTree fc Gamma phi -> Nat
  | .axiom _ _ _ _ => 0
  | .assumption _ _ _ => 0
  | .modus_ponens _ _ _ d1 d2 => 1 + max d1.height d2.height
  | .temporal_necessitation _ d => 1 + d.height
  | .temporal_duality _ d => 1 + d.height
  | .weakening _ _ _ d _ => 1 + d.height

-- Height lemmas for well-founded recursion
-- Deriv, Derivable
-- temporalDerivationSystem : Metalogic.DerivationSystem (Formula Atom)
```

The `temporalDerivationSystem` must provide:
- `Deriv := fun Gamma phi => Nonempty (DerivationTree FrameClass.Base Gamma phi)`
- `weakening`, `assumption`, `mp` from the corresponding tree constructors

Note: We fix `FrameClass.Base` for the derivation system since the generic MCS framework doesn't need frame class parametrization, and Base is the weakest.

### 5.2 Deduction Theorem (`Metalogic/DeductionTheorem.lean`, ~300 lines)

Structure follows modal exactly:

1. **removeAll** helper (can be shared or redefined)
2. **Helper functions**: `deduction_axiom`, `deduction_imp_self`, `deduction_assumption_other`, `deduction_mp`
3. **deduction_with_mem** -- handles the weakening subcase where `A in Gamma'`
4. **deduction_theorem** -- main theorem, 6 constructor cases:
   - `axiom`: Use `implyK` to wrap under implication
   - `assumption` (same): Produce `A -> A` via `deduction_imp_self`
   - `assumption` (other): Use `implyK` with the other assumption
   - `modus_ponens`: Recurse on both subderivations, combine via `implyS`
   - `temporal_necessitation`: Impossible (context is `A :: Gamma`, non-empty)
   - `temporal_duality`: Impossible (context is `A :: Gamma`, non-empty)
   - `weakening`: Three subcases (context equality, A in Gamma', A not in Gamma')
5. **temporal_has_deduction_theorem** -- wraps for generic framework

The temporal duality constructor adds exactly one additional trivial case compared to modal. Total line count is similar to modal (~250 lines including helpers).

### 5.3 MCS Theory (`Metalogic/MCS.lean`, ~400 lines)

This is where the temporal-specific content diverges significantly from modal.

**Generic properties (instantiated from Consistency.lean):**
- `temporal_lindenbaum`
- `temporal_closed_under_derivation`
- `temporal_implication_property`
- `temporal_negation_complete`

**Basic MCS properties:**
- `temporal_mcs_bot_not_mem`: Bottom not in MCS
- `temporal_mcs_neg_of_not_mem`, `temporal_mcs_not_mem_of_neg`, `temporal_mcs_mem_iff_neg_not_mem`

**Temporal-specific MCS properties for G/H:**
- `mcs_all_future_closure`: If `G(phi) in S` then, using derived G-distribution + axiom instances, `phi` follows at accessible future states. (But note: G is not directly an operator on the MCS level like box is -- this requires a different approach since the canonical model for temporal logic uses the linear order structure, not an accessibility relation.)

**Key difference from modal MCS**: The modal canonical model uses an accessibility relation `R S T iff forall psi, box(psi) in S -> psi in T`. For temporal logic over linear orders, the canonical model construction is fundamentally different:

- **Worlds**: Still MCS of the temporal derivation system
- **Linear order**: Defined on MCS via a temporal ordering relation
- **Witness conditions for Until/Since**: This is the critical temporal-specific content

**Until witness condition**: If `phi U psi in S` (S is MCS), then there must exist an MCS `T` "in the future of S" where `phi` holds and `psi` holds at all intermediate MCS. This requires:
1. Showing that `{chi | G(chi) in S} union {psi}` (or a suitable variant) is consistent
2. Extending to an MCS via Lindenbaum
3. Establishing the ordering relationship

**Since witness condition**: Symmetric to Until, looking to the past.

**The canonical linear order**: The standard approach for temporal logic completeness over linear orders constructs:
1. Take the set of all MCS as candidate worlds
2. Define an order on MCS (this is the hardest part)
3. Show the order is linear using the linearity axioms (BX7, BX7', BX11, BX11')
4. Prove witness lemmas for Until and Since using the enrichment and absorption axioms

The key axioms for establishing linearity are:
- **BX7** (linear_until): Linearity of Until
- **BX7'** (linear_since): Linearity of Since
- **BX11** (temp_linearity): `F(phi) and F(psi) -> F(phi and psi) or F(phi and F(psi)) or F(F(phi) and psi)`
- **BX11'** (temp_linearity_past): Past version

The enrichment axioms (BX13, BX13') and self-accumulation (BX5, BX5') / absorption (BX6, BX6') are critical for the Until/Since witness construction.

### 5.4 Soundness (`Metalogic/Soundness.lean`, ~350 lines)

**Strategy**: Prove that every derivable formula is valid over serial linear orders (the BX axioms are designed for `ValidSerial`, requiring `NoMaxOrder` and `NoMinOrder`).

**Structure**:
1. `axiom_sound`: Verify each of the 26 axiom constructors semantically. This is the bulk of the work:
   - 4 propositional axioms: Straightforward (same as modal)
   - 22 temporal axioms: Each requires a semantic argument over the linear order with `Satisfies`. Key challenges:
     - **BX7 (linear_until)**: Must use linearity of the order to case-split
     - **BX11 (temp_linearity)**: F(phi) and F(psi) on a linear order -- the witness times are comparable
     - **BX13 (enrichment_until)**: Combining Until with Since witnesses
     - **BX5 (self_accum_until)**: Showing the Until witness can be strengthened
     - **BX6 (absorb_until)**: Collapsing nested Until
     - **BX1 (serial_future/past)**: Requires `NoMaxOrder`/`NoMinOrder`

2. `soundness`: Structural induction on `DerivationTree`, 6 constructor cases:
   - `axiom`: `axiom_sound`
   - `assumption`: Context satisfaction
   - `modus_ponens`: Apply IH to both subderivations
   - `temporal_necessitation`: Universal quantification over all future times (using `all_future_iff`)
   - `temporal_duality`: Show satisfaction is preserved under `swap_temporal` (requires a lemma relating `Satisfies M t (swap_temporal phi)` to swapped temporal operators)
   - `weakening`: Context monotonicity

3. `soundness_derivable`: Empty-context specialization

**Temporal duality soundness lemma**: This is unique to temporal logic. Need to show:
```
Satisfies M t (swap_temporal phi) iff Satisfies (swap_model M) t phi
```
or equivalently, prove directly by induction on `phi` that if `phi` is valid on all serial linear orders, so is `swap_temporal phi`. The key insight: `swap_temporal` exchanges Until/Since, and on a linear order, the future and past are symmetric (the order on `D` and its reverse are both linear orders).

### 5.5 Completeness (`Metalogic/Completeness.lean`, ~450 lines)

This is the most complex module. The canonical model for temporal logic over linear orders follows Burgess (1982).

**Canonical model construction**:

1. **CanonicalWorld**: MCS of the temporal derivation system (same as modal)

2. **Canonical linear order on MCS**: Define `S <= T` iff `forall phi, G(phi) in S -> phi in T` (and the symmetric past condition). The linearity axioms BX7, BX7', BX11, BX11' are used to show this is a total order.

   Actually, the standard Burgess construction is more subtle. The canonical model for the BX system uses a quotient or a direct construction where worlds are MCS and the order is defined via:
   - `S < T` iff `{phi | G(phi) in S} subset T` and `{phi | H(phi) in T} subset S`

   This ordering must be shown to be:
   - Irreflexive (from the connectedness axioms BX4/BX4')
   - Transitive (from the distribution properties of G/H)
   - Total (from the linearity axioms BX7/BX11)

3. **Canonical valuation**: `v S p iff atom(p) in S` (same as modal)

4. **Truth lemma**: By structural induction on formula type:
   - `atom`: By definition
   - `bot`: `bot not in S` for any MCS
   - `imp`: Same pattern as modal (using implication_property and negation_complete)
   - `untl phi psi`: Forward direction uses the Until witness lemma. Reverse direction uses the definition of the canonical order and Until membership in MCS.
   - `snce phi psi`: Symmetric to Until.

5. **Completeness theorem**: Contrapositive -- if `phi` is not derivable, `{neg phi}` is consistent, extends to MCS, and the truth lemma shows `phi` is not satisfied at that world.

**Key technical challenges for temporal completeness**:

a) **Constructing the linear order**: The BX axioms are specifically designed to make this work. The enrichment axioms (BX13/BX13') allow us to build the order step by step. The linearity axioms (BX7/BX7'/BX11/BX11') ensure totality.

b) **Until/Since witness lemmas**: Showing that if `phi U psi in S`, there exists a future MCS `T` witnessing the event, with appropriate guard conditions on intermediate MCS. This requires:
   - BX10 (until_F): `phi U psi -> F(phi)` -- the event will happen
   - BX5 (self_accum): The Until strengthens itself
   - BX6 (absorb_until): Nested Until collapses
   - BX13 (enrichment): Combines current state with Until witness

c) **Seriality**: The canonical order has no endpoints (follows from BX1/BX1' -- serial_future/serial_past). These ensure `NoMaxOrder` and `NoMinOrder` on the canonical model.

d) **Nontriviality**: Need at least two distinct MCS. Follows from the existence of `top` and non-derivability of `bot`.

## 6. Proof Strategy Summary

### Phase 1: DerivationTree Setup (~100 lines)
- Add `height` function to existing `DerivationTree`
- Height lemmas for well-founded recursion
- `Deriv`, `Derivable` wrappers
- `temporalDerivationSystem` instance

### Phase 2: Deduction Theorem (~300 lines)
- Port modal deduction theorem pattern
- Handle 6 constructors (2 trivially impossible when context non-empty)
- `temporal_has_deduction_theorem` for generic MCS framework

### Phase 3: MCS Theory (~400 lines)
- Instantiate generic MCS properties
- Temporal-specific MCS properties
- Until/Since witness lemmas
- Linear order construction helpers

### Phase 4: Soundness (~350 lines)
- 26-axiom semantic verification (bulk of work)
- `swap_temporal` soundness lemma
- Soundness theorem by structural induction

### Phase 5: Completeness (~450 lines)
- Canonical world and model definition
- Canonical linear order construction and properties
- Truth lemma (5 formula cases)
- Completeness theorem

**Total estimated**: ~1,600 lines (slightly above the ~1,500 target due to the 26-axiom soundness proof)

## 7. Risk Assessment

### Medium Risk
- **Canonical linear order construction**: The key challenge. The BX axiom system is specifically designed for completeness over linear orders, but the formal Lean construction of the order and proof of its properties (total, serial) requires careful work with the axiom instances.
- **Until/Since witness lemmas**: These are technically demanding. The enrichment and absorption axioms must be used precisely.
- **26-axiom soundness**: Each axiom requires individual semantic verification. While conceptually straightforward, the 22 temporal axioms involve quantifier manipulation over linear orders that can be verbose in Lean.

### Low Risk
- **DerivationTree setup**: Direct port of modal pattern
- **Deduction theorem**: Direct port with one additional trivial case
- **Generic MCS instantiation**: Template from modal exists
- **Completeness outer structure**: Standard contrapositive argument

### Mitigation
- The existing `TemporalDerived` theorems (G/H distribution, etc.) provide ready-made derived facts that simplify the MCS and completeness proofs
- The generic MCS framework handles all the hard Zorn's-lemma machinery
- The `Satisfies` simp lemmas significantly simplify soundness proof obligations

## 8. File Plan

```
Cslib/Logics/Temporal/Metalogic/
  DerivationTree.lean   -- Height, Deriv, temporalDerivationSystem (~100 lines)
  DeductionTheorem.lean -- Deduction theorem for temporal BX (~300 lines)
  MCS.lean              -- MCS properties + temporal witness lemmas (~400 lines)
  Soundness.lean        -- Soundness over serial linear orders (~350 lines)
  Completeness.lean     -- Canonical model + truth lemma + completeness (~450 lines)

Cslib/Logics/Temporal/
  Metalogic.lean        -- Barrel import (~10 lines)
```

## 9. Import Dependencies

```
DerivationTree.lean
  <- Temporal.ProofSystem.Derivation
  <- Foundations.Logic.Metalogic.Consistency

DeductionTheorem.lean
  <- DerivationTree.lean

MCS.lean
  <- DeductionTheorem.lean

Soundness.lean
  <- DerivationTree.lean
  <- Temporal.Semantics.Validity

Completeness.lean
  <- MCS.lean
  <- Soundness.lean
```
