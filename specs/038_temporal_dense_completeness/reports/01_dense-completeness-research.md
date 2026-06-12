# Research Report: Dense Temporal Completeness (Task 38)

## 1. Executive Summary

This report covers research for proving dense temporal completeness: every formula valid on all dense serial linear orders is derivable in the Dense temporal proof system. The implementation requires:

1. Adding two dense axioms to `Axiom` (density + dense_indicator), with `minFrameClass` gating
2. FC-parameterized MCS infrastructure (derivability, consistency, Lindenbaum)
3. Dense soundness proofs for the two new axioms
4. A key lemma: Dense-MCS implies Base-MCS (enables reuse of existing chronicle construction)
5. A DenselyOrdered instance for the chronicle subtype (via limit C4 + dense_indicator)
6. The dense completeness theorem itself (contrapositive argument)

Estimated scope: ~400-600 lines across 3-4 files. No existing sorry-blocked dependencies.

## 2. Existing Infrastructure Analysis

### 2.1 Axiom System (`ProofSystem/Axioms.lean`)

Current state: 26 axiom constructors (4 propositional + 22 BX temporal), all mapped to `FrameClass.Base` by `minFrameClass`. The `FrameClass` type has `.Base`, `.Dense`, `.Discrete` with `Base <= Dense` and `Base <= Discrete`.

The two dense axioms to add match the bimodal versions at `Bimodal/ProofSystem/Axioms.lean:295-300`:

```lean
-- Density: G(G phi) -> G phi
| density (phi : Formula Atom) :
    Axiom (phi.allFuture.allFuture.imp phi.allFuture)

-- Dense indicator: neg U(top, bot) -- "no immediate successor"
| dense_indicator :
    Axiom (Formula.untl Formula.top Formula.bot).neg
```

Both gated to `.Dense` in `minFrameClass`.

**Impact**: Adding constructors to `Axiom` requires updating every `cases h_ax` match in the codebase. Key files affected:
- `Soundness.lean:axiom_sound` -- needs two new cases
- `Instances.lean` -- needs new `HasAxiom*` instances (if abstract classes exist)
- Anything that pattern-matches on `Axiom`

### 2.2 Derivation Trees (`Derivation.lean`)

Already parameterized by `fc : FrameClass`. Axioms gated by `h_fc : h.minFrameClass <= fc`. The `lift` function handles frame class monotonicity. **No changes needed.**

### 2.3 Derivability (`DerivationTree.lean`)

**Critical gap**: `Temporal.Deriv` and `Temporal.ThDerivable` are hardcoded to `FrameClass.Base`:

```lean
def Temporal.Deriv (Gamma : List (Formula Atom)) (phi : Formula Atom) : Prop :=
  Nonempty (DerivationTree FrameClass.Base Gamma phi)
```

Need FC-parameterized versions:

```lean
def Temporal.DerivFc (fc : FrameClass) (...) : Prop :=
  Nonempty (DerivationTree fc Gamma phi)

def Temporal.ThDerivableFc (fc : FrameClass) (phi : Formula Atom) : Prop :=
  Temporal.DerivFc fc [] phi

def temporalDerivationSystemFc (fc : FrameClass) : DerivationSystem (Formula Atom) where ...
```

### 2.4 MCS Infrastructure (`MCS.lean`, `CompletenessHelpers.lean`)

**Critical gap**: All MCS machinery is instantiated via `temporalDerivationSystem` (Base). Need FC-parameterized versions:

- `Temporal.SetConsistentFc fc Omega`
- `Temporal.SetMaximalConsistentFc fc Omega`  
- `temporal_lindenbaum_fc` -- extends consistent sets to MCS
- `temporal_closed_under_derivation_fc`
- `temporal_implication_property_fc`
- `temporal_negation_complete_fc`
- `theoremInMcsFc`
- `mcs_bot_not_mem_fc`, `mcs_neg_of_not_mem_fc`, `mcs_not_mem_of_neg_fc`

All are trivial wrappers around `Metalogic.SetMaximalConsistent.*` instantiated with `temporalDerivationSystemFc fc`.

### 2.5 Key Lemma: Dense-MCS implies Base-MCS

**Theorem**: `SetMaximalConsistentFc .Dense M -> Temporal.SetMaximalConsistent M`

**Proof sketch**:
1. Dense-consistent => Base-consistent (since every Base derivation is also a Dense derivation by frame class monotonicity: `Base <= Dense`)
2. Dense-MCS => negation complete (standard MCS property via deduction theorem)
3. For Base-maximality: if `phi not in M`, then `neg phi in M` (by negation completeness). So `insert phi M` contains both `phi` and `neg phi`. By `set_consistent_not_both` (which only uses MP and assumption), `insert phi M` is Base-inconsistent.
4. Combined: M is Base-consistent and Base-maximal = Base-MCS.

This lemma is essential: it allows feeding a Dense-MCS directly into the existing chronicle construction (which requires `Temporal.SetMaximalConsistent`).

### 2.6 Soundness

Current `axiom_sound` handles 26 base axioms over serial linear orders. For dense completeness, need:

**`density_sound`**: `G(G phi) -> G phi` valid on `DenselyOrdered`. Proof uses `exists_between`: given `neg(G phi)` witnessed at `s > t`, find `r` between `t` and `s` via density, then `neg(G phi)` at `r` from the `s` witness. (Matches bimodal `Soundness.lean:437-448`.)

**`dense_indicator_sound`**: `neg U(top, bot)` valid on `DenselyOrdered`. Proof: if `U(top, bot)` held at `t`, there's `s > t` with `top` at `s` and `bot` between. But density gives `r` between `t` and `s`, and `bot` at `r` is a contradiction. (Matches bimodal `Soundness.lean:430-435`.)

**`axiom_sound_dense`**: Master theorem for all 28 axioms at `FrameClass.Dense`. The 26 base cases delegate to existing `axiom_sound`; the 2 dense cases use the new lemmas.

### 2.7 Validity Definitions (`Validity.lean`)

`ValidDense` is already defined with `DenselyOrdered D` constraint. **No changes needed.**

### 2.8 Chronicle Construction (`Chronicle/`)

The chronicle construction builds a countermodel on `{x : Rat // x in limitDom A h_mcs}`. Already provides `LinearOrder`, `Nontrivial`, `NoMaxOrder`, `NoMinOrder`. 

**Missing**: `DenselyOrdered` instance.

**Key theorem `limit_satisfies_c4`** (already proved):
```
For all x < y in limitDom, if neg(untl eta xi) in limitF(x) and eta in limitF(y),
then exists z in limitDom with x < z < y and xi.neg in limitF(z).
```

### 2.9 DenselyOrdered for Chronicle Subtype

**Theorem**: If `A` is a Dense-MCS (hence also Base-MCS), then `ChronicleSubtype A h_mcs` is `DenselyOrdered`.

**Proof**: Given `x < y` in the chronicle subtype:
1. `limitF(x)` is a Base-MCS (by `limit_c0`).
2. Since `A` is Dense-MCS, `neg U(top, bot)` is Dense-derivable (it's the `dense_indicator` axiom).
3. By the Dense-MCS-implies-Base-MCS lemma, `A` is also a Base-MCS.
4. `neg U(top, bot)` is in `A = limitF(0)`.
5. We need `neg U(top, bot)` at `limitF(x)` -- this requires showing that Dense theorems propagate through the chronicle. Actually, we need a simpler argument.

**Simpler approach**: The dense_indicator `neg U(top, bot)` is a Dense theorem. Any Dense theorem is also a Base theorem when `Base <= Dense`... no, wait. A Dense axiom is NOT a Base axiom. `neg U(top, bot)` is derivable at `FrameClass.Dense` but NOT at `FrameClass.Base`.

However, `limitF(x)` for every `x` is a Base-MCS (by `limit_c0`). A Base-MCS contains all Base theorems but not necessarily Dense theorems. So `neg U(top, bot)` might NOT be in `limitF(x)`.

**This is the fundamental obstacle.** The chronicle construction produces Base-MCS at each point, even when started from a Dense-MCS. Dense axioms are not Base theorems, so they might not propagate.

**Revised approach**: Instead of trying to get DenselyOrdered from C4 + dense_indicator, we should use a different argument.

**Approach A: Direct density from Rat**

The subtype `{x : Rat // x in limitDom}` inherits DenselyOrdered from Rat IF limitDom is OrdConnected (i.e., if `x, z in limitDom` and `x < y < z`, then `y in limitDom`). But the limit domain is a countable scattered set of rationals -- it's NOT OrdConnected in general.

**Approach B: Prove chronicle density directly**

Given `x < y` in `limitDom`, we need to find `z` with `x < z < y` and `z in limitDom`. 

Consider the formula `U(top, top)` at `x`. Since `limitF(x)` is a Base-MCS:
- `F(top)` is in `limitF(x)` (seriality axiom + mcs_f_top_mem)
- By BX12: `F(top) -> U(top, top)`, so `U(top, top)` is in `limitF(x)`
- By `limit_satisfies_c5_weak`: there exists `y' > x` in `limitDom` with `top` at `y'`

But this gives us SOME `y' > x`, not necessarily `y' < y`.

For the specific Until formula `U(top, top)`, C5 actually gives:
```
exists y' in limitDom, x < y' /\ top in limitF(y') /\ 
  forall z in limitDom, x < z < y' -> top in limitF(z) /\ U(top,top) in limitF(z)
```

This gives a witness y' but not necessarily between x and y.

**Approach C: Use the negative Until C4 argument**

Actually, we can use `limit_satisfies_c4` with the NEGATED formula. For `neg U(top, bot)`:
- This is equivalent to `G(F(top))` (G of "not all-bot after me" = G of "there's something future")
- Wait, `neg U(top, bot) = neg(exists s > t, top(s) /\ forall r in (t,s), bot(r))`.
- `U(top, bot)` means: there exists a future point with no intermediate points satisfying anything (because bot is always false). In other words, there's an "immediate successor" in the temporal sense.
- `neg U(top, bot)` means: there is no immediate successor.

But `neg U(top, bot)` being in a Base-MCS is NOT guaranteed. It's only in Dense-MCS. The points of the chronicle are Base-MCS.

**Approach D: Modify chronicle construction for Dense**

The cleanest approach: build a Dense-specific chronicle construction where all point functions are Dense-MCS (not just Base-MCS). This requires:
1. The seed MCS is Dense-MCS
2. Point insertion creates Dense-MCS (using `temporal_lindenbaum_fc .Dense` instead of `temporal_lindenbaum`)
3. All chronicle conditions are preserved

This is a significant refactoring of the chronicle construction but follows the same logic.

**Approach E: The simplest correct approach**

Since the chronicle subtype is a subtype of `Rat` (which IS `DenselyOrdered`), and the limit domain is dense in itself (between any two limit points, the omega-chain inserts a new point), we need to prove this density property directly.

The key insight: for any `x < y` in `limitDom`, the chronicle construction processes ALL potential counterexamples including the one for `(x, top, bot, c4_forward)`. The C4 counterexample for `neg U(top, bot)` at `x` with `top` at `y` produces a new point between `x` and `y`.

But wait -- `neg U(top, bot)` is only in `limitF(x)` if `limitF(x)` is a Dense-MCS or if it's otherwise derivable. For Base-MCS, `neg U(top, bot)` is NOT necessarily a member.

However, we DON'T need every `limitF(x)` to contain `neg U(top, bot)`. We need: **the starting MCS `A` is a Dense-MCS, so `neg U(top, bot)` is in `A = limitF(0)`.**

For the completeness argument:
1. Start with Dense-MCS `A` containing `neg phi`.
2. `A` is also a Base-MCS (by Dense-MCS => Base-MCS lemma).
3. Build chronicle from `A` using existing Base construction.
4. Chronicle subtype has LinearOrder, Nontrivial, NoMaxOrder, NoMinOrder.
5. Need DenselyOrdered for the chronicle subtype.

For step 5, we can't get DenselyOrdered from the Base chronicle in general. But we know `A = limitF(0)` is a Dense-MCS and contains `neg U(top, bot)`.

For the completeness argument, we actually only need validity to fail. The base completeness theorem says: if `phi` is valid on all serial linear orders, then `phi` is Base-derivable. We want: if `phi` is valid on all DENSE serial linear orders, then `phi` is Dense-derivable.

The countermodel for the base case is the chronicle subtype, which is serial but not necessarily dense. For the dense case, we need a dense countermodel.

**Approach F: The bimodal pattern (correct approach)**

Looking more carefully at the bimodal dense completeness (`BXCanonical/Completeness/Dense.lean`), the strategy is:

1. Start with Dense-MCS `M`.
2. Case split on whether `box(neg U(top, bot))` (equivalently `box(F'T)`) is in `M`:
   - **Dense case**: `box(F'T) in M` means the box content "no immediate successor" holds everywhere. The countermodel is built on `Rat` via Cantor isomorphism (the bimodal has this but with a sorry).
   - **Non-dense case**: Impossible because `neg U(top, bot)` is a Dense axiom, so `G(neg U(top, bot))` = `box(neg U(top, bot))` is in every Dense-MCS.

In the temporal case (no box operator), the analog is:
1. Start with Dense-MCS `M`.
2. `neg U(top, bot)` is Dense-derivable (dense_indicator axiom).
3. By temporal necessitation, `G(neg U(top, bot))` is Dense-derivable.
4. So `G(neg U(top, bot))` is in `M`.
5. `G(neg U(top, bot))` propagates: for any `x` in the limit domain, if the future content of `A` includes `G(neg U(top, bot))`, then `neg U(top, bot)` is in `limitF(x)` for all `x > 0`.
6. For `x = 0`: `limitF(0) = A`, and `neg U(top, bot)` is in `A` (Dense axiom).
7. For `x > 0`: `x` is a successor of `0` in the chronicle, so `G(neg U(top, bot))` being in `limitF(0)` means `neg U(top, bot)` is in `limitF(x)`.
8. For `x < 0`: By temporal duality, `H(neg S(top, bot))` is also Dense-derivable and in `A`. Since the chronicle construction is symmetric, `neg S(top, bot)` propagates backward.

But this requires showing that `G(phi)` in `limitF(0)` implies `phi` in `limitF(x)` for `x > 0`. This is exactly what the r-relation / g-function / C2 condition gives us. The chronicle's C2 condition says the g-content between 0 and x contains all formulas from `limitF(0)` that should propagate, and the r-relation ensures the Guard formulas propagate.

Actually, this is more complex. Let me think again.

**The correct approach for temporal dense completeness**:

The chronicle construction starts with a Base-MCS `A`. If `A` is also a Dense-MCS, then `neg U(top, bot)` is in `A`. The chronicle's interval function `g(0, x)` for `x > 0` is defined to satisfy C2 (r3Relation from `f(0)` to `g(0,x)` to `f(x)`). The r-relation ensures:
- For `untl delta gamma in f(0)`: either `delta in g(0,x)` or `gamma in g(0,x) /\ untl delta gamma in g(0,x)`.

This doesn't directly force `neg U(top, bot)` into `g(0,x)` or `f(x)`.

**Better approach**: We don't need `neg U(top, bot)` at every point. We need the limit domain to be dense. This follows from: given `x < y` in the limit domain, we need `z` between them. 

Consider: the chronicle construction processes counterexamples for EVERY formula at EVERY point. For any `x < y` in the limit domain and the formula pair `(top, bot)` at point `x`, the counterexample `(x, y, top, bot, c4_forward)` asks: is `(untl top bot).neg in limitF(x)` and `top in limitF(y)`?

- `top in limitF(y)` is always true (all MCS contain top).
- `(untl top bot).neg in limitF(x)` is NOT always true for Base-MCS.

So this approach only works if `limitF(x)` contains `neg U(top, bot)`.

**Final correct approach: Re-parameterize the chronicle by frame class**

The cleanest solution is to generalize the chronicle construction to work with `fc`-MCS. The key insight is that the chronicle construction only uses Base-level axioms (seriality, enrichment, self-accumulation, absorption, linearity, BX12). It never uses Dense-specific axioms. So re-parameterizing is straightforward: replace `Temporal.SetMaximalConsistent` with `Temporal.SetMaximalConsistentFc fc` everywhere in the chronicle construction.

**But this has a subtlety**: the chronicle's point insertion uses `temporal_lindenbaum` to create new MCS points. If we're working with `fc = .Dense`, the new points would be Dense-MCS. And Dense-MCS satisfy `neg U(top, bot)`. So `limitF(x)` for all `x` would contain `neg U(top, bot)`. Then `limit_satisfies_c4` applied with `neg U(top, bot)` at `x` and `top` at `y` gives us the intermediate point `z`, proving DenselyOrdered.

However, re-parameterizing the entire chronicle construction is a large refactoring.

**The pragmatic correct approach: Avoid re-parameterization entirely**

There is a simpler way that avoids re-parameterizing the chronicle:

1. Build the chronicle from the Dense-MCS `A` using the existing Base construction (A is also Base-MCS by the Dense-MCS => Base-MCS lemma).
2. The chronicle subtype is a serial linear order (has LinearOrder, Nontrivial, NoMaxOrder, NoMinOrder).
3. We do NOT have DenselyOrdered for the chronicle subtype.
4. But we DON'T NEED DenselyOrdered for the chronicle subtype!

Here's why: the completeness theorem states `ValidDense phi -> ThDerivableFc .Dense phi`. The contrapositive is: if phi is not Dense-derivable, then phi is not ValidDense. "Not ValidDense" means there exists SOME dense serial linear order model where phi fails. We need to produce such a model.

Since the chronicle subtype is built on Rat (which IS DenselyOrdered), and the subtype may not be DenselyOrdered, we can instead use **Rat itself** as the domain. We define a valuation on ALL of Rat, not just the limit domain points.

**Approach G: Extend the chronicle model to all of Rat**

Define a TemporalModel on Rat (not just the subtype):
- For `x in limitDom`: `V(p)(x) := atom p in limitF(x)`
- For `x not in limitDom`: extend by some default (e.g., interpolation)

Then Rat with this model is a dense serial linear order. The truth lemma at limit domain points still holds (it only depends on the Until/Since semantics between domain points). Since `phi not in limitF(0) = A`, we have `not Satisfies model 0 phi`, contradicting ValidDense.

But the truth lemma for the extended model is tricky: the Until semantics involves ALL rationals between two points, not just those in the limit domain. So the truth lemma would not hold directly.

**Approach H: The Rat-based canonical model (the actual correct approach)**

The simplest correct approach, which avoids all the issues above:

The base completeness already builds a countermodel on `{x : Rat // x in limitDom}`. For dense completeness, we instead build a countermodel on **all of Rat** using a Cantor-style argument:

1. Start with Dense-MCS `A` (hence also Base-MCS).
2. Use the chronicle construction to get a countable dense suborder of Rat with MCS at each point.
3. Since each point's MCS contains `neg U(top, bot)` (if the chronicle is Dense-parameterized) or if we can extend the domain to be dense.
4. Define the model on all of Rat by extending the limit point function.

Actually, this is getting complicated. Let me re-examine the bimodal approach one more time.

**Re-reading bimodal Dense.lean**: The bimodal completeness has a `sorry` for exactly this issue (universe mismatch with `countermodel_dense`). The non-dense branch is eliminated but the dense branch countermodel construction is incomplete.

**The correct minimal approach for temporal dense completeness**:

Given the analysis, the simplest correct approach that avoids major refactoring is:

1. **Add dense axioms** to `Axioms.lean`.
2. **Add FC-parameterized MCS infrastructure** (thin wrappers).
3. **Prove Dense-MCS => Base-MCS** (key enabler).
4. **Prove dense soundness** (two new axiom cases + extension of `axiom_sound`).
5. **For dense completeness**: Use the fact that the chronicle subtype is built on Rat. Prove that when starting from a Dense-MCS, the chronicle limit domain is dense by showing it satisfies the `OrdConnected`-like property. Alternatively, prove `DenselyOrdered` for the subtype directly using the C4 condition + the fact that `neg U(top, bot)` is in the starting MCS A.

For step 5 in detail: Given `x < y` in the chronicle subtype:
- Case 1: `x.val = 0`. Then `limitF(0) = A` which is Dense-MCS, so `neg U(top, bot)` is in `limitF(0)`. `top in limitF(y)` (all MCS contain top). By `limit_satisfies_c4` with `xi = bot, eta = top`: exists `z` between `x` and `y` in limitDom with `bot.neg = top` at `z`. This `z` is our intermediate point.
- Case 2: `x.val != 0`. We need `neg U(top, bot)` at `limitF(x)`. Since `limitF(x)` is a Base-MCS, this is not guaranteed directly. But we can argue: `G(neg U(top, bot))` is in `A = limitF(0)`. For `x > 0`, there's a chain of chronicle points from 0 to x. The G-propagation through the r-relation ensures that `neg U(top, bot)` propagates from 0 to x.

Actually, the G-propagation argument works as follows. The r-relation `rRelation(f(0), g(0, x))` says: for `untl delta gamma in f(0)`, either `delta in g(0,x)` or `gamma in g(0,x) /\ untl delta gamma in g(0,x)`. And C3 says `g(0, x) subset f(z)` for `0 < z < x`.

But `G(neg U(top, bot))` in `f(0)` means `neg F(neg(neg U(top, bot)))` = `neg F(U(top, bot))`. This is about the non-existence of a future point where `U(top, bot)` holds. The G-propagation through the chronicle doesn't directly give us `neg U(top, bot)` at interior points.

**Alternative for Case 2**: For arbitrary `x < y` in limitDom, `limitF(x)` is a Base-MCS. `U(top, top)` is in `limitF(x)` (since `F(top)` is in every Base-MCS by seriality, and BX12 gives `F(top) -> U(top, top)`). By `limit_satisfies_c5_weak`, there exists `z > x` with `top` at `z` and `top` between. But we can't guarantee `z < y`.

Actually, `limit_satisfies_c5_strong` (if it exists) might give a stronger result:

Looking at the C5 condition:
```
forall x in dom, forall gamma delta,
  untl delta gamma in f(x) ->
  exists y in dom, x < y /\ delta in f(y) /\
    forall z in dom, x < z < y -> gamma in f(z) /\ untl delta gamma in f(z)
```

This gives a WITNESS `y` for the Until formula. The witness `y` might be arbitrarily far from `x`. We need a witness between `x` and some given `y'`.

**C4 is the right tool**: C4 says if `neg U(eta, xi)` is at `x` and `eta` is at `y`, then there's a point between with `neg xi`. We need `neg U(top, bot)` at `x`. So the problem reduces to: does `neg U(top, bot)` hold at `limitF(x)` for all `x` in the limit domain?

**Key realization**: We need to either:
(a) Re-parameterize the chronicle to produce Dense-MCS at each point, OR
(b) Show that `neg U(top, bot)` is a Base theorem (it's not), OR
(c) Find a different proof strategy that doesn't need DenselyOrdered for the subtype.

Option (c) is the bimodal approach: case-split on the "dense" formula's membership. In the temporal case without a box operator, the case split is:

- If `neg U(top, bot) in limitF(x)` for all x: use C4 to get DenselyOrdered.
- If `U(top, bot) in limitF(x)` for some x: this means there's an immediate successor from x, but we have a Dense-MCS at 0 with `neg U(top, bot)`.

Actually, the chronicle is built from A which is Base-MCS. The new points in the chronicle are also Base-MCS (created by temporal_lindenbaum). There's no guarantee they're Dense-MCS or contain `neg U(top, bot)`.

**Final recommendation: Re-parameterize chronicle by frame class (Approach D)**

Despite the refactoring cost, the cleanest approach is to re-parameterize the key parts of the chronicle construction by frame class. Specifically:

1. `limitDom`, `limitF`, `ChronicleSubtype`, etc. should take `fc : FrameClass` and `h_mcs : SetMaximalConsistentFc fc A`.
2. For `fc = .Dense`, all limit points are Dense-MCS.
3. `neg U(top, bot)` is in every Dense-MCS, so C4 gives DenselyOrdered.
4. For `fc = .Base`, everything is unchanged.

The re-parameterization is mostly mechanical: replace `Temporal.SetMaximalConsistent` with `Temporal.SetMaximalConsistentFc fc` throughout. The chronicle conditions C0-C5 remain the same (they only use Base axioms internally). The key change is that `temporal_lindenbaum` becomes `temporal_lindenbaum_fc fc` when creating new MCS points.

**However**, there's a subtlety: the r-relation and the point insertion logic uses specific Base axioms (self-accumulation, absorption, enrichment, etc.) in their proofs. These axioms have `minFrameClass = .Base <= .Dense`, so they're available at `.Dense` too. The proofs should go through unchanged when parameterized by `fc` as long as `fc >= .Base` (which is always true by `FrameClass.base_le`).

**Estimated refactoring cost**: The chronicle construction spans 8 files with ~3500 lines total. The re-parameterization is mostly search-and-replace of `Temporal.SetMaximalConsistent` with `Temporal.SetMaximalConsistentFc fc` and `temporalDerivationSystem` with `temporalDerivationSystemFc fc`. Most proofs should work unchanged because `FrameClass.base_le fc` gives `Base <= fc`, making all Base axioms available. Estimate: ~200 lines of changes spread across 8 files, plus ~200 lines of new FC-parameterized MCS infrastructure.

## 3. Recommended Architecture

### Phase 1: Dense Axioms (~50 lines)

**File**: `Cslib/Logics/Temporal/ProofSystem/Axioms.lean`

- Add `density` and `dense_indicator` constructors
- Update `minFrameClass` with two new Dense cases
- Update docstring (28 constructors, Layer 3: Density)

### Phase 2: FC-Parameterized Infrastructure (~200 lines)

**New file**: `Cslib/Logics/Temporal/Metalogic/DerivationTreeFc.lean`

- `Temporal.DerivFc`, `Temporal.ThDerivableFc`
- `temporalDerivationSystemFc`
- `temporal_has_deduction_theorem_fc` (should follow from existing pattern)

**New file**: `Cslib/Logics/Temporal/Metalogic/MCSFc.lean`

- `Temporal.SetConsistentFc`, `Temporal.SetMaximalConsistentFc`
- `temporal_lindenbaum_fc`
- `temporal_closed_under_derivation_fc`, `temporal_implication_property_fc`
- `temporal_negation_complete_fc`
- `theoremInMcsFc`
- `mcs_bot_not_mem_fc`, `mcs_neg_of_not_mem_fc`, `mcs_not_mem_of_neg_fc`
- **Key lemma**: `dense_mcs_implies_base_mcs`

### Phase 3: Dense Soundness (~100 lines)

**New file**: `Cslib/Logics/Temporal/Metalogic/DenseSoundness.lean`

- `density_axiom_sound`: `G(G phi) -> G phi` valid on DenselyOrdered
- `dense_indicator_sound`: `neg U(top, bot)` valid on DenselyOrdered
- `axiom_sound_dense`: all 28 axioms valid on dense serial linear orders
- `soundness_dense`: derivation tree soundness for Dense frame class
- Update existing `axiom_sound` in Soundness.lean to handle new constructors (2 cases that reject `h_fc` since these axioms have `minFrameClass = .Dense > .Base`)

### Phase 4: Chronicle FC Re-parameterization (~200 lines of changes)

**Modified files** (search-and-replace + minor adjustments):
- `Chronicle/ChronicleTypes.lean`: parameterize DCS, r-relation by fc
- `Chronicle/RRelation.lean`: fc parameter
- `Chronicle/PointInsertion.lean`: use `temporal_lindenbaum_fc`
- `Chronicle/CounterexampleElimination.lean`: fc parameter
- `Chronicle/ChronicleConstruction.lean`: fc parameter throughout omega-chain
- `Chronicle/Frame.lean`: fc parameter
- `Chronicle/ChronicleToCountermodel.lean`: fc parameter + DenselyOrdered instance
- `Chronicle/TruthLemma.lean`: fc parameter

Alternative: Instead of modifying existing files, create wrapper functions that instantiate with `fc = .Dense` and add the DenselyOrdered instance. This is less invasive.

### Phase 5: Dense Completeness (~150 lines)

**New file**: `Cslib/Logics/Temporal/Metalogic/DenseCompleteness.lean`

```lean
theorem neg_consistent_of_not_derivable_dense
    {phi : Formula Atom} (h_not : not (Temporal.ThDerivableFc .Dense phi)) :
    Temporal.SetConsistentFc .Dense ({Formula.neg phi}) := ...

theorem completeness_dense [Denumerable (Formula Atom)] {phi : Formula Atom}
    (h_valid : ValidDense phi) :
    Temporal.ThDerivableFc .Dense phi := by
  by_contra h_not_deriv
  have h_cons := neg_consistent_of_not_derivable_dense h_not_deriv
  obtain ⟨M, hM_sup, hM_mcs⟩ := temporal_lindenbaum_fc h_cons
  have h_neg_in_M := hM_sup (Set.mem_singleton _)
  have h_phi_not_M := mcs_not_mem_of_neg_fc hM_mcs h_neg_in_M
  -- M is Dense-MCS, hence also Base-MCS
  have h_base_mcs := dense_mcs_implies_base_mcs hM_mcs
  -- Build chronicle from Base-MCS M
  let D := Chronicle.ChronicleSubtype M h_base_mcs  -- or fc-parameterized version
  let model := Chronicle.chronicleModel M h_base_mcs
  let t0 := Chronicle.chronicleZero M h_base_mcs
  -- Need: DenselyOrdered D (from Dense-MCS + C4)
  -- If fc-parameterized: all limit points are Dense-MCS, neg U(top,bot) everywhere, C4 gives density
  have h_sat := h_valid D model t0
  have h_mem := (Chronicle.chronicle_truth_lemma M h_base_mcs t0 phi).mp h_sat
  rw [Chronicle.limit_f_zero] at h_mem
  exact h_phi_not_M h_mem
```

## 4. Dependencies and Blockers

### No external blockers

The temporal dense completeness is independent of:
- Bimodal dense completeness (task 36 -- has universe sorry)
- Any other incomplete tasks

### Internal dependencies within this task

```
Phase 1 (Axioms) <- Phase 2 (FC Infrastructure) <- Phase 3 (Soundness)
                                                 <- Phase 4 (Chronicle FC) <- Phase 5 (Completeness)
```

## 5. Risk Assessment

### Low risk
- Phase 1 (Axiom additions): straightforward pattern matching
- Phase 3 (Dense soundness): direct proofs using `exists_between`
- Phase 5 (Completeness theorem): follows established pattern

### Medium risk  
- Phase 2 (FC infrastructure): mostly boilerplate but Dense-MCS => Base-MCS lemma needs careful argument
- Phase 4 (Chronicle FC re-parameterization): might require non-trivial adjustments if proofs depend on `FrameClass.Base` specifically

### Key technical risk
The main risk is Phase 4. If the chronicle construction proofs have implicit dependencies on `FrameClass.Base` that don't generalize, the re-parameterization might be more complex than estimated. Mitigation: test early by adding `fc` parameter to just `ChronicleConstruction.lean` and verifying `lake build`.

## 6. Alternative Approach: Without Chronicle Re-parameterization

If Phase 4 proves too costly, an alternative is:

1. Prove `dense_mcs_implies_base_mcs` (still needed).
2. Build the chronicle from the Base-MCS version of the Dense-MCS.
3. Instead of proving DenselyOrdered for the chronicle subtype, observe that between any two chronicle points there exist rationals (since Rat is dense), and define an extended model on ALL of Rat by:
   - For `x in limitDom`: valuation from `limitF(x)`
   - For `x not in limitDom`: valuation from the "interval function" `limitG(a, b)` where `a, b` are the nearest limit domain points around `x`
4. Prove the truth lemma for this extended Rat model.

This avoids re-parameterizing the chronicle but requires defining `limitG` (the interval function for the limit) and proving the truth lemma for the extended model. This is likely MORE work than re-parameterization.

## 7. Answers to Key Questions

**Q: What dense-specific axioms are needed?**
A: Two: `density` (`G(G phi) -> G phi`) and `dense_indicator` (`neg U(top, bot)`). Both match the bimodal versions exactly.

**Q: Can the existing chronicle construction be reused directly?**
A: Partially. The chronicle is built on Rat (dense) but produces Base-MCS at each point. For DenselyOrdered, we need Dense-MCS at each point, requiring FC re-parameterization of the Lindenbaum step inside the chronicle. The construction logic (C0-C5 conditions) doesn't change.

**Q: How does minFrameClass need to change?**
A: Add `| density _ => .Dense` and `| dense_indicator => .Dense`. The existing `| _ => .Base` catch-all for base axioms remains.

**Q: What soundness lemmas are needed?**
A: Two: `density_axiom_sound` and `dense_indicator_sound`. Both use `exists_between` from `DenselyOrdered`. Plus an updated `axiom_sound_dense` master theorem.

**Q: Is there existing infrastructure for dense axiom typeclasses?**
A: No. The `Foundations/Logic/ProofSystem.lean` has no `HasAxiomDensity` or `HasAxiomDenseIndicator` typeclasses. The `FrameConditions.lean` has `DenseTemporalFrame` but it's for the bimodal semantics with `AddCommGroup` (not applicable to pure temporal logic). New abstract typeclasses could be added but aren't required for this task.

**Q: What is the relationship between base and dense completeness?**
A: Dense completeness reuses the chronicle construction with FC-parameterized MCS. The proof structure is: contrapositive -> Dense-MCS -> (Dense-MCS implies Base-MCS) -> chronicle on Rat -> DenselyOrdered for chronicle (from Dense-MCS + C4) -> ValidDense gives phi in M -> contradiction.
