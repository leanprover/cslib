# Task 49: Temporal Truth Lemma and Completeness Assembly -- Research Report

## 1. Overview

Task 49 fills the single `sorry` at line 416 of `Completeness.lean` by:
1. Building a `TemporalModel` from the chronicle limit construction
2. Proving the truth lemma (Satisfies <-> MCS membership) by formula induction
3. Applying the validity hypothesis to derive a contradiction

The chronicle infrastructure (tasks 46-48) provides all the raw materials.
No bimodal prior art (`ChronicleToCountermodel*.lean`) transfers -- those files
use `Formula.box`, FMCS/BFMCS, modal_k_dist, S5 box-stability, and algebraic
parametric completeness, none of which exist in temporal logic.

## 2. Existing Infrastructure Inventory

### 2.1 Completeness.lean (418 lines)

**Already proved:**
- MCS helper lemmas: `mcs_mp_axiom`, `mcs_top_mem`, `mcs_f_top_mem`, `mcs_p_top_mem`
- G/H-transitivity: `mcs_g_trans`, `mcs_h_trans`
- F/P-idempotency: `mcs_ff_imp_f`, `mcs_pp_imp_p`
- DNE in MCS: `mcs_dne`
- Past/future subset duality: `past_of_future_subset`, `future_of_past_subset`
- CanonicalWorld type, canonical_acc
- Truth lemma G forward/reverse, H reverse
- Future/past successor existence
- `neg_consistent_of_not_derivable`
- `mcs_g_and_g_neg_absurd`

**The sorry (line 416):** Inside `theorem completeness`, after obtaining MCS M with
neg(phi) in M and phi not in M. Needs to construct a countermodel and derive False.

### 2.2 ChronicleConstruction.lean (1435 lines)

**Key results available:**
- `chronicle_model_exists`: Given MCS A, produces `(D : Set Rat, f : Rat -> Set (Formula Atom))` with:
  - `0 in D`, `f(0) = A`
  - `forall x in D, SetMaximalConsistent (f x)` (C0)
  - C5 forward: `untl eta xi in f(x) -> exists y in D, x < y /\ eta in f(y)`
  - C5' backward: `snce eta xi in f(x) -> exists y in D, y < x /\ eta in f(y)`
- `limit_dom`, `limit_f`, `limit_g` definitions
- `limit_c0`: all limit domain points map to MCS
- `limit_f_zero`: `limit_f(0) = A`
- `zero_mem_limit_dom`: `0 in limit_dom`
- `limit_forward_G`: G(phi) in limit_f(x) and x < y implies phi in limit_f(y)
- `limit_backward_H`: H(phi) in limit_f(x) and y < x implies phi in limit_f(y)
- `limit_satisfies_c5_strong`: Full C5a with guard (Until with intermediate formula propagation)
- `limit_satisfies_c5'_strong`: Mirror for Since
- `limit_satisfies_c4`: Generalized C4a (counterexample elimination between any x < y)
- `limit_satisfies_c4'`: Mirror
- `limit_F_resolution`: F(phi) in limit_f(x) -> exists y > x in limit_dom
- `limit_P_resolution`: P(phi) in limit_f(x) -> exists y < x in limit_dom
- `limit_c3`: C3 at the limit (interval function decomposition)
- `limit_c3_interval_subset_point`: limit_g(x,z) subset limit_f(y) for x < y < z

### 2.3 Other Temporal Metalogic Files

- `MCS.lean`: `mcs_g_witness`, `mcs_h_witness`, `temporal_lindenbaum`, `temporal_implication_property`, `temporal_negation_complete`, `mcs_mem_iff_neg_not_mem`
- `TemporalContent.lean`: `g_content`, `h_content` definitions
- `WitnessSeed.lean`: `g_content_subset_implies_h_content_reverse`, `h_content_subset_implies_g_content_reverse`
- `Frame.lean`: `TPoint`, `t_le`, witness lemmas (used by chronicle, not directly needed for completeness)
- `Soundness.lean`: Soundness theorem (imported by Completeness.lean)

### 2.4 Semantics

- `TemporalModel D Atom`: structure with `valuation : D -> Atom -> Prop`
- `Satisfies M t phi`: recursive truth at a point
  - `.atom p` -> `M.valuation t p`
  - `.bot` -> `False`
  - `.imp phi psi` -> `Satisfies M t phi -> Satisfies M t psi`
  - `.untl phi psi` -> `exists s > t, Satisfies M s phi /\ forall r, t < r -> r < s -> Satisfies M r psi`
  - `.snce phi psi` -> `exists s < t, Satisfies M s phi /\ forall r, s < r -> r < t -> Satisfies M r psi`
- Note: Formula has 5 constructors: `atom`, `bot`, `imp`, `untl`, `snce`
- G, H, F, P, neg, top, and, or are all abbreviations/derived

## 3. Countermodel Design

### 3.1 The Type D

Use `D := {x : Rat // x in limit_dom A h_mcs}` (subtype of Rat restricted to limit_dom).

**Properties to prove on D:**

1. **LinearOrder**: Inherited from Rat via `Subtype.linearOrder` (automatic).

2. **Nontrivial**: limit_dom contains 0 (by `zero_mem_limit_dom`), and by `limit_F_resolution` applied to F(top) in limit_f(0), there exists y > 0 in limit_dom. So limit_dom has at least two elements.

3. **NoMaxOrder**: For any x in limit_dom, F(top) in limit_f(x) (since top is a theorem and serial_future gives top -> F(top)). By `limit_F_resolution`, there exists y > x in limit_dom. Hence no maximum.

4. **NoMinOrder**: Mirror using P(top) and `limit_P_resolution`.

### 3.2 The TemporalModel

```lean
def chronicle_model (A : Set (Formula Atom)) (h_mcs : ...) : TemporalModel D Atom where
  valuation := fun t p => Formula.atom p in limit_f A h_mcs t.val
```

### 3.3 The Truth Lemma

**Statement**: For all `t : D` (i.e., `t.val in limit_dom`) and all `phi : Formula Atom`:
```
Satisfies chronicle_model t phi <-> phi in limit_f A h_mcs t.val
```

**Proof by structural induction on phi:**

**Case atom p**: `Satisfies M t (atom p) <-> M.valuation t p <-> (atom p) in limit_f(t)` by definition.

**Case bot**: `Satisfies M t bot <-> False`. Also `bot not_in limit_f(t)` by `mcs_bot_not_mem` (since limit_c0 gives MCS at t). Both are False, so iff holds.

**Case imp phi psi**: `Satisfies M t (imp phi psi) <-> (Satisfies M t phi -> Satisfies M t psi)`. By IH, this is `(phi in f(t) -> psi in f(t))`. By MCS implication property (`temporal_implication_property` + contrapositive), this is `(phi.imp psi) in f(t)`.

**Case untl phi psi** (phi = event, psi = guard):

*Forward* (membership -> satisfies):
- Assume `untl phi psi in f(t)`.
- By `limit_satisfies_c5_strong`: exists `y in limit_dom`, `t < y`, `phi in f(y)`, and `psi in limit_g(t,y)` (i.e., forall `w in limit_dom`, `t < w < y -> psi in f(w)`).
- The witness s = y (as subtype element) satisfies: `t < s` in D, `Satisfies M s phi` (by IH), and forall `r : D` with `t < r < s`, `psi in f(r.val)` hence `Satisfies M r psi` (by IH).

*Backward* (satisfies -> membership):
- Assume exists `s : D` with `t < s`, `Satisfies M s phi`, and forall `r` between, `Satisfies M r psi`.
- By IH: `phi in f(s.val)` and forall `r : D` between t and s, `psi in f(r.val)`.
- Suppose for contradiction `untl phi psi not_in f(t)`. Then `neg(untl phi psi) in f(t)`.
- By `limit_satisfies_c4`: since `neg(untl phi psi) in f(t)` and `phi in f(s)` and `t < s`, there exists `z in limit_dom` with `t < z < s` and `psi.neg in f(z)`.
- But z is in limit_dom, so z (as subtype element) satisfies `t < z < s`, hence `Satisfies M z psi` by hypothesis, hence `psi in f(z)` by IH.
- Contradiction: both `psi` and `psi.neg` in f(z), violating MCS consistency.

**Case snce phi psi**: Mirror of untl using `limit_satisfies_c5'_strong` and `limit_satisfies_c4'`.

### 3.4 Closing the Sorry

1. From `h_not_deriv`, get MCS M with `neg(phi) in M` (already in Completeness.lean).
2. Apply chronicle limit construction to M, getting `limit_dom` and `limit_f`.
3. Build D = subtype of limit_dom, prove LinearOrder/Nontrivial/NoMaxOrder/NoMinOrder.
4. Build `chronicle_model : TemporalModel D Atom`.
5. Prove truth lemma.
6. Apply `h_valid D chronicle_model (0 : D)` to get `Satisfies chronicle_model 0 phi`.
7. By truth lemma, `phi in limit_f(0) = M`.
8. Contradiction with `phi not_in M`.

## 4. File Structure

### 4.1 New Files Needed

**`Cslib/Logics/Temporal/Metalogic/Chronicle/TruthLemma.lean`** (~300-500 lines)
- Import: ChronicleConstruction, Completeness (for MCS helpers), Satisfies
- Define: `ChronicleSubtype` (the D type), `chronicle_valuation`, `chronicle_model`
- Prove: `NoMaxOrder`, `NoMinOrder`, `Nontrivial` on ChronicleSubtype
- Prove: `truth_lemma`: `Satisfies chronicle_model t phi <-> phi in limit_f t.val`
- This is the main new file.

**`Cslib/Logics/Temporal/Metalogic/Chronicle/ChronicleToCountermodel.lean`** (~100-200 lines)
- Import: TruthLemma
- Prove: `chronicle_countermodel`: given MCS A with neg(phi) in A, produce a countermodel
- Package the countermodel theorem in a form ready for Completeness.lean

### 4.2 Modified Files

**`Cslib/Logics/Temporal/Metalogic/Completeness.lean`**
- Add import of ChronicleToCountermodel
- Replace the sorry at line 416 with a call to the countermodel theorem

### 4.3 Estimated Lines

- TruthLemma.lean: 300-500 lines (truth lemma is the core; 5 cases by induction)
- ChronicleToCountermodel.lean: 100-200 lines (packaging)
- Completeness.lean changes: ~20-30 lines (replacing sorry)
- **Total: 420-730 lines**

## 5. Dependencies and Prerequisites

### 5.1 Required [Denumerable (Formula Atom)] Instance

The chronicle construction requires `[Denumerable (Formula Atom)]` (for counterexample enumeration). The completeness theorem currently does NOT have this constraint. The sorry replacement must add this variable constraint or work around it.

Looking at the completeness theorem signature:
```lean
variable {Atom : Type*}
theorem completeness {phi : Formula Atom} ...
```

The chronicle construction uses `[Denumerable (Formula Atom)]`. This instance needs to be assumed somewhere. Options:
1. Add it to the completeness theorem itself
2. Add it as a variable in the file
3. Use it locally within the sorry replacement

Option 1 is cleanest -- add `[Denumerable (Formula Atom)]` to the completeness theorem's hypotheses. This is a standard assumption in completeness proofs for countable languages.

### 5.2 The `t_le_refl` Sorry in Frame.lean

Frame.lean has `t_le_refl` sorry'd. This is NOT needed for the completeness proof. The TPoint/t_le infrastructure was built for the chronicle construction (tasks 46-48) and is used internally there. The completeness proof uses `limit_forward_G` and `limit_backward_H` directly, not t_le.

### 5.3 Import Chain

```
Completeness.lean
  <- Chronicle/ChronicleToCountermodel.lean (new)
    <- Chronicle/TruthLemma.lean (new)
      <- Chronicle/ChronicleConstruction.lean (existing)
      <- Semantics/Satisfies.lean (existing)
```

Note: Completeness.lean already imports MCS.lean and Soundness.lean. It does NOT currently import any Chronicle files. The new import of ChronicleToCountermodel.lean brings in the entire chronicle chain.

### 5.4 Circular Import Risk

Frame.lean already imports Completeness.lean (for MCS helpers). If Completeness.lean imports ChronicleToCountermodel.lean -> TruthLemma.lean, and TruthLemma.lean tries to import Frame.lean, we'd have a cycle. 

**Resolution**: TruthLemma.lean should NOT import Frame.lean. It should import ChronicleConstruction.lean directly (which does not import Completeness.lean or Frame.lean). The truth lemma uses `limit_*` functions from ChronicleConstruction.lean, not TPoint/t_le from Frame.lean.

Let me verify: Does ChronicleConstruction.lean import Completeness.lean?
- ChronicleConstruction.lean imports ChronicleTypes.lean, RRelation.lean, PointInsertion.lean, CounterexampleElimination.lean
- None of these import Completeness.lean (they import MCS.lean, TemporalContent.lean, etc.)

So the import chain is safe: Completeness.lean -> ChronicleToCountermodel.lean -> TruthLemma.lean -> ChronicleConstruction.lean, and there's no cycle.

## 6. Literature Proof Structure

### Source: Burgess 1982, Claim 2.11 + Completeness conclusion

**Strategy**: Contrapositive completeness via chronicle countermodel construction.

### Step Map

1. **Consistent set extension** (lines 400-404, already done): If phi is not derivable, {neg phi} is consistent, extend to MCS M. -- [Burgess Section 2, setup]
2. **Chronicle construction** (tasks 46-48, done): From MCS M, build omega-chain chronicle with limit domain D, limit function f, satisfying C0-C5. -- [Burgess Section 2, Claim 2.9-2.10]
3. **Model extraction** (new, TruthLemma.lean): Build TemporalModel on D with valuation V(p,t) := (atom p) in f(t). -- [Burgess Claim 2.11, setup]
4. **Truth lemma** (new, TruthLemma.lean): Prove Satisfies M t phi <-> phi in f(t) by structural induction on phi. -- [Burgess Claim 2.11]
   - 4a. atom/bot/imp: Standard MCS properties
   - 4b. untl (forward): C5-strong gives witness with guard
   - 4c. untl (backward): C4 gives contradicting intermediate point
   - 4d. snce: Mirror of untl
5. **Contradiction** (new, Completeness.lean): Apply h_valid to get phi in f(0) = M, contradicting phi not in M. -- [Burgess, completeness conclusion]

### Dependencies
- Step 3 depends on Step 2
- Step 4 depends on Steps 2, 3
- Step 5 depends on Steps 1, 3, 4

### Potential Formalization Challenges
- **Step 3 (model extraction)**: Need to prove NoMaxOrder/NoMinOrder on limit_dom subtype. Requires showing F(top)/P(top) in every MCS (seriality axioms) + limit_F_resolution/limit_P_resolution. Should be straightforward.
- **Step 4b (Until forward)**: The strong C5 gives guard as `psi in limit_g(t,y)`, which by definition means `psi in limit_f(w)` for all `w in limit_dom` between t and y. Since our D IS limit_dom (subtype), this directly gives what we need. Key insight: using limit_dom subtype avoids the density issue entirely.
- **Step 4c (Until backward)**: The C4 condition requires `neg(untl phi psi) in f(t)` and `phi in f(s)`. We get z between t and s with `psi.neg in f(z)`. We need the IH at z (psi in f(z) iff Satisfies M z psi). Since z is in limit_dom, it's a valid point in our subtype D, so the IH applies.
- **Step 5 (Denumerable constraint)**: The chronicle construction requires `[Denumerable (Formula Atom)]`. Must add this to the completeness theorem signature.

## 7. Key Technical Insight

The crucial design decision is **using limit_dom as the model domain D** (via subtype), rather than using all of Rat and trying to transport via Cantor isomorphism.

**Why this works**: The completeness theorem only requires `LinearOrder + Nontrivial + NoMaxOrder + NoMinOrder` on D. It does NOT require `DenselyOrdered`. The limit_dom subtype satisfies all four conditions. Using it directly means:

1. The truth lemma quantifiers (`forall s > t`, `exists s > t`) range over exactly the limit_dom points.
2. The `limit_g` definition (`forall y in limit_dom, x < y < z -> phi in limit_f(y)`) matches the Until/Since guard condition perfectly.
3. No Cantor isomorphism needed (unlike the bimodal case which needed it for density in the discrete case).

**Why the bimodal case was harder**: The bimodal completeness quantified over `TaskModel` which required `DenselyOrdered` or `IsSuccArchimedean` (density/discreteness split). The temporal completeness only needs serial linear orders, so the subtype approach works directly.

## 8. Risk Assessment

| Risk | Likelihood | Mitigation |
|------|-----------|------------|
| Circular imports | Low | TruthLemma imports ChronicleConstruction, not Frame.lean |
| Missing Until backward | Medium | C4 condition proved in ChronicleConstruction; need careful IH application |
| Denumerable constraint | Low | Standard; add to completeness theorem signature |
| Universe level issues | Low | `D : Type` in ValidSerial matches subtype universe |
| Heartbeat limits | Medium | May need set_option maxHeartbeats for truth lemma induction |
| t_le_refl sorry in Frame.lean | None | Not used by completeness proof |

## 9. Bimodal Prior Art Assessment

### BXCanonical/TruthLemma.lean (223 lines): ~70% structural transfer

The bimodal truth lemma has the same 5+2 cases (atom/bot/imp/G/H/Until/Since + box). The temporal version drops the box case entirely. The G/H/Until/Since cases have the same logical structure but use temporal-specific constructs (`limit_forward_G` vs `bx_G_forward`, `limit_satisfies_c5_strong` vs `bx_until_eventuality_resolution`).

**Transfers**: Overall proof architecture, case structure, IH pattern.
**Does not transfer**: Box case, modal equivalence, FMCS/BFMCS references.

### BXCanonical/CanonicalModel.lean (771 lines): ~0% direct transfer

This file builds FMCS Int (FC-parametric MCS chains), BFMCS (bimodal families), modal witnesses, Cantor isomorphisms for dense/discrete cases. None of this is relevant to temporal logic which has no modal operator and no density/discreteness case split.

### ChronicleToCountermodelBasic.lean (1170 lines): ~0% transfer

Dense pipeline with Cantor isomorphism to Rat, FMCS construction, ParametricCompleteness invocation. All bimodal-specific.

### ChronicleToCountermodel.lean (229 lines): ~0% transfer

Gap elimination, IsSuccArchimedean, discrete pipeline, BFMCS on Int. All bimodal-specific.

## 10. Recommendations

1. **Create TruthLemma.lean first** with the truth lemma and all supporting definitions (ChronicleSubtype, chronicle_model, NoMaxOrder/NoMinOrder/Nontrivial instances).

2. **Create ChronicleToCountermodel.lean** as a thin wrapper packaging the countermodel construction for Completeness.lean.

3. **Modify Completeness.lean** to add `[Denumerable (Formula Atom)]` and replace the sorry.

4. **Do NOT attempt to fix t_le_refl sorry** in Frame.lean -- it's unrelated to the completeness proof.

5. **Do NOT use Cantor isomorphism** -- the subtype approach is simpler and sufficient.
