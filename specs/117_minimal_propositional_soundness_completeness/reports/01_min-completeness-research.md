# Research Report: Minimal Propositional Soundness and Completeness

**Task**: 117
**Date**: 2026-06-11
**Status**: Research findings ready for planning

## Executive Summary

Minimal propositional logic (Johansson 1937) has only two axiom schemata -- implyK and implyS -- with no ex falso quodlibet (EFQ). This requires a fundamentally different canonical model construction from intuitionistic logic: worlds are *deductively closed sets* (theories) without a consistency requirement, and `bot_forces w = (Proposition.bot in w.val)` is a genuine predicate rather than trivially False.

The intuitionistic Lindenbaum infrastructure (IntLindenbaum.lean) is hardcoded to `IntPropAxiom` and cannot be directly reused. A new `MinLindenbaum.lean` must be created with Min-specific versions of the deductive closure, cut lemma, and implication witness. The implication witness proof is simpler for minimal logic (no EFQ needed) but requires dropping the consistency hypothesis from the DCCS definition.

Soundness is straightforward: 2 axiom cases instead of 3, same proof structure.

## Research Question 1: How much of IntLindenbaum uses EFQ?

### EFQ-Dependent Components (CANNOT reuse for Min)

| Component | Lines | EFQ Usage |
|-----------|-------|-----------|
| `int_neg_phi_imp_psi` | 79-94 | Explicitly uses `.efq psi` to derive `[neg phi] |- phi -> psi` |
| `int_neg_phi_imp_psi_deriv` | 97-99 | Wrapper for above |
| `int_imp_witness` | 244-265 | Calls `int_neg_phi_imp_psi_deriv` at line 257 |
| `int_theorems_dccs` | 289-324 | Uses `lift_int_to_cl` which matches on `.efq` |
| `IntDCCS` | 47-51 | Uses `PropSetConsistent IntPropAxiom S` (consistency is the issue, not EFQ directly) |

### EFQ-Independent Components (use only implyK + implyS, but hardcoded to IntPropAxiom)

| Component | Lines | Notes |
|-----------|-------|-------|
| `int_deriv_from_closure_to_S` | 109-136 | Uses DT with int_h_implyK/int_h_implyS only |
| `int_deriv_imp_of_union` | 144-198 | Uses DT and deductionWithMem with implyK/implyS only |
| `int_deductive_closure` | 203-206 | Definition only |
| `int_subset_deductive_closure` | 209-213 | Trivial |
| `int_deductive_closure_dccs_closed` | 216-221 | Trivial delegation |
| `int_deductive_closure_consistent` | 224-230 | Needs consistency hypothesis |
| `int_deductive_closure_is_dccs` | 233-237 | Assembles consistency + closure |
| `int_dccs_bot_not_mem` | 55-60 | Uses only assumption rule |
| `int_dccs_imp_property` | 63-74 | Uses only MP |

### Verdict

All infrastructure is hardcoded to `IntPropAxiom`. The EFQ-independent components need Min-specific copies with `MinPropAxiom` substituted. The EFQ-dependent components need fundamentally different proofs or replacements. Parameterizing IntLindenbaum over `Axioms` would be a larger refactor and is out of scope for this task.

## Research Question 2: The Minimal Canonical Model

### Why IntDCCS Does Not Work for Minimal Logic

`IntDCCS S` requires `PropSetConsistent IntPropAxiom S`, which means `bot not in S`. If we define `MinDCCS` analogously with `PropSetConsistent MinPropAxiom S`, then `bot not in S` for every world (since `[bot] |- bot` by assumption). This means `bot_forces w = (bot in w.val) = False` for all worlds, collapsing minimal semantics to intuitionistic semantics. Since MinPropAxiom is strictly weaker than IntPropAxiom, this would prove too much.

### Correct Approach: Deductively Closed Sets (Theories)

For minimal logic, worlds are **deductively closed sets without a consistency requirement**:

```lean
def MinTheory (S : Set (PL.Proposition Atom)) : Prop :=
  forall (L : List (PL.Proposition Atom)) (phi : PL.Proposition Atom),
    (forall x in L, x in S) -> (propDerivationSystem MinPropAxiom).Deriv L phi -> phi in S
```

Key properties:
- `bot` CAN be in a MinTheory (representing worlds where falsum is "true")
- `bot_forces w = (Proposition.bot in w.val)` is a genuine predicate
- The ordering is set inclusion (preserved from intuitionistic case)
- `bot_forces` is upward-closed: if `bot in w` and `w <= w'`, then `bot in w'` (immediate from subset ordering)

### Canonical Model Structure

```
MinCanonicalWorld Atom := { S : Set (PL.Proposition Atom) // MinTheory S }

Preorder: S <= T iff S.val ⊆ T.val

min_canonical_val w p := Proposition.atom p in w.val
  -- upward-closed by subset ordering

min_bot_forces w := Proposition.bot in w.val
  -- upward-closed by subset ordering
```

## Research Question 3: Truth Lemma Differences

### Intuitionistic Truth Lemma (existing)

```
int_truth_lemma S phi : IForces int_canonical_val (fun _ => False) S phi <-> phi in S.val
```

Bot case: `IForces ... bot = False`, and `bot not in S.val` (by consistency), so `False <-> False`.

### Minimal Truth Lemma (needed)

```
min_truth_lemma S phi : IForces min_canonical_val min_bot_forces S phi <-> phi in S.val
```

Bot case: `IForces ... bot = min_bot_forces S = (bot in S.val)`, so the iff is `Iff.rfl`. **Simpler than intuitionistic!**

Atom case: `IForces ... (atom p) = min_canonical_val S p = (atom p in S.val)`, so `Iff.rfl`. Same as intuitionistic.

Imp case: Same structure as intuitionistic. Forward direction uses `min_imp_witness`. Backward direction uses deductive closure (imp property of MinTheory).

### Comparison

| Case | Intuitionistic | Minimal |
|------|---------------|---------|
| atom | `Iff.rfl` | `Iff.rfl` |
| bot | `False <-> bot not in S` (uses `int_dccs_bot_not_mem`) | `Iff.rfl` (trivial!) |
| imp (forward) | Uses `int_imp_witness` (needs EFQ) | Uses `min_imp_witness` (no EFQ needed) |
| imp (backward) | Uses `int_dccs_imp_property` | Uses `min_theory_imp_property` |

## Research Question 4: Implication Witness Without EFQ

### Intuitionistic Approach (requires EFQ)

Given IntDCCS S with `phi -> psi not in S`:
1. Show `S ∪ {phi}` is consistent (uses EFQ: if inconsistent, get `neg phi in S`, then compose with EFQ to get `phi -> psi in S`, contradiction)
2. Take T = deductive closure of `S ∪ {phi}`
3. T is a DCCS (consistent + closed)

### Minimal Approach (no EFQ needed)

Given MinTheory S with `phi -> psi not in S`:
1. Take T = min_deductive_closure (S ∪ {phi}) -- **no consistency check needed!**
2. T is a MinTheory (deductively closed by construction)
3. phi in T (by closure of S ∪ {phi})
4. psi not in T:
   - Assume psi in T, so exists L ⊆ S ∪ {phi} with L |- psi
   - By `min_deriv_imp_of_union`: exists L' ⊆ S with L' |- phi -> psi
   - Since S is a MinTheory (deductively closed): phi -> psi in S
   - Contradiction with phi -> psi not in S

**Key insight**: The minimal implication witness is structurally simpler because it does not need to prove consistency of `S ∪ {phi}`. The deductive closure is always well-defined regardless of consistency.

### Formal Statement

```lean
theorem min_imp_witness {S : Set (PL.Proposition Atom)}
    (h_theory : MinTheory S) {phi psi : PL.Proposition Atom}
    (h_not : phi.imp psi not in S) :
    exists T : Set (PL.Proposition Atom),
      S ⊆ T ∧ MinTheory T ∧ phi in T ∧ psi not in T
```

## Research Question 5: MinSoundness Design

### Axiom Soundness

Only 2 cases vs. 3 for intuitionistic:

```lean
theorem min_axiom_sound {phi : PL.Proposition Atom}
    (h_ax : MinPropAxiom phi) : MValid phi
```

- **implyK**: `phi -> (psi -> phi)`. Same proof as intuitionistic case. Uses `iforces_persistence` with `v_uc` AND `bf_uc` (since we have arbitrary bot_forces, we need both).
- **implyS**: `(phi -> (psi -> chi)) -> ((phi -> psi) -> (phi -> chi))`. Same proof using transitivity of <=.
- **No efq case**: This is the whole point -- minimal logic has no EFQ axiom.

### Soundness Theorem

```lean
theorem min_soundness
    {Gamma : List (PL.Proposition Atom)} {phi : PL.Proposition Atom}
    (d : DerivationTree MinPropAxiom Gamma phi)
    {World : Type v} [Preorder World]
    (val : World -> Atom -> Prop)
    (bot_forces : World -> Prop)
    (v_uc : forall {w w' : World} (p : Atom), w <= w' -> val w p -> val w' p)
    (bf_uc : forall {w w' : World}, w <= w' -> bot_forces w -> bot_forces w')
    (w : World)
    (h_ctx : forall psi, psi in Gamma -> IForces val bot_forces w psi) :
    IForces val bot_forces w phi
```

Structure: Same 4-case match as `int_soundness`. The key difference is that `val` and `bot_forces` are BOTH parameters (not `bot_forces = fun _ => False`).

## Research Question 6: MinCompleteness Proof Strategy

### Starting World

```
W0 = { psi | Derivable MinPropAxiom psi }
```

This is a MinTheory because:
- If L ⊆ W0 and L |- phi, then each element of L is derivable from empty context. By compilation/cut, phi is derivable from empty context, so phi in W0.
- This requires `min_deriv_from_closure_to_S` (Min-specific version of `int_deriv_from_closure_to_S`).

### Consistency of MinPropAxiom

We need: `not (Derivable MinPropAxiom Proposition.bot)`.

Proof approach: lift MinPropAxiom derivations to IntPropAxiom via `MinPropAxiom.toIntProp`, then use `int_consistent`:

```lean
noncomputable def lift_min_to_int {Gamma} {phi}
    (d : DerivationTree MinPropAxiom Gamma phi) :
    DerivationTree IntPropAxiom Gamma phi

theorem min_consistent :
    not (Derivable MinPropAxiom Proposition.bot) :=
  fun h => int_consistent (lift h)
```

### Completeness Proof

```lean
theorem min_completeness {phi : PL.Proposition Atom}
    (h_valid : MValid phi) : Derivable MinPropAxiom phi := by
  by_contra h_not_deriv
  let W0 : MinCanonicalWorld Atom :=
    ⟨{psi | Derivable MinPropAxiom psi}, min_theorems_theory⟩
  have h_not_forced : ¬ IForces min_canonical_val min_bot_forces W0 phi := by
    intro h; exact h_not_deriv ((min_truth_lemma W0 phi).mp h)
  have h_forced : IForces min_canonical_val min_bot_forces W0 phi :=
    h_valid (MinCanonicalWorld Atom) min_canonical_val min_bot_forces
      (fun {_ _} p hw hv => min_canonical_val_upward_closed p hw hv)
      (fun {_ _} hw hbf => min_bot_forces_upward_closed hw hbf)
      W0
  exact h_not_forced h_forced
```

## File Structure Recommendation

### File 1: `Cslib/Logics/Propositional/Metalogic/MinSoundness.lean`

```
imports: Kripke, Derivation
definitions:
  - min_axiom_sound (2 cases)
  - min_soundness (4-case match on DerivationTree)
  - min_soundness_derivable (wrapper)
estimated lines: ~80
```

### File 2: `Cslib/Logics/Propositional/Metalogic/MinLindenbaum.lean`

```
imports: DeductionTheorem, MCS (for PropSetConsistent -- used in consistency proof)
definitions:
  - min_h_implyK, min_h_implyS (helper hypotheses)
  - MinTheory (deductively closed, no consistency)
  - min_theory_imp_property (MP closure)
  - min_deriv_from_closure_to_S (compilation lemma)
  - min_deriv_imp_of_union (cut lemma)
  - min_deductive_closure (deductive closure definition)
  - min_subset_deductive_closure
  - min_deductive_closure_is_theory
  - min_imp_witness (implication witness, NO EFQ)
  - lift_min_to_int (derivation lifting)
  - min_consistent (consistency via lifting)
  - min_theorems_theory ({psi | Derivable MinPropAxiom psi} is a MinTheory)
estimated lines: ~250
```

### File 3: `Cslib/Logics/Propositional/Metalogic/MinCompleteness.lean`

```
imports: Kripke, MinSoundness, MinLindenbaum
definitions:
  - MinCanonicalWorld (subtype of MinTheory)
  - Preorder instance
  - min_canonical_val, min_bot_forces
  - Upward closure proofs
  - min_truth_lemma (3 cases: atom, bot, imp)
  - min_completeness
  - min_soundness_completeness (biconditional)
estimated lines: ~120
```

## Critical Implementation Notes

1. **MinTheory vs IntDCCS**: MinTheory has NO consistency requirement. This is the key structural difference. It means `bot ∈ S` is possible, which is essential for `bot_forces w = (bot ∈ w.val)` to be a meaningful predicate.

2. **Deduction theorem reuse**: The `deductionTheorem` and `deductionWithMem` in DeductionTheorem.lean are already parameterized over `Axioms` with explicit `h_implyK`/`h_implyS`. They can be called directly with `min_h_implyK`/`min_h_implyS`. Similarly, `prop_has_deduction_theorem` is parameterized.

3. **iforces_persistence reuse**: The `iforces_persistence` theorem in Kripke.lean is already parameterized over arbitrary `v_uc` and `bf_uc`. It works directly for minimal semantics.

4. **Universe polymorphism**: The completeness theorem needs `MValid.{u, u}` (same universe for World and Atom) to match the canonical model construction, following the pattern of `int_completeness`.

5. **Import structure**: MinSoundness imports Kripke + Derivation (no Lindenbaum). MinLindenbaum imports DeductionTheorem. MinCompleteness imports both MinSoundness and MinLindenbaum.

## Tactic Survey Results

The proofs in this task are primarily structural (pattern matching on inductive types, set membership reasoning). Expected tactic usage:

| Proof Component | Primary Tactics | Notes |
|----------------|-----------------|-------|
| min_axiom_sound | intro, exact, le_trans | Same structure as int_axiom_sound |
| min_soundness | match, exact, le_refl | Same structure as int_soundness |
| MinTheory properties | intro, apply, simp, exact | Set membership |
| min_deriv_from_closure_to_S | induction, obtain, exact | List induction, same as Int version |
| min_deriv_imp_of_union | obtain, by_cases, simp | Same as Int version |
| min_imp_witness | refine, exact, intro | Simpler than Int (no consistency sub-proof) |
| min_truth_lemma | constructor, intro, exact, by_contra | Bot case is Iff.rfl (trivial) |
| min_completeness | by_contra, exact | Same structure as int_completeness |

## Risk Assessment

| Risk | Likelihood | Mitigation |
|------|-----------|------------|
| MinTheory definition issues | Low | Well-understood mathematically |
| min_imp_witness proof difficulty | Low | Simpler than Int version (no EFQ/consistency) |
| Universe issues in completeness | Medium | Follow int_completeness pattern exactly |
| Compilation lemma complexity | Medium | Direct copy from Int with MinPropAxiom substituted |
| Import/dependency cycles | Low | Clean dependency chain: DT -> MinLindenbaum -> MinCompleteness |
