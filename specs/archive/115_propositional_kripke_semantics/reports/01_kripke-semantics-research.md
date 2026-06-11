# Research Report: Propositional Kripke Semantics (Task 115)

**Task**: Define propositional Kripke semantics with parameterized forcing function
**Date**: 2026-06-11
**Status**: Research complete

## Literature Proof Structure

**Source**: CZ (Chagrov-Zakharyaschev) Section 2.2 (lines 1564-1642 of `specs/literature/modal_logic.md`)
**Strategy**: Inductive definition of forcing + persistence by structural induction on formulas

### Step Map

1. **Intuitionistic Kripke frame**: (W, R) where R is a partial order (reflexive, transitive, antisymmetric) -- CZ Section 2.2, line 1568-1574
2. **Valuation**: Map V : Atom -> UpW (upward-closed subsets of W) -- CZ line 1577-1582
3. **Forcing relation** (inductive on formula structure):
   - atom: (M, x) |= p iff x in V(p)
   - and: (M, x) |= A /\ B iff (M,x)|=A and (M,x)|=B
   - or: (M, x) |= A \/ B iff (M,x)|=A or (M,x)|=B
   - imp: (M, x) |= A -> B iff for all y with xRy, (M,y)|=A implies (M,y)|=B
   - bot: (M, x) |/= bot (intuitionistic: never forced)
   -- CZ lines 1596-1618
4. **Persistence (Proposition 2.1)**: If x |= phi and xRy then y |= phi, by induction on phi -- CZ line 1627-1630
5. **Validity**: phi valid in frame F iff phi true in all models on F, for all worlds -- CZ lines 1634-1641
6. **Int = {phi : phi valid in all intuitionistic frames}** -- CZ line 1697-1699

### Dependencies
- Step 3 depends on Steps 1 and 2
- Step 4 depends on Step 3 (persistence uses the forcing definition)
- Step 5 depends on Steps 1, 2, 3
- Step 6 depends on Step 5

### Potential Formalization Challenges
- **Step 1**: CZ says "partial order" but antisymmetry is never used in the persistence proof or soundness/completeness. A `Preorder` suffices and is more general.
- **Step 3**: PL.Proposition has only `atom | bot | imp` (and/or/neg are derived via abbreviations). The forcing definition only needs 3 cases, not 5. The derived connectives inherit their semantics automatically.
- **Step 3 (bot)**: For minimal logic, bot_forces must be a parameter. CZ does not discuss minimal Kripke semantics, but the standard approach treats bot as an atom with upward-closed valuation.
- **Step 4**: The persistence proof for `imp` is automatic from universal quantification over accessible worlds (transitivity handles the step).

## Research Findings

### Q1: Standalone vs. Reuse Modal.Model

**Recommendation: Define a standalone propositional Kripke structure.**

Reasons:
1. `Modal.Model` bundles relation and valuation but uses `v : World -> Atom -> Prop` with no upward-closure constraint. The intuitionistic/minimal Kripke model requires `IsUpperSet` on the valuation sets.
2. `Modal.Satisfies` handles `.box` which PL.Proposition lacks. We cannot directly reuse `Modal.Satisfies`.
3. The critical difference: intuitionistic implication forces universally over all accessible worlds (`forall y, R x y -> ...`), whereas modal implication is a simple function type. Modal.Satisfies defines `imp` as `Satisfies m w phi1 -> Satisfies m w phi2` (local), not the Kripke-style universal one.
4. `PL.Proposition.toModal` embeds into `Modal.Proposition`, but Modal.Satisfies interprets `imp` classically (locally). The intuitionistic forcing interprets `imp` relationally (universally over R-successors).

The task description says "reusing Modal.Model", but the semantic interpretation is fundamentally different. We should define a lightweight `KripkeModel` structure that captures what we need:
- A `World` type with `Preorder` instance
- A valuation `v : World -> Atom -> Prop` with upward-closure
- A `bot_forces : World -> Prop` parameter (also upward-closed)

### Q2: Definition of IForces (Forcing Parameterized by bot_forces)

```lean
/-- Forcing relation for propositional Kripke semantics, parameterized by `bot_forces`.
- Intuitionistic instantiation: `bot_forces = fun _ => False`
- Minimal instantiation: `bot_forces` is an arbitrary upward-closed predicate -/
def IForces [Preorder World]
    (v : World → Atom → Prop) (bot_forces : World → Prop)
    (w : World) : PL.Proposition Atom → Prop
  | .atom p => v w p
  | .bot => bot_forces w
  | .imp φ ψ => ∀ w', w ≤ w' → IForces v bot_forces w' φ → IForces v bot_forces w' ψ
```

Key design points:
- Uses `Preorder World` with `w ≤ w'` instead of an explicit relation `R`
- `bot` case is `bot_forces w` (parameterized)
- `imp` case universally quantifies over all `w' ≥ w` (the key difference from classical/modal semantics)

### Q3: Persistence Proof (iforces_persistence)

**Theorem**: If `IForces v bf w φ` and `w ≤ w'`, then `IForces v bf w' φ`.

**Proof by structural induction on `φ`**:
- **atom p**: Need `v w p -> v w' p` when `w ≤ w'`. This requires upward-closure of `v`: `∀ p, IsUpperSet {w | v w p}`, equivalently `∀ w w' p, w ≤ w' → v w p → v w' p`.
- **bot**: Need `bot_forces w -> bot_forces w'` when `w ≤ w'`. This requires upward-closure of `bot_forces`: `IsUpperSet {w | bot_forces w}`, equivalently `∀ w w', w ≤ w' → bot_forces w → bot_forces w'`.
- **imp φ ψ**: If `∀ u, w ≤ u → IForces v bf u φ → IForces v bf u ψ` and `w ≤ w'`, then for all `u` with `w' ≤ u`, we have `w ≤ u` by transitivity, so the hypothesis gives us what we need. **No inductive hypothesis needed for this case** -- it's automatic from transitivity.

The persistence proof requires two hypotheses:
1. `v_uc : ∀ p, IsUpperSet {w | v w p}` (valuation upward-closure)
2. `bf_uc : IsUpperSet {w | bot_forces w}` (bot_forces upward-closure)

Alternatively, we can express these more concretely:
1. `v_uc : ∀ {w w'} (p : Atom), w ≤ w' → v w p → v w' p`
2. `bf_uc : ∀ {w w'}, w ≤ w' → bot_forces w → bot_forces w'`

**Recommendation**: Use the concrete formulation for easier proof automation. We can provide lemmas connecting to `IsUpperSet` if needed later.

### Q4: Definitions of IValid and MValid

```lean
/-- A formula is intuitionistically valid (IValid) if it is forced at every world
    in every intuitionistic Kripke model (where bot is never forced). -/
def IValid (φ : PL.Proposition Atom) : Prop :=
  ∀ (World : Type*) [Preorder World] (v : World → Atom → Prop),
    (∀ p, IsUpperSet {w | v w p}) →
    ∀ w, IForces v (fun _ => False) w φ

/-- A formula is minimally valid (MValid) if it is forced at every world
    in every minimal Kripke model (where bot_forces is upward-closed). -/
def MValid (φ : PL.Proposition Atom) : Prop :=
  ∀ (World : Type*) [Preorder World] (v : World → Atom → Prop)
    (bot_forces : World → Prop),
    (∀ p, IsUpperSet {w | v w p}) →
    IsUpperSet {w | bot_forces w} →
    ∀ w, IForces v bot_forces w φ
```

Note: `IValid` is a special case of `MValid` where `bot_forces = fun _ => False`.

### Q5: Instantiation for Intuitionistic vs Minimal

- **Intuitionistic**: `IForces v (fun _ => False)` -- bot is never forced
- **Minimal**: `IForces v bot_forces` where `bot_forces` is an arbitrary upward-closed `World -> Prop`

The parameterization by `bot_forces` cleanly unifies both semantics. When `bot_forces = fun _ => False`, `IForces v bf w .bot = False`, matching the intuitionistic clause "(M, x) |/= bot".

### Q6: Frame Conditions -- Preorder vs PartialOrder

**Recommendation: Use `Preorder World` (not `PartialOrder World`).**

Reasons:
1. CZ says "partial order" (reflexive + transitive + antisymmetric), but antisymmetry is **never used** in:
   - The persistence proof (only uses transitivity for the imp case)
   - Soundness proofs for intuitionistic/minimal axioms
   - The completeness proof (canonical model construction gives a preorder that is made into a partial order only for aesthetic reasons)
2. Using `Preorder` is strictly more general -- every result proved for preorders automatically holds for partial orders.
3. Mathlib's `Preorder` gives us `LE` for `IsUpperSet`, plus `le_refl` and `le_trans`.
4. If specific results need antisymmetry later, they can add `[PartialOrder World]` as a stronger hypothesis.
5. The existing modal codebase uses unbundled `Std.Refl` and `IsTrans`, but since propositional Kripke semantics always needs both (it's the defining condition), bundling as `Preorder` is cleaner and idiomatic.

### Q7: Relationship to Bivalent Evaluate

`Evaluate` from `Semantics/Basic.lean` is the classical truth-value semantics:
```lean
def Evaluate (v : Valuation Atom) : PL.Proposition Atom → Prop
  | .atom x => v x
  | .bot => False
  | .imp a b => Evaluate v a → Evaluate v b
```

The connection: `Evaluate v φ` is equivalent to `IForces (fun _ => v) (fun _ => False) () φ` on the single-world frame `World = Unit` with the trivial preorder. This follows CZ's observation (line 1623-1626): "an intuitionistic model on the frame containing only a single point is in essence the same as the classical model."

This semantic coherence theorem is deferred to task 118 (integration).

## Recommended File Structure

### File: `Cslib/Logics/Propositional/Semantics/Kripke.lean`

```
module

import Cslib.Logics.Propositional.Defs
import Mathlib.Order.Defs.PartialOrder     -- for Preorder
import Mathlib.Order.Defs.Unbundled        -- for IsUpperSet
import Mathlib.Data.Set.Basic              -- for Set membership

namespace Cslib.Logic.PL

section KripkeSemantics

-- Core definitions
structure KripkeModel (World : Type*) (Atom : Type*) [Preorder World] where
  v : World → Atom → Prop
  bot_forces : World → Prop
  v_upward_closed : ∀ {w w'} (p : Atom), w ≤ w' → v w p → v w' p
  bf_upward_closed : ∀ {w w'}, w ≤ w' → bot_forces w → bot_forces w'

-- Forcing relation (recursive on formula structure)
def IForces [Preorder World]
    (v : World → Atom → Prop) (bot_forces : World → Prop)
    (w : World) : PL.Proposition Atom → Prop
  | .atom p => v w p
  | .bot => bot_forces w
  | .imp φ ψ => ∀ w', w ≤ w' → IForces v bot_forces w' φ → IForces v bot_forces w' ψ

-- Persistence theorem
theorem iforces_persistence [Preorder World]
    {v : World → Atom → Prop} {bot_forces : World → Prop}
    (v_uc : ∀ {w w'} (p : Atom), w ≤ w' → v w p → v w' p)
    (bf_uc : ∀ {w w'}, w ≤ w' → bot_forces w → bot_forces w')
    {w w' : World} (hw : w ≤ w') {φ : PL.Proposition Atom}
    (hf : IForces v bot_forces w φ) : IForces v bot_forces w' φ

-- Validity definitions
def IValid (φ : PL.Proposition Atom) : Prop := ...
def MValid (φ : PL.Proposition Atom) : Prop := ...

end KripkeSemantics
end Cslib.Logic.PL
```

## Design Decisions Summary

| Decision | Choice | Rationale |
|----------|--------|-----------|
| Reuse Modal.Model? | No -- standalone | Modal imp is local; intuitionistic imp is universal over R-successors |
| Frame constraint | `Preorder World` | Antisymmetry never needed; more general; gives LE for IsUpperSet |
| Bundled vs unbundled | `Preorder` typeclass (bundled) | Always need both refl+trans; cleaner than two unbundled classes |
| Valuation upward-closure | Hypothesis on IForces/persistence | Not built into IForces itself; required where needed |
| bot_forces parameter | `World -> Prop` argument to IForces | Clean parameterization: `fun _ => False` for intuitionistic |
| KripkeModel structure? | Yes -- bundles v, bot_forces, and upward-closure proofs | Convenient for soundness/completeness; IForces is unbundled for flexibility |
| Derived connectives | Not separate cases in IForces | PL.Proposition has only atom/bot/imp; and/or/neg are abbrevs that reduce |
| Namespace | `Cslib.Logic.PL` | Consistent with existing propositional modules |

## Downstream Impact

### Task 116 (Intuitionistic Soundness/Completeness)
Will use `IValid` and prove:
- Soundness: If `HilbertInt ⊢ φ` then `IValid φ`
- Completeness: If `IValid φ` then `HilbertInt ⊢ φ`

Key: efq (`bot -> φ`) is sound under intuitionistic semantics because `IForces v (fun _ => False) w .bot = False`, so the premise is always false.

### Task 117 (Minimal Soundness/Completeness)
Will use `MValid` and prove:
- Soundness: If `HilbertMin ⊢ φ` then `MValid φ`
- Completeness: If `MValid φ` then `HilbertMin ⊢ φ`

Key: efq is NOT an axiom of HilbertMin, and NOT valid under MValid (since bot can be forced).

### Task 118 (Integration)
Will prove the semantic coherence theorem connecting `Evaluate` and `IForces` on single-world frames.

## Tactic Survey Results

Since this is primarily a definitions task, the main proof is `iforces_persistence`. Expected tactic profile:

| Goal | Tactic | Expected Result | Notes |
|------|--------|-----------------|-------|
| atom case persistence | exact v_uc | success | Direct from hypothesis |
| bot case persistence | exact bf_uc | success | Direct from hypothesis |
| imp case persistence | intro u hu hfu; exact hf u (le_trans hw hu) hfu | success | Transitivity of LE |
| Full persistence | induction phi with... | success | 3-case structural induction |

The proof should be approximately 10-15 lines total.

## Risk Assessment

- **Low risk**: The definitions are standard and well-understood.
- **Low risk**: Persistence proof is straightforward 3-case induction.
- **Medium risk**: Ensuring derived connective lemmas (and_iff, or_iff, neg_iff) work correctly through the abbreviation unfolding. These are convenience lemmas, not blockers.
- **No sorry expected**: All definitions and proofs are elementary.
