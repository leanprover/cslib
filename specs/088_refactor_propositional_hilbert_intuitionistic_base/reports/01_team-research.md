# Research Report: Task #88

**Task**: Refactor propositional Hilbert system to intuitionistic base with uniform extension architecture
**Date**: 2026-06-10
**Mode**: Team Research (4 teammates)

## Summary

All four researchers converge on a three-level typeclass hierarchy (MinimalHilbert → IntuitionisticHilbert → ClassicalHilbert) as the recommended architecture. The existing `HasAxiom*` mixin pattern is already well-suited; the refactoring is primarily in the bundled class layer. The FormalizedFormalLogic/Foundation project validates this approach at scale. The blast radius is manageable (~15 files, 4.5% of the codebase). The key risk is the Lukasiewicz conjunction encoding, which makes conjunction/disjunction elimination inherently classical.

## Key Findings

### 1. The Current Architecture Is 90% Ready

The existing fine-grained `HasAxiom*` typeclasses (individual axiom classes per axiom) already provide the atoms for an intuitionistic refactoring. The only problem is in the **bundled layer**: `PropositionalHilbert` bundles all four axioms (ImplyK, ImplyS, EFQ, Peirce) into one class, and everything extends it. The fix is to split this bundle into three levels.

### 2. Three-Level Hierarchy: Minimal → Intuitionistic → Classical

All teammates agree on this structure, which mirrors the ND system's `Theory.MPL/IPL/CPL`:

```lean
class MinimalHilbert (S : Type*) [HasBot F] [HasImp F] [InferenceSystem S F]
    extends ModusPonens S (F := F),
            HasAxiomImplyK S (F := F),
            HasAxiomImplyS S (F := F)

class IntuitionisticHilbert (S : Type*) [HasBot F] [HasImp F] [InferenceSystem S F]
    extends MinimalHilbert S (F := F),
            HasAxiomEFQ S (F := F)

class ClassicalHilbert (S : Type*) [HasBot F] [HasImp F] [InferenceSystem S F]
    extends IntuitionisticHilbert S (F := F),
            HasAxiomPeirce S (F := F)
```

**Why three levels, not two**: `MinimalHilbert` captures the purely implicational fragment. All combinators (`imp_trans`, `identity`, `b_combinator`, `flip`, `app1`, `app2`, `pairing`, `dni`, `contrapose_imp`, `contraposition`) are valid at this level — they use only K, S, and MP, never EFQ or Peirce. This enables maximum theorem reuse.

### 3. Theorem Stratification Is Clean

Concrete analysis of which theorems require which axiom level:

| Level | Theorems | Files |
|-------|----------|-------|
| **Minimal** | `imp_trans`, `identity`, `b_combinator`, `flip`, `app1`, `app2`, `pairing`, `dni`, `combine_imp_conj`, `contrapose_imp`, `contraposition`, `iff_intro` | `Combinators.lean` |
| **Intuitionistic** | `efq_axiom` | `Core.lean` (one theorem) |
| **Classical** | `peirce_axiom`, `double_negation`, `raa`, `efq_neg`, `rcp`, `lce_imp`, `rce_imp`, `classical_merge`, De Morgan laws | `Core.lean`, `Connectives.lean` |

The dependency chain for classical constructs is clear: all classical theorems trace back through 5 roots — `peirce_axiom`, `double_negation`, `lce_imp`, `rce_imp`, `classical_merge`.

### 4. The Lukasiewicz Conjunction Problem (Critic Finding)

The Lukasiewicz encoding defines conjunction as `φ ∧ ψ := ¬(φ → ¬ψ) = ((φ → (ψ → ⊥)) → ⊥)`. Extracting components (`lce_imp`: `φ ∧ ψ → φ`, `rce_imp`: `φ ∧ ψ → ψ`) requires double negation elimination, making conjunction elimination **classically valid only** with this encoding.

This does NOT block the refactoring — it simply means:
- Conjunction/disjunction elimination rules are correctly classified as classical
- The intuitionistic base has `⊥` and `→` only, with no derived connective elimination
- A future task could add primitive `HasAnd`/`HasOr` connectives for richer intuitionistic reasoning

### 5. FormalizedFormalLogic/Foundation Validates This Approach

The Foundation project (~1,378 commits) uses the same three-level hierarchy (`Minimal → Int → Cl`) and confirms it scales to 20+ logics. Their key architectural difference: axioms are `Set (Formula α)` rather than inductive types, and logic extension is set union. Their `Cl extends Minimal` (not `Int`) directly, using `HasAxiomDNE`.

For cslib, the linear chain `Cl extends Int extends Min` is simpler and mirrors the ND system. The Foundation approach of `Cl extends Min` is an alternative worth noting but not recommended for this refactoring.

### 6. `HasAxiomDNE` Is Dead Code

`HasAxiomDNE` is declared in `ProofSystem.lean` but never used anywhere. `PropositionalHilbert` uses `HasAxiomPeirce`. This should be resolved: either adopt DNE as the classical axiom (more standard, Foundation's choice) or remove the dead declaration. Recommendation: keep both declarations, use Peirce in `ClassicalHilbert` (matches current usage), but add a proof that Peirce implies DNE and vice versa.

### 7. MCS Framework Is Logic-Agnostic

The Lindenbaum's lemma and MCS machinery uses classical reasoning in the **metatheory** (Lean's `Classical.propDecidable`, `by_contra`) but does NOT require classical axioms in the **object logic**. An intuitionistic `DerivationSystem` instantiation works. The MCS theory applies to any logic with modus ponens and weakening.

### 8. Blast Radius: ~15 Files (4.5%)

| Category | Files | Impact |
|----------|-------|--------|
| Foundation definitions | 1 | `ProofSystem.lean` — split `PropositionalHilbert` |
| Foundation theorems | 5 | `Combinators`, `Core`, `Connectives`, `Modal/Basic`, `Modal/S5` |
| Propositional instances | 2 | `Propositional/ProofSystem/Instances.lean`, `BigConj.lean` |
| Temporal instances | 2 | `Temporal/ProofSystem/Instances.lean`, `PropositionalHelpers.lean` |
| Bimodal instances | 3 | `Bimodal/ProofSystem/Instances.lean`, `Bimodal/Theorems/Propositional/` |
| Other | 2 | `Theorems.lean` (aggregator), `Perpetuity/Helpers.lean` |

Total: 15 of 336 Lean files (~4.5%). The deduction theorem proofs are NOT affected (they pattern-match on `DerivationTree` constructors, not axiom constructors).

## Synthesis

### Conflicts Resolved

1. **Should `ClassicalHilbert` extend `IntuitionisticHilbert` or `MinimalHilbert` directly?**
   - Foundation uses `Cl extends Min` (non-linear lattice)
   - Recommendation: **Linear chain** (`Cl extends Int extends Min`). This is simpler, mirrors the ND system's `MPL ⊂ IPL ⊂ CPL`, and avoids the need to separately prove that `Cl` satisfies `Int` requirements.

2. **Should axiom inductives be factored now or later?**
   - Teammate A proposes nested inductives; Teammate D recommends deferring
   - Recommendation: **Defer axiom inductive refactoring**. The minimum viable change is typeclass hierarchy only. Existing concrete axiom inductives still prove `ClassicalHilbert` instances correctly. Factoring the inductives (sum types or nested embedding) can be a follow-up task.

3. **Should modal/temporal logics extend `IntuitionisticHilbert` or `ClassicalHilbert`?**
   - Teammate C notes one modal theorem (`box_contrapose_dia` in `Modal/Basic.lean`) uses `double_negation` (classical)
   - Recommendation: **Keep extending `ClassicalHilbert` for now**. All existing metalogic (completeness, soundness, MCS) is classical. Moving to intuitionistic modal logic is a separate future task. This minimizes disruption.

### Gaps Identified

1. **Primitive connectives**: For a genuinely useful intuitionistic base, primitive `HasAnd`/`HasOr` (with their own introduction/elimination axiom classes) would be valuable. The Lukasiewicz encoding limits the intuitionistic fragment to `⊥` and `→` only. This is a separate task.

2. **The `lem` theorem is misleadingly named**: With Lukasiewicz disjunction (`φ ∨ ψ := ¬φ → ψ`), `lem` reduces to `¬φ → ¬φ` (identity), which is trivially valid. It's not the real law of excluded middle. This should be documented.

3. **Tag types needed**: New tag types `Propositional.HilbertMin` and `Propositional.HilbertInt` should be added alongside existing `Propositional.HilbertCl`.

### Recommendations

**Recommended approach**: Typeclass hierarchy split (Approach B from Teammate B's taxonomy).

**Implementation phases**:

1. Add `MinimalHilbert` and `IntuitionisticHilbert` to `ProofSystem.lean`. Rename `PropositionalHilbert` to `ClassicalHilbert`. Add backward-compatibility alias.

2. Weaken `Combinators.lean` from `[PropositionalHilbert S]` to `[MinimalHilbert S]`.

3. Split `Core.lean` into intuitionistic and classical sections. Move `efq_axiom` to intuitionistic; `double_negation`, `raa`, `rcp`, `lce_imp`, `rce_imp` to classical.

4. Update `Connectives.lean` — mark De Morgan laws, `classical_merge` as classical; `contrapose_imp`, `contraposition` stay at minimal.

5. Update `ModalHilbert`, `TemporalBXHilbert`, `BimodalTMHilbert` to extend `ClassicalHilbert` (renamed from `PropositionalHilbert`).

6. Add tag types for minimal and intuitionistic systems.

7. Remove backward-compatibility alias. Clean up `HasAxiomDNE` (prove equivalence with Peirce+EFQ, or remove).

**Estimated effort**: Medium. Phases 1-2 are straightforward. Phase 3-4 is the main work (theorem audit and re-stratification). Phases 5-7 are mechanical.

## Teammate Contributions

| Teammate | Angle | Status | Confidence |
|----------|-------|--------|------------|
| A | Primary architecture design | completed | high |
| B | Prior art and alternatives | completed | high |
| C | Critic (gaps and risks) | completed | high |
| D | Strategic horizons | completed | high |

## References

- FormalizedFormalLogic/Foundation (GitHub): Three-level hierarchy at scale
- `Cslib/Logics/Propositional/Defs.lean`: Existing ND `MPL/IPL/CPL` hierarchy
- `Cslib/Foundations/Logic/ProofSystem.lean`: Current `PropositionalHilbert` definition
- `Cslib/Foundations/Logic/Theorems/Combinators.lean`: Purely minimal theorems
- `Cslib/Foundations/Logic/Theorems/Propositional/Core.lean`: Classical dependency roots
