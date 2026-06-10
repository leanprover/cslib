# Teammate C (Critic) Findings: Task 88

**Task**: Refactor propositional Hilbert system to intuitionistic base with uniform extension architecture
**Date**: 2026-06-10
**Angle**: Gaps, risks, and blind spots analysis
**Confidence**: High (evidence-based from codebase analysis)

## Key Findings

### 1. Classical/Intuitionistic Theorem Separation Is Cleaner Than Expected

The Combinators.lean file (`imp_trans`, `identity`, `b_combinator`, `flip`, `app1`, `app2`, `pairing`, `dni`, `combine_imp_conj`) uses **zero** references to `HasAxiomPeirce` or `double_negation`. All combinators require only `ImplyK`, `ImplyS`, `EFQ`, and `ModusPonens` — these are purely intuitionistic.

In Core.lean, the **four** theorems that directly invoke `HasAxiomPeirce.peirce` are:
- `peirce_axiom` (trivial wrapper)
- `double_negation` (DNE derived from Peirce+EFQ+B-combinator)
- `lce_imp` (left conjunction elimination — uses Peirce as a trick for DT-free proof)
- `rce_imp` (right conjunction elimination — same pattern)

In Connectives.lean, **one** theorem uses Peirce directly:
- `classical_merge` (case analysis pattern)

Everything else (`raa`, `efq_neg`, `rcp`, De Morgan laws, etc.) depends on Peirce **transitively** through `double_negation`, `lce_imp`, or `rce_imp`.

**Critical insight**: `lce_imp` and `rce_imp` (conjunction elimination) are classical in this codebase because they use Peirce as a shortcut for DT-free proofs. In an intuitionistic system, conjunction elimination **is** intuitionistically valid — but would need to be proved differently (e.g., via the deduction theorem instead of the DT-free Peirce trick, or by introducing `HasAnd` as a primitive connective rather than defining conjunction as `¬(φ → ¬ψ)` in the Lukasiewicz encoding).

### 2. The Lukasiewicz Encoding Is the Root Problem

The entire codebase defines conjunction and disjunction via the Lukasiewicz encoding:
- `φ ∧ ψ := (φ → (ψ → ⊥)) → ⊥` (double negation of `φ → ¬ψ`)
- `φ ∨ ψ := (φ → ⊥) → ψ` (negated antecedent implies consequent)

These encodings are **classically valid** but **not intuitionistically equivalent** to the standard connectives. In intuitionistic logic:
- `(φ → (ψ → ⊥)) → ⊥` does NOT prove `φ` (that requires DNE)
- `(φ → ⊥) → ψ` does NOT follow from `φ` alone (that requires case analysis on `φ ∨ ¬φ`)

This means:
- Conjunction elimination (`lce_imp`, `rce_imp`) is classical with the current encoding
- Disjunction introduction is classical with the current encoding
- De Morgan laws are classical with the current encoding

**If you want an intuitionistic base, you either need**:
1. Primitive conjunction/disjunction connectives (new `HasAnd`, `HasOr` typeclasses), or
2. Accept that the base system only has `⊥` and `→`, and conjunction/disjunction are only available in classical extensions

### 3. `HasAxiomDNE` Is Declared But Never Used

`HasAxiomDNE` is defined in `ProofSystem.lean` (line 118) but has **zero** uses anywhere in the codebase. `PropositionalHilbert` uses `HasAxiomPeirce` instead. `HasAxiomDNE` appears to be dead code — a design artifact. This should be resolved: either use DNE as the classical axiom (more standard) or remove it.

### 4. The MCS Framework Does NOT Require Classical Logic at the Object Level

Examining `Consistency.lean`, the Lindenbaum's lemma and MCS machinery uses:
- Zorn's lemma (metamathematical, in `Prop`)
- `by_contra` and `push Not` (Lean's classical reasoning in the metatheory)
- `Classical.propDecidable` (decidability in the metatheory)

But critically, the `DerivationSystem` structure only requires `Deriv`, `weakening`, `assumption`, and `mp`. It does **not** require Peirce's law or any classical axiom. The `negation_complete` property (either `φ ∈ S` or `¬φ ∈ S`) is proved about the *maximally consistent set*, not assumed as an axiom. An intuitionistic derivation system can instantiate `DerivationSystem` perfectly well — MCS theory works for any logic with modus ponens and weakening. The completeness of the *object-level* logic would just mean completeness w.r.t. Kripke models (for IPL) rather than Boolean valuations.

### 5. Blast Radius Analysis

**15 unique files** reference classical-specific constructs. By category:

| Category | Files | Impact |
|----------|-------|--------|
| **Foundation definitions** | 1 | `ProofSystem.lean` — change `PropositionalHilbert` definition |
| **Foundation theorems** | 5 | `Combinators`, `Core`, `Connectives`, `Modal/Basic`, `Modal/S5` |
| **Temporal instances** | 2 | `Temporal/ProofSystem/Instances.lean`, `Temporal/Metalogic/PropositionalHelpers.lean` |
| **Bimodal instances** | 3 | `Bimodal/ProofSystem/Instances.lean`, `Bimodal/Theorems/Propositional/{Core,Connectives}` |
| **Propositional instances** | 2 | `Propositional/ProofSystem/Instances.lean`, `BigConj.lean` |
| **Documentation** | 1 | `Theorems.lean` (module aggregator) |
| **Perpetuity** | 1 | `Bimodal/Theorems/Perpetuity/Helpers.lean` |

**Total project files**: 336 Lean files. Blast radius is ~4.5% of the project.

### 6. Typeclass Diamond Concern Is Real But Manageable

Current hierarchy:
```
PropositionalHilbert
├── ModalHilbert (extends PropositionalHilbert + Necessitation + HasAxiomK)
│   └── ModalS5Hilbert (extends ModalHilbert + T + 4 + B)
├── TemporalBXHilbert (extends PropositionalHilbert + TemporalNecessitation + 22 axioms)
└── BimodalTMHilbert (extends ModalS5Hilbert + TemporalBXHilbert + HasAxiomMF)
```

If we split into `IntuitionisticHilbert` and `ClassicalHilbert extends IntuitionisticHilbert + HasAxiomPeirce`:

```
IntuitionisticHilbert
├── ClassicalHilbert (extends + HasAxiomPeirce)
├── ModalHilbert (extends IntuitionisticHilbert + Necessitation + HasAxiomK)
│   └── ClassicalModalHilbert (extends ModalHilbert + HasAxiomPeirce)
│       └── ModalS5Hilbert (extends ClassicalModalHilbert + T + 4 + B)
├── TemporalBXHilbert (extends IntuitionisticHilbert + TemporalNecessitation + ...)
│   └── ClassicalTemporalBXHilbert (extends + HasAxiomPeirce)
└── BimodalTMHilbert (extends ModalS5Hilbert + ClassicalTemporalBXHilbert + MF)
```

The diamond is between `ModalS5Hilbert → ClassicalHilbert → IntuitionisticHilbert` and `TemporalBXHilbert → IntuitionisticHilbert`. Lean 4 handles this with structure eta, but the `BimodalTMHilbert` already has this diamond (both modal and temporal extend propositional). The refactoring adds one more level but doesn't create a fundamentally new diamond.

**However**: if `ModalHilbert` extends `IntuitionisticHilbert` (not `ClassicalHilbert`), then we could have both intuitionistic and classical modal logics. But the existing K-level modal theorems in `Modal/Basic.lean` use `double_negation` (line 170) which requires classicality. This means either:
- `ModalHilbert` must extend `ClassicalHilbert` (current behavior, just renamed), OR
- The one classical theorem in `Modal/Basic.lean` (`box_contrapose_dia`) needs to be moved to a classical-only section

### 7. The Concrete Axiom Inductive Refactoring

Each logic has its own `Axiom` inductive with duplicated propositional constructors:
- `PropositionalAxiom`: 4 constructors (implyK, implyS, efq, peirce)
- `Modal.ModalAxiom`: 8 constructors (4 prop + 4 modal)
- `Temporal.Axiom`: 26 constructors (4 prop + 22 temporal)
- `Bimodal.Axiom`: 42 constructors (4 prop + 5 modal + 22 temporal + 11 others)

Removing `peirce` from the base affects **all four** axiom inductives. However, the concrete axiom inductives are only pattern-matched in:
- Soundness proofs (each case per axiom)
- Instance registration files

The deduction theorem proofs do NOT pattern-match on axioms — they pattern-match on `DerivationTree` constructors (`ax`, `assumption`, `modus_ponens`, `weakening`, `necessitation`). The `ax` case simply preserves the axiom hypothesis. So changing the axiom inductive does NOT require changing the deduction theorem proof.

## Risks and Concerns

### HIGH RISK: Lukasiewicz conjunction/disjunction is classical
The entire derived connective story collapses in intuitionistic logic with the current encoding. This is the single biggest risk and must be addressed in the design phase. Options:
- Add `HasAnd`, `HasOr` as primitive connectives (significant architectural change)
- Keep derived connectives but clearly mark lce/rce as classical-only
- Introduce two "levels" of connective availability

### MEDIUM RISK: Downstream theorem re-proofing
Modal S5 theorems heavily use `lce_imp`, `rce_imp`, `double_negation`, and `classical_merge`. These are ~15 theorem calls in `S5.lean` alone. All would need to be re-proved or restructured if conjunction elimination changes.

### LOW RISK: MCS framework compatibility
The MCS framework is agnostic to classical/intuitionistic — it works for any `DerivationSystem`. No changes needed.

### LOW RISK: Typeclass diamonds
The existing hierarchy already has diamonds. Adding the intuitionistic layer adds one more level but follows the same pattern.

## Questions That Must Be Answered Before Implementation

1. **Should conjunction/disjunction become primitive connectives** (`HasAnd`/`HasOr`), or remain as Lukasiewicz-derived with conjunction elimination only available in classical extensions?

2. **Should the intuitionistic base include EFQ (`⊥ → φ`)?** The ND system distinguishes `MPL` (minimal, no EFQ), `IPL` (intuitionistic, + EFQ), and `CPL` (classical, + DNE). The Hilbert system currently includes EFQ. The proposal should clarify whether the base is minimal or intuitionistic.

3. **Should `ModalHilbert` extend `IntuitionisticHilbert` or `ClassicalHilbert`?** If intuitionistic, one theorem in `Modal/Basic.lean` needs restructuring. If classical, the extension system is less uniform (modal logic becomes inherently classical).

4. **What is the target for the concrete axiom inductives?** Options:
   - Remove `peirce` from all four and add it as a separate extension axiom
   - Create a parametric axiom system where base axioms are shared and extensions are composable

5. **Is backward compatibility needed for `PropositionalHilbert`?** Can it simply be renamed to `ClassicalHilbert` or `ClassicalPropositionalHilbert`?

## Dependency Graph of Classical Constructs

```
HasAxiomPeirce
├── peirce_axiom (wrapper)
├── double_negation (DNE, derived from Peirce+EFQ+B)
│   ├── raa (reductio ad absurdum)
│   │   └── efq_neg
│   │       └── rcp (reverse contraposition)
│   ├── lce_imp (left conj. elim, DT-free)
│   │   └── iff_intro, contrapose_iff, demorgan_conj_neg_backward
│   ├── rce_imp (right conj. elim, DT-free)
│   │   └── iff_intro, contrapose_iff, demorgan_conj_neg_backward
│   ├── demorgan_conj_neg_forward
│   └── demorgan_disj_neg_forward
├── classical_merge
│   └── (used in Modal/S5.lean)
└── lce_imp (also uses Peirce directly)
    └── rce_imp (also uses Peirce directly)
```

All intuitionistic theorems would be: `imp_trans`, `identity`, `b_combinator`, `flip`, `app1`, `app2`, `pairing`, `dni`, `combine_imp_conj`, `contrapose_imp`, `contraposition`, `efq_axiom`, `lem` (note: `lem` as defined is just `identity (¬φ)`, which is intuitionistically valid — the Lukasiewicz definition of disjunction makes this trivially `¬φ → ¬φ`, not the real LEM).
