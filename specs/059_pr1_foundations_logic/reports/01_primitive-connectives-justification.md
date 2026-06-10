---
task: 59
type: research
title: "Justification for Primitive Connective Choice in Foundations"
created: 2026-06-09
session: sess_1781057037_55e0e0
status: complete
---

# Justification for Primitive Connective Choice in Foundations

## Executive Summary

The `Foundations/Logic` layer of cslib takes `bot` (⊥, falsum) and `imp` (→, implication) as the two primitive connectives and derives negation, disjunction, and conjunction from them following the classical Łukasiewicz encoding. This is a well-established choice grounded in formal logic literature (Church 1956, Tarski–Bernays–Wajsberg), aligned with the Curry–Howard correspondence (→ is function type, ⊥ is the empty type), and particularly well-suited to the layered typeclass architecture used here: intuitionistic logic, classical logic, and all modal/temporal extensions differ from each other by adding exactly one axiom schema to the shared `{⊥, →}` core.

---

## Current Codebase Structure

### File inventory (16 files, 3,666 lines)

| File | Lines | Role |
|------|-------|------|
| `InferenceSystem.lean` | 68 | `InferenceSystem` typeclass + `DerivableIn` |
| `Connectives.lean` | 98 | Atomic classes `HasBot`, `HasImp`, `HasBox`, `HasUntil`, `HasSince`; bundled classes; `LukasiewiczDerived` |
| `Axioms.lean` | 322 | Polymorphic axiom `abbrev`s: `ImplyK`, `ImplyS`, `EFQ`, `Peirce`, `DNE`, all modal/temporal axioms |
| `ProofSystem.lean` | 354 | `ModusPonens`, `Necessitation`, `HasAxiom*` typeclasses; bundled `PropositionalHilbert`, `ModalHilbert`, `ModalS5Hilbert`, `TemporalBXHilbert`, `BimodalTMHilbert` |
| `LogicalEquivalence.lean` | 35 | `LogicalEquivalence` typeclass for context-based congruence |
| `Theorems.lean` | 38 | Barrel aggregator |
| `Theorems/Combinators.lean` | 330 | I, B, C combinators; `imp_trans`, `pairing`, `dni`, `combine_imp_conj` |
| `Theorems/Propositional/Core.lean` | 285 | LEM, DNE, RAA, `efq_neg`, `rcp`, `lce_imp`, `rce_imp` |
| `Theorems/Propositional/Connectives.lean` | 545 | `classical_merge`, `iff_intro`, `contrapose_imp`, De Morgan laws |
| `Theorems/Propositional/Reasoning.lean` | 43 | `bi_imp` |
| `Theorems/BigConj.lean` | 136 | `BigConj` syntax and derivability lemmas |
| `Theorems/Modal/Basic.lean` | 200 | K-level: `box_mono`, `diamond_mono`, `k_dist_diamond`, modal duality |
| `Theorems/Modal/S5.lean` | 585 | S5-level: Axiom 5 derivation, collapse theorems |
| `Theorems/Temporal/TemporalDerived.lean` | 270 | Temporal operator lemmas |
| `Theorems/Temporal/FrameConditions.lean` | 84 | Frame condition implications |
| `Metalogic/Consistency.lean` | 273 | `DerivationSystem`, Lindenbaum's lemma, MCS foundations |

### Dependency graph

```
InferenceSystem
    └── Connectives
        └── Axioms
            └── ProofSystem
                └── Theorems/Combinators
                    ├── Theorems/Propositional/Core
                    │   ├── Theorems/Propositional/Connectives
                    │   │   └── Theorems/Propositional/Reasoning
                    │   ├── Theorems/Modal/Basic
                    │   │   └── Theorems/Modal/S5
                    │   └── Theorems/Temporal/TemporalDerived
                    │       └── Theorems/Temporal/FrameConditions
                    └── Theorems/BigConj
Metalogic/Consistency  (imports Connectives only; no ProofSystem dependency)
```

---

## Design Decision: {⊥, →} as Primitives

### The two atomic typeclass declarations

```lean
class HasBot (F : Type*) where
  bot : F

class HasImp (F : Type*) where
  imp : F → F → F
```

These two classes, together with the bundled `PropositionalConnectives`, are the only connective requirements for the entire propositional, modal, and temporal tower. All other connectives are abbreviations:

```lean
-- Negation
¬φ  :=  φ → ⊥          -- imp φ bot

-- Top / Verum
⊤   :=  ⊥ → ⊥          -- imp bot bot

-- Disjunction (Łukasiewicz)
φ ∨ ψ  :=  (¬φ) → ψ    -- imp (imp φ bot) ψ

-- Conjunction (Łukasiewicz)
φ ∧ ψ  :=  ¬(φ → ¬ψ)   -- imp (imp φ (imp ψ bot)) bot

-- Biconditional
φ ↔ ψ  :=  (φ → ψ) ∧ (ψ → φ)
```

These definitions are collected in the `LukasiewiczDerived` class (intentionally uninstantiated -- each concrete formula type defines its own `abbrev`s that are definitionally equal to these defaults, avoiding typeclass resolution overhead).

### Axiom organization

The propositional axioms over `{⊥, →}` are:

| Axiom | Schema | Role |
|-------|--------|------|
| `ImplyK` | `φ → (ψ → φ)` | Weakening |
| `ImplyS` | `(φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))` | Distribution |
| `EFQ` | `⊥ → φ` | Ex falso quodlibet |
| `Peirce` | `((φ → ψ) → φ) → φ` | Classicality |
| `DNE` | `¬¬φ → φ` | Alternative classical axiom |

The `PropositionalHilbert` class bundles `{ImplyK, ImplyS, EFQ, Peirce}` with modus ponens. The boundary between intuitionistic and classical logic is drawn by the presence of `Peirce` (or equivalently `DNE`). Removing both leaves the intuitionistic fragment (`ImplyK + ImplyS + EFQ + MP`). Removing `EFQ` as well leaves minimal logic.

---

## Justifications

### Historical and Traditional Basis

The `{⊥, →}` primitive basis has a long and authoritative history in formal logic.

**Church (1956)**: Alonzo Church's *Introduction to Mathematical Logic* (Princeton University Press) presents classical propositional logic with implication (→) and falsum (⊥) as primitives, with negation defined as `¬A := A → ⊥`. The axiom schemas are exactly:
1. `A → (B → A)` (ImplyK)
2. `(A → (B → C)) → ((A → B) → (A → C))` (ImplyS)
3. `((A → ⊥) → ⊥) → A` (double negation via falsum)

This is the exact axiom system realized in `Axioms.lean` (`ImplyK`, `ImplyS`, and `DNE` / `Peirce`).

**Tarski–Bernays–Wajsberg**: The Tarski–Bernays–Wajsberg system (documented in the Wikipedia list of axiomatic systems in logic) is another classical example using `{→, ⊥}` with four axiom schemas including `⊥ → A` (EFQ) and Peirce's law.

**Gentzen (1935)**: Gerhard Gentzen's *Investigations into Logical Deduction* defines intuitionistic logic with falsum as a nullary connective, with negation `¬A` as the abbreviation `A → ⊥`. This is the standard treatment in proof theory textbooks.

**Johansson (1937)**: Minimal logic ("Minimalkalkül") uses `{→, ⊥}` without EFQ, providing the weakest base in the classical/intuitionistic/minimal hierarchy.

**Mendelson (1964 and later editions)**: *Introduction to Mathematical Logic* presents the alternative `{→, ¬}` basis for comparison. The `{→, ⊥}` formulation is strictly cleaner because it avoids treating negation as primitive (see Comparison section below).

### Proof-Theoretic Advantages

**Minimality of the axiom set**: Using `{⊥, →}` as primitives means the entire classical propositional calculus requires exactly four axiom schemas (ImplyK, ImplyS, EFQ, Peirce) plus modus ponens. No axiom schema mentions a connective not in the basis -- every axiom is a pure implication formula with `⊥` as the sole non-implicational atom. This makes independence proofs and metatheoretic analysis more tractable.

**The Deduction Theorem**: The deduction theorem holds for the implicational fragment alone and extends cleanly to the full system. In contrast, systems that include conjunction and disjunction as primitives require more complex formulations of the deduction theorem.

**Clean axiom shapes**: All axioms are built from `→` and `⊥` only. This means:
- Every axiom is a pure implication (possibly with `⊥` appearing as an atom)
- Proof-search procedures (e.g., resolution, tableau) can treat `⊥` uniformly as a propositional constant
- The S and K axioms (`ImplyS` and `ImplyK`) are precisely the types of the SKI combinators (see Curry-Howard section)

**Combinatorial foundation**: As shown in `Theorems/Combinators.lean`, the B, C, S, K, and I combinators are all derivable from just `ImplyK` and `ImplyS` alone (no `⊥` needed for the positive fragment). This establishes a clean separation: `{ImplyK, ImplyS}` gives you the positive implicational calculus (corresponding to the simply typed lambda calculus without base types), and adding `{EFQ, Peirce}` over `⊥` adds the classical negation theory.

### Clean Classical/Intuitionistic Separation

The `{⊥, →}` primitive choice makes the classical/intuitionistic boundary maximally visible and simple:

| System | Axioms | Class |
|--------|--------|-------|
| Minimal logic | `{ImplyK, ImplyS}` | not yet defined (subsumed) |
| Intuitionistic logic | `{ImplyK, ImplyS, EFQ}` | not yet defined (subsumed) |
| Classical logic | `{ImplyK, ImplyS, EFQ, Peirce}` | `PropositionalHilbert` |

The only difference between intuitionistic and classical logic in this formulation is the single axiom `Peirce` (or equivalently `DNE`). This is the clearest possible presentation of what makes classical logic "more than" intuitionistic logic.

This separation is documented directly in the `Axioms.lean` module: `Peirce` and `DNE` are defined as distinct `abbrev`s with notes explaining their role as the boundary.

In `Theorems/Propositional/Core.lean`, `double_negation` is *derived* from `EFQ + Peirce + B-combinator`, making the derivation structure explicit:
```lean
-- EFQ: ⊥ → φ
-- Peirce(φ,⊥): ((φ→⊥)→φ) → φ
-- B-combinator: (⊥→φ) → ((φ→⊥)→⊥) → ((φ→⊥)→φ)
-- Compose → DNE
```

### Curry-Howard Correspondence

The `{⊥, →}` basis has the most natural computational interpretation under the Curry-Howard correspondence (Curry 1934, Howard 1969):

| Logic | Type Theory |
|-------|-------------|
| `φ → ψ` (implication) | `φ → ψ` (function type) |
| `⊥` (falsum) | `Empty` (uninhabited type) |
| `¬φ = φ → ⊥` (negation) | `φ → Empty` (refutation function) |
| proof of `φ` | term of type `φ` |
| modus ponens | function application |

This correspondence is exact and natural for intuitionistic logic. The K and S axioms correspond precisely to the K and S combinators:
- `ImplyK`: `φ → (ψ → φ)` corresponds to `fun (a : φ) (b : ψ) => a : φ → ψ → φ` (the K combinator)
- `ImplyS`: `(φ → ψ → χ) → (φ → ψ) → φ → χ` corresponds to the S combinator

The classical axioms (`Peirce`, `DNE`) correspond to control operators (continuations, call/cc), as established by Griffin (1990). The `{⊥, →}` primitive choice makes this correspondence manifest: classical logic = intuitionistic logic + continuation passing.

In Lean 4, which is itself based on the Calculus of Inductive Constructions (a type theory), the `{⊥, →}` encoding is not just a notational choice -- it is structurally aligned with how Lean's type theory works internally. `HasBot.bot` maps naturally to `False : Prop` and `HasImp.imp` maps naturally to `→ : Prop → Prop → Prop`.

### Formalization Advantages in Lean 4

**Typeclass inheritance**: The two atomic classes `HasBot` and `HasImp` bundle cleanly into `PropositionalConnectives`, which extends into `ModalConnectives` (adds `HasBox`) and `TemporalConnectives` (adds `HasUntil`, `HasSince`). Because the primitives are exactly `{⊥, →}`, there is no redundancy: every modality extension adds new structure and not a redefinition of existing connectives.

**Polymorphic axiom `abbrev`s**: All axiom schemas in `Axioms.lean` are `abbrev`s over `[HasBot F] [HasImp F]`, making them available polymorphically at every formula type in the hierarchy (propositional, modal, temporal, bimodal) without duplication.

**Derived connectives as `abbrev`s**: Negation, conjunction, and disjunction are definitionally equal to their `{⊥, →}` encodings. This means Lean's kernel-level definitional equality handles all coercions automatically. No explicit rewrite lemmas are needed to convert between `¬φ` and `φ → ⊥`.

**MCS foundations**: The `Metalogic/Consistency.lean` module parameterizes Lindenbaum's lemma over `DerivationSystem F` which requires only `[HasBot F] [HasImp F]`. Consistency is defined as non-derivability of `⊥`. This is the correct, minimal definition that works identically for propositional, modal, temporal, and bimodal logics -- all of which share the `{⊥, →}` core.

**Diamond as derived**: In modal logic, `◇φ` (possibility) is `¬□¬φ = (□(φ → ⊥)) → ⊥`. Because `¬` and `□` are already available from `HasBot + HasImp + HasBox`, the diamond operator requires no new primitive -- it is an `abbrev` in terms of the existing structure. This can be seen throughout `Axioms.lean` (e.g., `AxiomB`, `Axiom5`, `AxiomD` all encode `◇` inline).

**No diamond via `→` and `⊥` require consistency checks**: Admissibility results for temporal logics (serial frame conditions, etc.) are stated purely in terms of `{⊥, →, Until, Since}` with no additional connective infrastructure.

**Avoidance of typeclass diamonds**: By not having separate `HasNeg`, `HasAnd`, `HasOr` classes, the codebase avoids diamond inheritance problems in the typeclass hierarchy. The comment in `Connectives.lean` on `BimodalConnectives` notes the care taken: `BimodalConnectives` extends `ModalConnectives` and adds `HasUntil`/`HasSince` directly rather than extending `TemporalConnectives`, to avoid a typeclass diamond. This architectural clarity is possible precisely because the derived connectives are not primitive.

### Comparison with Alternative Bases

**Alternative 1: `{¬, →}` (Mendelson, Łukasiewicz)**

This is the most common alternative, used in many textbooks. The key disadvantage is that `¬` is an additional primitive with its own axioms, increasing the complexity of the proof system. With `{¬, →}` as primitives, falsum must be derived: `⊥ := ¬⊤ := ¬(φ → φ)` -- a non-trivial derivation. In the `{⊥, →}` formulation, `⊤` is derived as `⊥ → ⊥`, which is simpler and more transparent.

For the cslib formalization, `{¬, →}` would require a `HasNeg` typeclass introducing resolution overhead at every site where negation is used. The `{⊥, →}` approach instead makes negation an `abbrev`, which Lean resolves via definitional equality rather than typeclass search.

**Alternative 2: `{¬, ∨}` or `{¬, ∧}`**

Both require two typeclasses for non-implicational connectives and make modus ponens harder to state (it must be axiomatized as a schema or derived from more complex axioms). These bases are less standard in Hilbert-style systems.

**Alternative 3: `{⊥, ∧, ∨, →}` (all connectives primitive)**

This approach -- taking all four as primitive -- is common in natural deduction presentations (Gentzen's NK) but undesirable for Hilbert-style axiom systems. In cslib, it would require four atomic typeclasses (or one large bundled class), axioms for introduction and elimination of each connective, and a more complex proof that the system is classical vs. intuitionistic. The single boundary axiom (Peirce or DNE) is obscured.

**Alternative 4: Pure implication `{→}` (Hilbert's original implicational calculus)**

The pure implicational calculus is functionally incomplete -- it cannot express tautologies involving negation, contradiction, or exclusive truth. Adding `⊥` as a nullary constant is the standard minimal extension to achieve functional completeness for classical logic (and `{→, ⊥}` without double negation gives intuitionistic logic, and without EFQ gives minimal logic).

**Summary of advantages of `{⊥, →}`**:

| Criterion | `{⊥,→}` | `{¬,→}` | `{¬,∨,∧,→}` |
|-----------|---------|---------|-------------|
| Number of primitives | 2 | 2 | 4 |
| Classical/intuitionistic boundary | Single axiom (Peirce/DNE) | Same | More complex |
| Curry-Howard naturalness | Direct (Empty/→) | Indirect | Indirect |
| Typeclass complexity | Minimal (2 classes) | 3 classes | 5 classes |
| Lean definitional equality | All derived connectives | `⊥` must be derived | No derived connectives |
| Modal/temporal extension | Add `HasBox`/`HasUntil` | Same + `¬` conflict | Same + more |

---

## Derived Connectives

The following table shows how all non-primitive connectives are encoded in terms of `{⊥, →}`:

| Connective | Encoding | Justification |
|------------|----------|---------------|
| `¬φ` | `φ → ⊥` | Standard: "φ implies contradiction" |
| `⊤` | `⊥ → ⊥` | Trivially provable (EFQ applied to itself) |
| `φ ∨ ψ` | `(φ → ⊥) → ψ` | "If φ is false, then ψ" (classical) |
| `φ ∧ ψ` | `(φ → (ψ → ⊥)) → ⊥` | "`φ → ¬ψ` is refuted" |
| `φ ↔ ψ` | `((φ→ψ)→((ψ→φ)→⊥))→⊥` | Conjunction of both directions |
| `◇φ` | `(□(φ→⊥)) → ⊥` | "¬□¬φ" -- possibility as dual of necessity |
| `Fφ` | `(⊤ U φ) → ⊤` | Eventuality via Until |
| `Gφ` | `¬(⊤ U ¬φ)` | Invariant via negated Until |

The `LukasiewiczDerived` class in `Connectives.lean` documents these encodings with docstrings. The same encodings appear inline throughout `Axioms.lean` (e.g., `◇` in modal axioms, `G`/`H`/`F`/`P` in temporal axioms).

**Why this encoding for disjunction?** The encoding `φ ∨ ψ := (φ → ⊥) → ψ` is classically equivalent to the standard `φ ∨ ψ` and is sound under classical propositional semantics. The encoding is standard in the literature (Mendelson, Church, and others). In the Łukasiewicz tradition, the classical disjunction `φ ∨ ψ` is taken to mean "if φ is false then ψ" -- which is exactly the material conditional `¬φ → ψ`. The equivalent intuitionistic encoding would require a different approach, but since this system targets classical logic (`PropositionalHilbert` includes Peirce), the classical equivalence holds.

**Why this encoding for conjunction?** The encoding `φ ∧ ψ := ¬(φ → ¬ψ)` captures the intuition that "φ and ψ hold" means "it is not the case that φ implies not-ψ". Under classical semantics, this is equivalent to standard conjunction. The proofs of `lce_imp` and `rce_imp` in `Theorems/Propositional/Core.lean` show that left and right projection are derivable from this encoding using Peirce's law.

---

## References

1. **Church, A. (1956)**. *Introduction to Mathematical Logic, Vol. I*. Princeton University Press. The definitive treatment of classical propositional logic with `{→, ⊥}` as primitives.

2. **Gentzen, G. (1935)**. "Untersuchungen über das logische Schließen" (*Investigations into Logical Deduction*). *Mathematische Zeitschrift* 39. Introduces minimal and intuitionistic logic with `¬A := A → ⊥`.

3. **Johansson, I. (1937)**. "Der Minimalkalkül, ein reduzierter intuitionistischer Formalismus". *Compositio Mathematica* 4:119–136. Minimal logic over `{→, ⊥}` without EFQ.

4. **Curry, H.B. and Feys, R. (1958)**. *Combinatory Logic, Vol. I*. North-Holland. The K and S combinators correspond to `ImplyK` and `ImplyS`; the B, C combinators to `b_combinator` and `theorem_flip`.

5. **Howard, W.A. (1980)**. "The Formulae-as-Types Notion of Construction" (circulated 1969). In *To H.B. Curry: Essays on Combinatory Logic, Lambda Calculus and Formalism*. Academic Press. Establishes the direct Curry-Howard correspondence between proofs and programs.

6. **Hindley, J.R. and Seldin, J.P. (2008)**. *Lambda-Calculus and Combinators: An Introduction* (2nd ed.). Cambridge University Press. Explains combinator bases (SK, BCKW) and their type-theoretic interpretation; directly relevant to the combinator structure of `Theorems/Combinators.lean`.

7. **Griffin, T.G. (1990)**. "A Formulae-as-Types Notion of Control". *Proceedings of POPL 1990*. Shows that classical axioms (Peirce, DNE) correspond computationally to continuation operators.

8. **Wikipedia: List of axiomatic systems in logic**. Documents the Tarski–Bernays–Wajsberg and Church systems using `{→, ⊥}` as primitives, confirming the historical standing of this choice.

9. **Wikipedia: Minimal logic**. Explains the three-tier hierarchy Minimal < Intuitionistic (+ EFQ) < Classical (+ Peirce/DNE) for systems over `{→, ⊥}`.

10. **Wikipedia: Curry–Howard correspondence**. Explains the mapping `→ ↔ function type`, `⊥ ↔ Empty type`, and classical extensions via continuations.

11. **Wikipedia: Implicational propositional calculus**. Shows that pure `{→}` is functionally incomplete and that adding `⊥` as a constant restores classical completeness.

---

## Recommendations for PR Description

The following points should appear in the PR description for `feat(Foundations/Logic)`:

1. **Standard basis**: "The connective hierarchy takes `bot` (⊥) and `imp` (→) as the two primitive connectives, following Church (1956) and the Tarski–Bernays–Wajsberg tradition. Negation, disjunction, conjunction, and biconditional are all derived via the classical Łukasiewicz encoding."

2. **Clean classical/intuitionistic split**: "The classical/intuitionistic boundary is drawn by a single axiom: `Peirce` (((φ→ψ)→φ)→φ) or equivalently `DNE` (¬¬φ→φ). The intuitionistic fragment is `{ImplyK, ImplyS, EFQ, MP}`; adding `Peirce` gives classical logic. This separation is made explicit in `Axioms.lean` and `ProofSystem.lean`."

3. **Curry-Howard alignment**: "The primitive basis `{⊥, →}` aligns naturally with Lean 4's type theory: implication is function type, falsum is the empty type. The K and S axiom schemas correspond directly to the K and S combinators, as realized in `Theorems/Combinators.lean`."

4. **Polymorphic design**: "All axiom schemas are defined once as polymorphic `abbrev`s over `[HasBot F] [HasImp F]` and are instantiated at any formula type (propositional, modal, temporal, bimodal) via typeclass resolution. This avoids code duplication across the four logic levels."

5. **Avoiding typeclass diamonds**: "Derived connectives (negation, conjunction, disjunction) are `abbrev`s rather than typeclass instances, eliminating the `HasNeg`/`HasAnd`/`HasOr` classes that would create resolution overhead and potential diamond conflicts in the multi-modal hierarchy."

6. **MCS foundations scope**: "The `Metalogic/Consistency.lean` module provides a logic-agnostic framework for maximal consistent sets (Lindenbaum's lemma via Zorn's lemma) parameterized over `DerivationSystem F` for any formula type with `[HasBot F] [HasImp F]`. This is included in this PR because it is imported by both the modal and temporal metalogic files."
