# Teammate A Findings: Primary Approach — Tableau & Decidability Architecture

**Task**: 9 — Port Decidability and Tableau to Bimodal module
**Date**: 2026-06-09
**Angle**: Implementation approaches, compositional architecture, and specific patterns

---

## Key Findings

1. **The four formula types form a strict embedding hierarchy with no shared inductive**. Propositional (`atom|bot|imp`) ⊂ Modal (`+box`) ⊂ Bimodal (`+untl|snce`); Temporal (`atom|bot|imp|untl|snce`) ⊂ Bimodal. Each is its own inductive — there is no parametric "Formula" type. The existing `Embedding/` files (`PropositionalEmbedding.lean`, `ModalEmbedding.lean`, `TemporalEmbedding.lean`) define structural recursion maps between them. This means a generic typeclass-based tableau framework would need to abstract over the formula type via typeclasses, not inherit from a shared datatype.

2. **The generic MCS framework in `Foundations/Logic/Metalogic/Consistency.lean` already provides the parametric pattern**: `DerivationSystem F` abstracts over `Deriv`, `weakening`, `assumption`, `mp`; then Lindenbaum's lemma, `SetConsistent`, `SetMaximalConsistent` are derived generically. Modal, Temporal, and Bimodal each instantiate this. **A similar generic Tableau framework at the Foundations level is feasible and desirable.**

3. **Each logic's tableau differs in a well-understood, structured way**:
   - **Propositional**: ~5 rules (T/F for atom, bot, imp, neg, and/or). No modal/world-creating rules. Terminates by subformula property alone.
   - **Modal (K/S5)**: Propositional rules + 2-4 modal rules (T-box, F-box/diamond creating new worlds). Terminates via Fischer-Ladner closure (finite subformula set). The S5 case has a universal accessibility relation simplifying the modal rules.
   - **Temporal**: Propositional rules + rules for U/S (unfolding rules, eventuality tracking). Termination is more complex — requires Fischer-Ladner closure + eventuality fulfillment. Often uses "until-unfolding": `T(φ U ψ)` branches into `T(ψ)` or `T(φ) ∧ T(X(φ U ψ))`.
   - **Bimodal (TM)**: All of the above + 28 expansion rules (per task description). The interaction axiom MF and uniformity axioms add cross-modal rules. This is the largest and most complex.

4. **Compositionality through embedding is LIMITED for tableau**: Unlike the MCS completeness proofs (where the canonical model construction naturally factors), tableau rules are tightly coupled to the formula type. You cannot simply "reuse propositional tableau rules" inside a modal tableau because the signed formula type is different. However, **the infrastructure types** (SignedFormula, Closure, Saturation, ProofExtraction pattern) can be abstracted.

5. **The `FrameClass` pattern (Base/Dense/Discrete) already exists in both Temporal and Bimodal**. This is important for decidability: the tableau and decision procedure may need to be parameterized by frame class, since density and discreteness affect which axioms are available and which models can be extracted.

6. **Propositional logic currently has minimal infrastructure** — just `Defs.lean`, `Embedding.lean`, and `NaturalDeduction/Basic.lean`. It lacks a Hilbert-style proof system, DerivationTree, MCS, soundness, and completeness. Adding a tableau here first would require either (a) building the full metalogic stack first, or (b) doing tableau independently of the MCS-based completeness. Option (b) is actually natural — propositional tableau is self-contained and doesn't need MCS.

7. **The existing DerivationTree pattern is remarkably uniform**: Modal has 5 constructors (ax, assumption, modus_ponens, necessitation, weakening). Bimodal has 7 (adding temporal_dual and induction). This uniformity means ProofExtraction (closed tableau → DerivationTree) will follow a consistent pattern across logics.

---

## Recommended Approach

### Architecture: "Bottom-Up Build with a Thin Generic Layer"

Build decidability/tableau in a **bottom-up order** (Propositional → Modal → Temporal → Bimodal), with a **thin generic infrastructure layer** in Foundations that captures shared patterns as typeclasses, NOT as a monolithic framework.

#### Layer 1: Generic Infrastructure (`Cslib/Foundations/Logic/Metalogic/Tableau/`)

Define typeclasses and structures that all four logics instantiate:

```
Cslib/Foundations/Logic/Metalogic/Tableau/
├── SignedFormula.lean    -- Generic SignedFormula type (parametric over F)
├── Branch.lean           -- Branch type, closure predicate
├── Expansion.lean        -- Typeclass for expansion rules
└── Decidability.lean     -- Generic decidability from finite tableau
```

Key types:
- `SignedFormula (F : Type*) := Bool × F` (or `inductive Sign | T | F`)
- `class TableauExpansion (F : Type*) where rules : SignedFormula F → List (List (SignedFormula F))`
- `class HasClosure (F : Type*) where closed : List (SignedFormula F) → Prop`
- `class HasSubformulas (F : Type*) where subformulas : F → Finset F`

#### Layer 2: Logic-Specific Implementations

Each logic gets `Metalogic/Decidability/` with the same file structure:

```
{Logic}/Metalogic/Decidability/
├── SignedFormula.lean       -- Logic-specific signed formula (may extend generic)
├── Tableau.lean             -- Expansion rules, tableau construction, termination
├── Closure.lean             -- Closure conditions
├── Saturation.lean          -- Saturation definition and lemmas
├── ProofExtraction.lean     -- Closed tableau → DerivationTree
├── CountermodelExtraction.lean  -- Open saturated → model
├── Correctness.lean         -- Soundness + completeness of tableau
└── DecisionProcedure.lean   -- decide function + Decidable instance
```

For Bimodal additionally:
```
Bimodal/Metalogic/Decidability/
├── FMP/
│   ├── ClosureMCS.lean
│   ├── BoundedModel.lean
│   ├── ModelSize.lean
│   └── FMP.lean
```

#### Layer 3: Cross-Logic Transfer Theorems (via Embedding)

In `Embedding/` or a new `Transfer/` directory:
- If Propositional formula φ is decidable, then its Modal embedding is decidable
- If Modal formula is decidable, its Bimodal embedding is decidable
- Conservative extension results for decidability

These leverage the existing embedding maps.

### Build Order

1. **Propositional** (simplest, ~800 lines): Stand-alone propositional tableau. No world-creating rules. Termination by subformula measure. This serves as the template.

2. **Modal** (~2,000 lines): Add modal rules for box/diamond. World-creating rules (F-box generates new branch/world). Termination via Fischer-Ladner closure.

3. **Temporal** (~3,000 lines): Add temporal rules for U/S. Eventuality tracking needed. More complex termination argument (quasimodel-based or automata-based).

4. **Bimodal** (~10,000 lines, the main port): Port the existing BimodalLogic source. This already has 28 rules. FMP is a major subcomponent.

### Why NOT a fully generic framework

A fully parametric `GenericTableau F` that all four logics instantiate would:
- Require abstracting over world-creation rules (modal), eventuality fulfillment (temporal), and frame-class-specific rules (both) — the abstraction boundary is extremely complex
- Add significant type-level overhead for little practical reuse, since each logic's termination argument is fundamentally different
- Fight against Lean 4's strengths (concrete pattern matching is much more ergonomic than typeclass dispatch for complex rule systems)

The thin generic layer captures what IS reusable (SignedFormula, Branch, Closure predicate shape) while letting each logic own its complex parts.

---

## Evidence/Examples

### SignedFormula (Generic)

```lean
-- Foundations/Logic/Metalogic/Tableau/SignedFormula.lean
inductive Sign where
  | T  -- True: formula should be satisfiable
  | F  -- False: formula should be falsified
  deriving DecidableEq, BEq, Repr

structure SignedFormula (F : Type*) where
  sign : Sign
  formula : F
  deriving DecidableEq, BEq

instance [DecidableEq F] : DecidableEq (SignedFormula F) := inferInstance

def SignedFormula.negate (sf : SignedFormula F) : SignedFormula F :=
  { sf with sign := match sf.sign with | .T => .F | .F => .T }
```

### Propositional Tableau Rules (Concrete)

```lean
-- Propositional/Metalogic/Decidability/Tableau.lean
inductive PropExpansion : SignedFormula (PL.Proposition Atom) →
    List (List (SignedFormula (PL.Proposition Atom))) → Prop where
  | t_imp (φ ψ) : PropExpansion ⟨.T, .imp φ ψ⟩ [[⟨.F, φ⟩], [⟨.T, ψ⟩]]
  | f_imp (φ ψ) : PropExpansion ⟨.F, .imp φ ψ⟩ [[⟨.T, φ⟩, ⟨.F, ψ⟩]]
  | t_bot : PropExpansion ⟨.T, .bot⟩ []  -- immediate closure
  | f_bot : PropExpansion ⟨.F, .bot⟩ [[]]  -- trivially satisfied
```

### Modal Tableau Rules (Extension Pattern)

```lean
-- Modal/Metalogic/Decidability/Tableau.lean
-- Reuses propositional rule shapes for imp/bot, adds:
inductive ModalExpansion : ... → Prop where
  | t_imp ... | f_imp ... | t_bot | f_bot  -- same as propositional
  | t_box (φ) : ModalExpansion ⟨.T, .box φ⟩ ...  -- propagate to all accessible worlds
  | f_box (φ) : ModalExpansion ⟨.F, .box φ⟩ ...  -- create new world with F(φ)
```

### Termination Strategy

For propositional and modal: well-founded recursion on `(Finset.card unprocessed, complexity measure)`.

For temporal: fuel-based approach with a proof that fuel suffices:
```lean
def tableau_fuel (φ : Formula Atom) : Nat :=
  2 ^ (subformulas φ).card * (subformulas φ).card
```

### Transfer via Embedding

```lean
-- Embedding/DecidabilityTransfer.lean
theorem decidable_of_propositional_decidable
    (h : Decidable (PL.Proposition.valid φ)) :
    Decidable (Modal.Proposition.valid (φ.toModal)) :=
  -- Propositional formulas have no box, so modal semantics reduces to propositional
  ...
```

---

## Confidence Level

**Medium-High**

**Justification**:
- **High confidence** on the directory structure, build order, and the recommendation against a fully generic framework — these are well-supported by the existing codebase patterns and the known complexity differences between propositional/modal/temporal tableau systems.
- **Medium confidence** on the specific termination strategies — temporal and bimodal tableau termination in Lean 4 is genuinely hard and may require creative approaches (fuel + proof of fuel sufficiency, or well-founded recursion on a custom ordering). The bimodal case with 28 rules has not been done in Lean 4 before to my knowledge.
- **Medium confidence** on the cross-logic transfer theorems — while the embeddings exist, proving decidability transfer through them involves showing that the embedding preserves satisfiability and that the simpler logic's decision procedure is correct for the embedded fragment. This is doable but nontrivial.
- **Key risk**: The propositional logic currently lacks even a Hilbert-style proof system. Building Propositional/Metalogic/ first (even just DerivationTree + Soundness) may be a prerequisite for ProofExtraction, unless tableau is done completely independently of the axiomatic system.
