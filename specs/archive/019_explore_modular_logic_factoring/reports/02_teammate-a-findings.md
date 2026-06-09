# Teammate A Findings: Semantic Boundary Analysis

## Key Findings

### 1. CSLib Already Has Separate Semantics Per Logic — and That's the Right Pattern

CSLib's existing architecture already commits to **separate, concrete semantics per logic module**:

- **Propositional** (`Logics/Propositional/Defs.lean`): Theory-based; `Theory` = `Set (Proposition Atom)`, with `IsIntuitionistic` and `IsClassical` typeclasses. No Kripke/model-theoretic semantics — uses natural deduction.
- **Modal** (`Logics/Modal/Basic.lean`): Kripke semantics with `Model World Atom` (accessibility relation `r : World → World → Prop`, valuation `v : World → Atom → Prop`), a recursive `Satisfies`, and the Modal Cube (`logic` = set of valid propositions over a frame class).
- **Temporal** (`Logics/Temporal/Syntax/Formula.lean`): Syntax only — no semantics yet.
- **Bimodal** (`Logics/Bimodal/Syntax/Formula.lean`): Syntax + embeddings only — no semantics yet in CSLib.

BimodalLogic has a radically different semantic structure from CSLib's modal semantics:
- **Task frame semantics**: `TaskFrame D` parameterized by an ordered additive commutative group `D` (duration type), with `WorldHistory F` (functions from time to world states), `truth_at M Omega τ t φ` (truth at model-history-time triple), and `ShiftClosed Omega` for time-shift invariance.
- Box quantifies over **all world histories** at a given time (not accessible worlds).
- Until/Since use **strict witnesses with open guards** on a linear temporal order.

These are fundamentally different semantic structures. Modal Kripke semantics uses a binary accessibility relation on worlds. Bimodal task semantics uses time-indexed world histories with duration-parameterized frames. There is no natural common typeclass that could abstract both without losing the mathematical content that makes soundness/completeness proofs work.

### 2. FormalizedFormalLogic Confirms: Separate Semantics Is Standard Practice

The FormalizedFormalLogic/Foundation project (the largest Lean 4 logic formalization) uses **separate Kripke semantics directories per logic**:

- `Propositional/Kripke/` — propositional Kripke semantics
- `Modal/Kripke/` — modal Kripke semantics (separate from propositional)
- `InterpretabilityLogic/Veltman/` — entirely different semantic framework

Each logic has its own `Model`, `Satisfies`, and completeness/soundness theorems within its own namespace. They do NOT share a unified semantic typeclass — the semantic structures are too different.

### 3. The Proof System Typeclasses CAN Be Shared; Semantics Cannot

CSLib's Foundations layer already demonstrates the correct separation:

- **Proof systems share typeclasses**: `PropositionalHilbert`, `ModalHilbert`, `ModalS5Hilbert`, `TemporalBXHilbert`, `BimodalTMHilbert` form a clean hierarchy with `extends`. Theorems proved at `[PropositionalHilbert S]` are reusable by all logics. This is the correct place for typeclass generalization.

- **Semantics should NOT share typeclasses**: Modal `Satisfies` pattern-matches on `{atom, bot, imp, box}`. Temporal truth would pattern-match on `{atom, bot, imp, untl, snce}`. Bimodal `truth_at` pattern-matches on all 6 constructors with history/time parameters. These are recursive functions on different inductive types — they cannot be meaningfully unified by typeclasses without losing the structural content that soundness proofs depend on.

### 4. Soundness/Completeness Must Be Per-Logic, Connected via Conservative Extension

Each logic needs its own:
- **Soundness theorem**: "If `Γ ⊢_S φ` then `Γ ⊨_S φ`" where both `⊢_S` and `⊨_S` use that logic's proof system and semantics.
- **Completeness theorem**: "If `Γ ⊨_S φ` then `Γ ⊢_S φ`" — requires logic-specific canonical model constructions (MCS theory, Lindenbaum lemma, etc.).

BimodalLogic already demonstrates this structure: `Soundness.lean` proves `(Γ ⊢ φ) → (Γ ⊨ φ)` specifically for the bimodal derivation tree and task semantics. The soundness proof depends intimately on the task frame structure (e.g., `ShiftClosed`, `time_shift_preserves_truth` for MF/TF axioms).

The connection between logics would be via **conservative extension theorems**, not unified semantics:
- If `φ` is a modal formula and `⊢_Modal φ`, then `⊢_Bimodal embed(φ)` (proof-theoretic).
- If `⊨_Modal φ`, then `⊨_Bimodal embed(φ)` (semantic, requires showing the modal embedding preserves truth).

CSLib already has the syntactic embeddings (`PL.Proposition.toModal`, `Modal.Proposition.toBimodal`, `PL.Proposition.toTemporal`) that would support these conservative extension theorems.

### 5. Tableau/Decision Procedures Must Be Per-Logic

BimodalLogic's `Tableau.lean` shows 20+ rules that are deeply tied to the bimodal formula structure:
- S5 modal rules (`boxPos`, `boxNeg`, `diamondPos`, `diamondNeg`)
- Temporal rules (`allFuturePos/Neg`, `allPastPos/Neg`, `someFuturePos/Neg`, `somePastPos/Neg`)
- Temporal interaction rules (`untlPos/Neg`, `sncePos/Neg`, `boxTemporal`)
- Frame-class-specific rules (`denseAxiom`)

A standalone modal logic tableau would only need the S5 rules (subset). A temporal-only tableau would only need temporal rules. A propositional tableau needs only the propositional rules. There is no meaningful "generic tableau" that could abstract across these — the rule sets are proper subsets/supersets of each other, and the termination arguments differ.

### 6. Temporal Semantics: Linear Orders Without World Histories

For standalone Temporal/, the semantics should be simpler than BimodalLogic's task frames:
- **Temporal models**: `(D, <, V)` where `D` is a linearly ordered set, `<` is the strict order, and `V : D → Atom → Prop` is a time-indexed valuation.
- **truth_at**: Directly on the linear order, no world histories, no box quantification.
- `φ U ψ` at time `t`: ∃ s > t, ψ(s) ∧ ∀ r ∈ (t,s), φ(r)
- `φ S ψ` at time `t`: ∃ s < t, ψ(s) ∧ ∀ r ∈ (s,t), φ(r)

This is a proper specialization of BimodalLogic's `truth_at` (drop the box case, drop world histories, use direct valuation). The bimodal `truth_at` then extends the temporal one by adding box + world histories.

## Recommended Approach

**Keep semantics completely separate for each logic module.** Specifically:

1. **Propositional** (`Foundations/Logic/` or `Logics/Propositional/`): Truth-value semantics via valuation `v : Atom → Prop`, or keep the existing theory-based approach. No Kripke frames needed.

2. **Modal** (`Logics/Modal/`): Keep the existing Kripke semantics exactly as is. `Model World Atom` with accessibility relation, `Satisfies`, frame correspondence theorems, Modal Cube. This is mature and well-designed.

3. **Temporal** (`Logics/Temporal/`): New standalone semantics on linear orders. `TemporalModel D Atom` with `(D, <, V)`, `truth_at` for `{atom, bot, imp, untl, snce}`. Standalone soundness/completeness for `TemporalBXHilbert`.

4. **Bimodal** (`Logics/Bimodal/`): Port BimodalLogic's task frame semantics as-is. `TaskFrame D`, `WorldHistory`, `TaskModel`, `truth_at` for all 6 constructors. Soundness/completeness for `BimodalTMHilbert`.

5. **Proof system typeclasses remain shared** at `Foundations/Logic/ProofSystem.lean` — this is where generalization pays off. Theorems proved at `[PropositionalHilbert S]` are automatically available to modal, temporal, and bimodal proof systems via typeclass inheritance.

6. **Conservative extension theorems** bridge the logics semantically, using the existing syntactic embeddings.

## Evidence/Examples

### Evidence 1: Semantic structures are structurally incompatible

Modal `Satisfies` (CSLib):
```lean
def Satisfies (m : Model World Atom) (w : World) : Proposition Atom → Prop
  | .atom p => m.v w p
  | .bot => False
  | .imp φ₁ φ₂ => Satisfies m w φ₁ → Satisfies m w φ₂
  | .box φ => ∀ w', m.r w w' → Satisfies m w' φ
```

Bimodal `truth_at` (BimodalLogic):
```lean
def truth_at (M : TaskModel F) (Omega : Set (WorldHistory F))
    (τ : WorldHistory F) (t : D) : Formula → Prop
  | Formula.atom p => ∃ (ht : τ.domain t), M.valuation (τ.states t ht) p
  | Formula.bot => False
  | Formula.imp φ ψ => truth_at M Omega τ t φ → truth_at M Omega τ t ψ
  | Formula.box φ => ∀ (σ : WorldHistory F), σ ∈ Omega → truth_at M Omega σ t φ
  | Formula.untl φ ψ => ∃ s : D, t < s ∧ truth_at M Omega τ s φ ∧ ...
  | Formula.snce φ ψ => ∃ s : D, s < t ∧ truth_at M Omega τ s φ ∧ ...
```

These differ in:
- **Evaluation context**: `(Model, World)` vs `(TaskModel, Omega, WorldHistory, Time)`
- **Box semantics**: accessibility relation vs history-universal quantification
- **Temporal structure**: none vs duration-parameterized linear order
- **Domain handling**: total vs partial (atoms false outside `dom(τ)`)

### Evidence 2: Soundness proofs depend on semantic-specific lemmas

BimodalLogic's MF axiom soundness uses `TimeShift.time_shift_preserves_truth` — a 250-line proof by structural induction on formulas that is specific to the `truth_at` definition and `WorldHistory.time_shift`. No abstract typeclass could provide this.

### Evidence 3: FormalizedFormalLogic precedent

The largest Lean 4 logic formalization uses separate `Kripke/` directories per logic with no shared semantic infrastructure. Their Modal/Kripke and Propositional/Kripke are separate developments.

## Confidence Level

**High** — The recommendation follows from three independent lines of evidence:
1. **Structural analysis**: The semantic definitions are recursive functions on different inductive types with different evaluation contexts; typeclasses cannot abstract this.
2. **External precedent**: FormalizedFormalLogic uses the same per-logic-separate-semantics pattern.
3. **Internal consistency**: CSLib's existing architecture already separates Modal and Propositional semantics, and the proof system typeclasses in Foundations/ are the correct (and already operational) layer for cross-logic generalization.
