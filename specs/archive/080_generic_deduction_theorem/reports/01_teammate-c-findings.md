# Teammate C (Critic) Findings — Task 80: Generic DeductionTheorem

**Date**: 2026-06-10
**Role**: Critic — identify gaps, risks, and blind spots
**Confidence Level**: HIGH (risks are concrete and verified against source code)

---

## Key Findings (Ranked by Severity)

### CRITICAL-1: Pattern Matching Cannot Be Abstracted Via Typeclasses

**Severity**: Critical (potential blocker)

The entire deduction theorem proof depends on Lean 4's native pattern matching against the concrete `DerivationTree` inductive type:

```lean
match d with
| .ax _ ψ h_ax => ...
| .assumption _ ψ h_mem => ...
| .modus_ponens _ ψ χ d₁ d₂ => ...
| .weakening Γ'' _ ψ d' h_sub => ...
```

Lean 4 typeclasses **cannot** expose pattern matching over an unknown inductive type. A typeclass can expose fields/methods, but not the ability to destructure an arbitrary inductive. The proposed `HasDerivationTree` typeclass with "constructor accessors" fundamentally misunderstands what the proof needs — it needs an **elimination principle**, not field getters.

**Why this matters**: The proof isn't calling methods on the tree; it's doing case analysis over every possible way a derivation could have been built. This is induction, not method dispatch. You cannot write `match (someAbstractTree d) with | ...` when the constructors aren't statically known.

**Possible mitigations**:
1. **Custom recursor/eliminator in the typeclass**: Expose a hand-rolled `recOn`/`casesOn` that takes one continuation per constructor. This is technically possible but extremely verbose and makes the termination argument harder.
2. **Don't abstract over the inductive**: Instead, use a single shared `DerivationTree` inductive parameterized by an "extension" type, and make the generic proof work over that. This is likely the only feasible path.

### CRITICAL-2: Well-Founded Recursion Through Typeclass Methods

**Severity**: Critical

The proofs use `termination_by d.height` with `decreasing_by` blocks that reference **constructor-specific** height lemmas:

- PL/Modal: `DerivationTree.height_modus_ponens_left d₁ d₂`, `DerivationTree.height_weakening d' h_sub`
- Temporal: `DerivationTree.height_modus_ponens_left d₁ d₂`, `DerivationTree.height_weakening d' h_sub`
- Bimodal: `DerivationTree.mp_height_gt_left h1 h2`, `DerivationTree.subderiv_height_lt h1 h2`

These lemmas mention concrete constructor names (`modus_ponens`, `weakening`). If `d` comes from a typeclass, the elaborator cannot see through the abstraction to extract the height relationship needed for termination. The variables `d₁`, `d₂`, `d'` are **pattern-match bound** — they exist only inside the `match` arms. If the match is replaced by a typeclass-provided eliminator, these variables live in continuation closures, making `decreasing_by` proofs much harder or impossible.

### HIGH-1: Axiom Naming Is Swapped Between Logic Families

**Severity**: High (must be resolved before any unification)

The axiom constructor names are **semantically swapped** between PL/Modal and Temporal/Bimodal:

| Logical Content | PL/Modal Name | Temporal/Bimodal Name |
|---|---|---|
| Weakening: `φ → (ψ → φ)` | `.implyK` | `.imp_s` |
| Distribution: `(φ→(ψ→χ))→((φ→ψ)→(φ→χ))` | `.implyS` | `.imp_k` |

This is not just a cosmetic difference — the names are **backwards**. Standard convention calls `φ → ψ → φ` the "K combinator" and the distribution axiom the "S combinator." PL/Modal follows the standard; Temporal/Bimodal has K and S swapped.

The generic proof needs to invoke these axioms by name. Any unification must first harmonize the naming. This could be a Task 79 prerequisite or done inline.

### HIGH-2: Axiom Constructor Signatures Differ Fundamentally

**Severity**: High

The `.ax` constructor differs across logic families:

| Logic | Constructor | Signature |
|---|---|---|
| Propositional | `.ax Γ φ h_ax` | 3 args; `h_ax : PropositionalAxiom φ` |
| Modal | `.ax Γ φ h_ax` | 3 args; `h_ax : ModalAxiom φ` |
| Temporal | `.axiom Γ φ h_ax h_fc` | 4 args; `h_ax : Axiom φ`, `h_fc : h_ax.minFrameClass ≤ fc` |
| Bimodal | `.axiom Γ φ h_ax h_fc` | 4 args; same as Temporal |

PL/Modal use `.ax` (no frame class argument); Temporal/Bimodal use `.axiom` with an additional `h_fc` frame class constraint. A generic proof must either:
- Abstract over both signatures (complex)
- Require all logics to adopt the 4-arg form (requires changing PL/Modal)

### HIGH-3: FrameClass Parameterization Divergence

**Severity**: High

| Logic | FrameClass Treatment |
|---|---|
| Propositional | None — `DerivationTree Γ φ` |
| Modal | None — `DerivationTree Γ φ` |
| Temporal | Hardcoded `FrameClass.Base` in deduction theorem |
| Bimodal | Polymorphic `{fc : FrameClass}` in deduction theorem |

The Bimodal proof is generic over frame classes; the Temporal proof hardcodes `FrameClass.Base`; PL/Modal have no concept of frame classes. A generic interface must handle this three-way split.

### HIGH-4: Height Lemma Names Are Inconsistent

**Severity**: High (must be harmonized)

| Concept | PL/Modal/Temporal | Bimodal |
|---|---|---|
| MP left height | `height_modus_ponens_left` | `mp_height_gt_left` |
| MP right height | `height_modus_ponens_right` | `mp_height_gt_right` |
| Weakening height | `height_weakening` | `subderiv_height_lt` |

### MEDIUM-1: Subset Notation Differences

**Severity**: Medium

PL/Modal use `∀ x ∈ Γ, x ∈ Δ` (explicit membership) and `fun _ h => nomatch h` for empty subset proofs. Temporal/Bimodal use `Γ ⊆ Δ` (`List.Subset`) and `List.nil_subset _`.

The weakening constructor signature differs correspondingly:
- PL/Modal: `h : ∀ x ∈ Γ, x ∈ Δ`
- Temporal/Bimodal: `h : Γ ⊆ Δ`

These are definitionally equal (`List.Subset` unfolds to the explicit form), but the generic proof must pick one convention.

### MEDIUM-2: removeAll Proof Style Divergence

**Severity**: Medium

Bimodal inlines `removeAll` subset proofs with `simp only [removeAll, List.mem_filter, decide_eq_true_eq]` (3 occurrences), while PL/Modal/Temporal use the shared helper lemmas from `ListHelpers.lean` (`mem_removeAll_of_mem_of_ne`, `removeAll_subset_removeAll`).

### MEDIUM-3: Extra Helper Functions in Bimodal

**Severity**: Medium

Bimodal defines unique helpers not present in other logics:
- `weaken_under_imp`: General helper for `⊢ φ → ⊢ A → φ`
- `weaken_under_imp_ctx`: Lifts weakening to contexts
- `deduction_assumption_same`: Uses `identity` from `Perpetuity/Helpers.lean` and `DerivationTree.lift`

PL/Modal/Temporal build identity proofs inline from S and K axioms. Bimodal uses a pre-proven `identity` lemma. The generic proof must pick one approach.

### MEDIUM-4: Constructor Count Variance

**Severity**: Medium (explicitly addressed in task description)

| Logic | Constructors | Extra (empty-context-only) |
|---|---|---|
| Propositional | 4 | None |
| Modal | 5 | `necessitation` |
| Temporal | 6 | `temporal_necessitation`, `temporal_duality` |
| Bimodal | 7 | `necessitation`, `temporal_necessitation`, `temporal_duality` |

The empty-context constructors are all discharged by `simp at hA` (vacuous since context is non-empty). The task description correctly identifies this.

### LOW-1: `noncomputable` vs `def` Divergence

**Severity**: Low

PL/Modal/Temporal use `noncomputable def` for all deduction helpers. Bimodal uses plain `def` inside a `noncomputable section`. The effect is the same, but the style differs.

### LOW-2: Linter Option Differences

**Severity**: Low

Temporal: `set_option linter.flexible false`, `linter.style.multiGoal false`, `linter.unusedTactic false`, `linter.style.setOption false`
Bimodal: `set_option linter.style.emptyLine false`, `linter.flexible false`
PL/Modal: No linter suppression

---

## Assumptions Not Validated

1. **"Constructor accessors in a typeclass" is sufficient**: The task description proposes exposing `ax`, `assumption`, `mp`, `weakening` as typeclass fields. This assumes the proof calls these as methods. In reality, the proof **pattern-matches** against them. These are fundamentally different operations.

2. **"All extra constructors discharged by `simp at hA`"**: True for `deduction_theorem` (context is `A :: Γ`, non-empty) and `deduction_with_mem` (context satisfies `A ∈ Γ'`). But the mechanism (`simp at hA`) works because Lean knows the context is `[]` from the constructor type — this relies on the concrete inductive structure being visible.

3. **"~600 lines eliminated"**: Likely overestimated. The generic proof would still need ~150-200 lines. Each domain would need 20-40 lines for instance definition + extra constructor dispatch. Net savings: ~300-400 lines, not 600.

4. **Task 79 provides needed harmonization**: Task 79 is `[PLANNED]`, not complete. Its survey identifies the axiom naming issue but the fix hasn't been applied. Task 80 may need axiom name harmonization done first.

---

## What Could Go Wrong (Specific Technical Scenarios)

### Scenario A: Typeclass Approach Fails at Pattern Matching
You define `class HasDerivationTree`, write the generic proof, and discover that Lean's elaborator cannot synthesize the match on an abstract type. The proof compiles only when you concretely instantiate the tree type, defeating the purpose.

### Scenario B: Termination Proof Breaks
The `termination_by d.height` / `decreasing_by` blocks reference pattern-bound variables. If the match is mediated by an eliminator function, these variables don't exist in the right scope. Lean's WF recursion elaborator rejects the proof.

### Scenario C: Universe Mismatch
PL/Modal: `DerivationTree Γ φ : Type _` (auto-inferred)
Temporal/Bimodal: `DerivationTree fc Γ φ : Type u` (explicit universe)
A unified typeclass must be universe-polymorphic, which may cause issues with typeclass resolution.

### Scenario D: Axiom Construction Fails Generically
The generic proof must invoke `K_axiom` and `S_axiom` for arbitrary logics. It needs to construct `DerivationTree [] (φ.imp (A.imp φ))` from an axiom witness. But the axiom types are different (`PropositionalAxiom`, `ModalAxiom`, `Temporal.Axiom`, `Bimodal.Axiom`). The typeclass must abstract over the axiom type AND provide axiom constructors, adding significant complexity.

---

## Questions That Should Be Asked

1. **Is a parameterized single inductive feasible?** Rather than typeclass abstraction, could a single `DerivationTree` in `Foundations/Logic/` be parameterized by an "extension constructors" type (e.g., `ExtraRule : Formula → Type`), with PL providing `Empty` (no extras), Modal providing a single `Necessitation`, etc.?

2. **Should axiom naming be harmonized first?** The `imp_k`/`imp_s` vs `implyK`/`implyS` swap is blocking. Should this be a prerequisite task or part of Task 80?

3. **Is Task 79 a hard dependency?** The task says "Dependencies: Task 79." Task 79 is `[PLANNED]`. Can Task 80 proceed independently by handling harmonization itself?

4. **What is the actual downstream usage?** The deduction theorem's output (`*_has_deduction_theorem`) feeds into `Metalogic.HasDeductionTheorem` for the MCS framework. Would a generic proof actually simplify downstream code, or just move complexity?

5. **Would a tactic/macro approach be more appropriate?** Instead of type-level abstraction, a Lean 4 macro that generates the deduction theorem proof from a specification of the constructors could achieve the same deduplication without fighting the type system.

---

## Recommended Alternative Design

Instead of the proposed typeclass, consider a **parameterized inductive** approach:

```lean
-- In Foundations/Logic/
inductive GenericDerivationTree (F : Type*) [HasImp F] 
    (AxiomPred : F → Prop) (ExtraRule : List F → F → Type*) :
    List F → F → Type _ where
  | ax (Γ : List F) (φ : F) (h : AxiomPred φ) : GenericDerivationTree ...
  | assumption (Γ : List F) (φ : F) (h : φ ∈ Γ) : GenericDerivationTree ...
  | modus_ponens (Γ : List F) (φ ψ : F) ... : GenericDerivationTree ...
  | weakening (Γ Δ : List F) (φ : F) ... : GenericDerivationTree ...
  | extra (Γ : List F) (φ : F) (e : ExtraRule Γ φ) 
      (d : GenericDerivationTree ...) : GenericDerivationTree ...
```

This allows:
- Pattern matching in the generic proof (it's a real inductive)
- Extra constructors handled uniformly via the `extra` case
- Each logic instantiates `ExtraRule` (PL: `Empty`, Modal: `Necessitation`, etc.)

The tradeoff: this requires refactoring the existing DerivationTree types to use the shared inductive, which is a larger change than the typeclass approach — but it's the only approach likely to actually work.
