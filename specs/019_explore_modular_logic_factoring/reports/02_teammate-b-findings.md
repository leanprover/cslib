# Teammate B Findings: Alternative Approaches and Prior Art

## Key Findings

### 1. FormalizedFormalLogic/Foundation — The Closest Prior Art

Foundation (https://github.com/FormalizedFormalLogic/Foundation) is the most comprehensive Lean 4 multi-logic formalization and the direct inspiration for CSLib's typeclass design. Its architecture reveals critical design choices for CSLib:

**Separate Semantics Per Logic**. Foundation defines completely independent semantic structures for propositional and modal logic:

- **Propositional Kripke**: `LO.Propositional.Kripke.Frame` with `World`, `Rel : Rel World World`, and crucially `[rel_partial_order : IsPartialOrder _ Rel]`. Its `Satisfies` is intuitionistic — implication is `∀ {w'}, w ≺ w' → (Satisfies M w' φ → Satisfies M w' ψ)`, quantifying over accessible worlds.

- **Modal Kripke**: `LO.Modal.Kripke.Frame` with `World`, `Rel : Rel World World`, and only `[world_nonempty : Nonempty World]`. No order constraint. Its `Satisfies` is classical — implication is standard material conditional `(Satisfies M x φ) 🡒 (Satisfies M x ψ)`.

These are **not the same Kripke semantics** — propositional uses intuitionistic forcing (monotone hereditary valuation), modal uses classical satisfaction. They share no code.

**Generic Semantics Typeclass**. Foundation defines `LO.Semantics (M : Type*) (F : outParam Type*)` with a single method `Models : M → F → Prop`. This is a thin unifying notation layer (`⊧`), not shared implementation. Each logic provides its own `Semantics` instance:
- Modal: `instance semantics {M : Kripke.Model} : Semantics M (Formula ℕ) := ⟨fun x ↦ Formula.Kripke.Satisfies M x⟩`
- Propositional: analogous instance

The `Semantics.Tarski` class bundles standard truth conditions (Top, Bot, And, Or, Imp, Not) as a convenience layer. This lets generic lemmas about `⊧` work across logics without knowing which logic is in play.

**Hilbert Systems Parameterized by Axiom Sets**. Foundation's `Hilbert.Normal` is parameterized by `(Ax : Axiom α)` — a set of axiom schemas. Different logics are just different axiom sets:
- K = `Hilbert.Normal {Axioms.K}`
- S4 = `Hilbert.Normal {Axioms.K, Axioms.T, Axioms.Four}`
- etc.

Soundness is then generic: `soundness_of_validates_axioms (hV : C ⊧* Ax) : Hilbert.Normal Ax ⊢ φ → C ⊧ φ`. This works because all normal modal logics share the same Kripke semantics infrastructure.

**No Temporal Logic**. Foundation has no temporal logic, no Until/Since, no tense operators. CSLib is breaking new ground here.

### 2. LeanLTL — Temporal Logic in Lean 4

LeanLTL (https://github.com/UCSCFormalMethods/LeanLTL, ITP 2025) formalizes LTL over infinite traces. Key observations:

- **No proof system, no Hilbert calculus** — purely semantic (model-checking oriented).
- **No Since operator** — only future-time LTL (Next, Until). The authors note past-time operators add no expressive power.
- **Traces, not Kripke frames** — `Trace σ` is a function from natural numbers to states, fundamentally different from Kripke models or task frames.
- **No connection to modal logic** — completely independent formalization.

This confirms that temporal logic semantics (traces/linear orders) is fundamentally different from modal Kripke semantics (relational structures), and no existing Lean 4 project attempts to unify them.

### 3. Other Projects

- **SnO2WMaN/lean4-modallogic**: Small modal logic formalization, appears inactive.
- **seberry/LFPS-Lean**: Modal logic for potentialist set theory — specialized, not general-purpose.
- **verse-lab/Lentil**: TLA+ in Lean 4 — temporal logic of actions, also trace-based, no Hilbert system.
- **Mathlib**: No formalized Kripke semantics, no modal/temporal logic. Mathlib has `Relation` infrastructure (reflexive, transitive, etc.) that Foundation and CSLib both use, but no logic-specific content.

### 4. Pattern Analysis: How Semantics Boundaries Work

Across all projects examined, a clear pattern emerges:

| Layer | Shared? | Why |
|-------|---------|-----|
| **Syntax** (formula types) | Per-logic | Each logic has different constructors |
| **Connective typeclasses** | Shared | `HasBot`, `HasImp`, `HasBox` — CSLib already does this |
| **Axiom definitions** | Shared | Polymorphic `abbrev`s over connective typeclasses — CSLib already does this |
| **Proof system typeclasses** | Shared | `PropositionalHilbert`, `ModalHilbert` — CSLib already does this |
| **Derived theorems** | Shared at typeclass level | `[PropositionalHilbert S] → derivable (ImplyK φ ψ)` — this is what Task 20/21/22 aims to create |
| **Kripke semantics** | Per-logic | Different Frame/Model/Satisfies for each logic |
| **Soundness** | Per-logic | Requires concrete semantics + concrete proof system |
| **Completeness** | Per-logic | Inherently tied to specific canonical model construction |
| **Tableau/Decision** | Per-logic | Algorithm depends on specific formula structure |

**The critical insight**: Foundation's architecture validates separating semantics per logic while sharing proof-theoretic infrastructure. Soundness cannot be proven generically because it inherently relates a concrete proof system to a concrete semantics. What CAN be shared are:
1. The axiom definitions (already done via `Axioms.lean`)
2. The typeclass hierarchy (already done via `ProofSystem.lean`)
3. Derived theorems at the typeclass level (the goal of Tasks 20-22)

## Recommended Approach

### Keep Semantics Separate Per Logic

Following Foundation's pattern and the fundamental mathematical reality:

1. **Propositional**: No independent Kripke semantics needed for Hilbert-style theorems. The theorems in Task 20 are purely syntactic — they derive `S ⊢ φ` from `[PropositionalHilbert S]` without any reference to semantics. Propositional soundness/completeness already exists in CSLib via natural deduction (a different proof system).

2. **Modal**: CSLib already has Kripke semantics (`Modal.Model`, `Modal.Satisfies`, frame correspondence). Keep this. When `Modal.DerivationTree` is created (Task 21), soundness will connect this existing semantics to the new Hilbert proof system. The Hilbert-derived theorems (`[ModalS5Hilbert S]` lemmas) are also purely syntactic.

3. **Temporal**: Needs its own semantics — truth on linear orders, NOT task frames. BimodalLogic's task frame semantics is inherently bimodal (box quantifies over world histories). Standalone temporal semantics would be simpler: truth at a point in a linear order, with Until/Since as the temporal operators. This is a new development not in BimodalLogic.

4. **Bimodal**: Task frame semantics stays in `Bimodal/` — it's the only logic that needs world histories, task relations, and the interaction between box and temporal operators.

### Adopt Foundation's `Semantics` Typeclass Pattern (Optional Enhancement)

Foundation's `Semantics M F` typeclass (`Models : M → F → Prop`) with the `⊧` notation is lightweight and useful. CSLib could adopt this pattern to unify notation across logics without sharing implementation. Currently CSLib uses `HasInferenceSystem` for a similar purpose on the proof-theory side, but has no analogous unification on the semantics side.

However, this is an **optional enhancement**, not a prerequisite for the factoring work. The current per-logic `Satisfies` definitions work fine.

### Don't Try to Genericize Soundness

No existing project attempts generic soundness across different kinds of logics (modal vs temporal vs bimodal). Foundation's soundness is generic only **within** modal logic (across different axiom sets sharing the same Kripke frame structure). CSLib should follow the same pattern:
- Soundness for modal Hilbert system → modal Kripke semantics (Task 21 + future)
- Soundness for bimodal proof system → task frame semantics (Task 6, already planned)
- Soundness for temporal proof system → temporal semantics (future work after Task 22)

Each is a separate theorem connecting a specific proof system to its specific semantics.

## Evidence/Examples

### Foundation's Soundness Pattern (Generic Within a Logic)

```lean
-- Foundation: soundness is generic over axiom sets, NOT over logics
lemma soundness_of_validates_axioms (hV : C ⊧* Ax) :
    Hilbert.Normal Ax ⊢ φ → C ⊧ φ
```

This works because `Hilbert.Normal Ax` always uses the same `DerivationTree` structure (axiom + MP + necessitation) and the same `Kripke.Satisfies`. Different axiom sets just validate on different frame classes.

### Foundation's Separate Frame Definitions

```lean
-- Propositional Frame: partial order (intuitionistic)
structure LO.Propositional.Kripke.Frame where
  World : Type
  Rel : Rel World World
  [rel_partial_order : IsPartialOrder _ Rel]

-- Modal Frame: arbitrary relation
structure LO.Modal.Kripke.Frame where
  World : Type
  Rel : Rel World World
  [world_nonempty : Nonempty World]
```

These are incompatible — you cannot use a modal frame as a propositional frame or vice versa. The semantics are fundamentally different.

### BimodalLogic's Task Frame (Inherently Bimodal)

```lean
-- BimodalLogic: task frame with temporal duration group
structure TaskFrame (D : Type*) [...] where
  WorldState : Type
  task_rel : WorldState → D → WorldState → Prop
  nullity_identity : ...
  forward_comp : ...
  converse : ...
```

The `truth_at` function interprets `□φ` as quantification over world histories and `Until`/`Since` over the temporal order — both in the same definition. This cannot be factored into separate modal and temporal semantics without losing the interaction.

### LeanLTL: Temporal Semantics are Trace-Based

```lean
-- LeanLTL: satisfaction over infinite traces
def sat (t : Trace σ) (f : Formula σ) : Prop :=
  match f with
  | Formula.until f₁ f₂ => ∃ i ≥ 0, (∀ j < i, sat (shift j) f₁) ∧ sat (shift i) f₂
```

No Kripke frames, no accessibility relation — just sequences. This is fundamentally different from modal semantics.

## Confidence Level

**High**. The recommendation (separate semantics, shared typeclass proof theory) is strongly supported by:
1. Every existing Lean 4 logic library uses separate semantics per logic
2. The mathematical reality: different logics have fundamentally different semantic structures
3. Foundation, the most mature project and CSLib's inspiration, validates this exact pattern
4. The factoring plan (Tasks 20-22) correctly targets the syntactic/proof-theoretic layer, not semantics
5. No existing project attempts to unify temporal and modal semantics — BimodalLogic is unique in combining them, and that combination is inherently bimodal

The only minor uncertainty is whether CSLib should adopt Foundation's `Semantics M F` notation typeclass. This is low-risk and orthogonal to the factoring decision.
