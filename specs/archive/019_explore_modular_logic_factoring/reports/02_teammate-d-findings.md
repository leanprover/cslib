# Teammate D Findings: Strategic Horizons

**Task**: 19 — Explore modular logic factoring
**Date**: 2026-06-08
**Angle**: Long-term strategic alignment, extensibility, and contribution potential

---

## Key Findings

### 1. The Semantic Boundary Decision Has Outsized Long-Term Impact

The question "should semantics be separate per logic or composable?" is the single most consequential architectural decision for CSLib's logic modules. Here's why:

**Current state**: CSLib already has *three distinct semantic paradigms* coexisting:
- **HML**: Satisfaction defined inductively over LTS transitions (`Satisfies lts s a`)
- **Modal**: Satisfaction defined recursively over Kripke models with accessibility relations (`Satisfies m w φ`)
- **Bimodal (BimodalLogic)**: Truth defined recursively over task frames with world histories (`truth_at M Omega τ t φ`)
- **Propositional**: Theory-based (sets of propositions), no model-theoretic semantics yet
- **Linear Logic**: Has phase semantics (`Cslib/Logics/LinearLogic/CLL/PhaseSemantics/`)

Each of these semantic frameworks is *genuinely different* in structure. They are not instances of one abstract pattern. This is the key empirical observation: **semantics resist unification more than syntax or proof theory do**.

### 2. Syntax and Proof Systems Compose; Semantics Don't (and Shouldn't)

The existing typeclass hierarchy already proves that syntax and proof systems compose well:

```
PropositionalConnectives → ModalConnectives → BimodalConnectives
                         → TemporalConnectives → BimodalConnectives

PropositionalHilbert → ModalHilbert → ModalS5Hilbert → BimodalTMHilbert
                     → TemporalBXHilbert → BimodalTMHilbert
```

This typeclass lattice is elegant, correct, and extensible. But the semantic structures are structurally incompatible:

| Logic | Semantic Structure | Truth Evaluated Over |
|-------|-------------------|---------------------|
| Modal | `Model World Atom` (accessibility `r : World → World → Prop`) | Single world `w : World` |
| Temporal | Linear/dense order on time | Time point `t : D` in a history |
| Bimodal | `TaskFrame D` + `WorldHistory F` + shift-closed `Omega` | Triple `(M, τ, t)` |
| HML | LTS transitions | State `s : State` |

A temporal `Satisfies` would need a linear order on time points — fundamentally different from modal's accessibility relation. There's no typeclass that abstracts over "a Kripke frame" and "a task frame with world histories" in a useful way. Attempting one would produce a lowest-common-denominator abstraction that adds complexity without value.

### 3. Separate Semantics Enable Independent Contribution and Verification

Looking at tasks 2-11 in TODO.md, the entire porting pipeline is currently bottlenecked on a single dependency chain through Bimodal/. With separate semantics:

- **Modal semantics already exists** (Cube.lean, Denotation.lean) and is independently useful. It can serve as the semantic foundation for `Modal/Theorems/` soundness results without waiting for bimodal porting.
- **Temporal semantics is new work** (not from BimodalLogic) — the research synthesis notes this explicitly. It needs truth on linear orders, not task frames. This can be developed independently.
- **Bimodal semantics** (task frame + world histories) is the complex specialized case that combines both.

This creates three independent contribution tracks:
1. Modal Kripke semantics → Modal soundness/completeness (leveraging existing `Cube.lean`)
2. Temporal linear-order semantics → Temporal soundness (new, could draw from Mathlib's order theory)
3. Bimodal task frame semantics → The full TM metalogic (tasks 3, 6, 8)

### 4. Mathlib Contribution Candidates

Examining what's most Mathlib-ready:

**Strong candidates** (self-contained, general, well-established theory):
- `Modal/Basic.lean` + `Cube.lean` — Already has frame correspondence proofs (K↔universal, T↔reflexive, B↔symmetric, 4↔transitive, 5↔Euclidean, D↔serial). This is textbook material and independently useful. The current implementation is clean and Mathlib-style (uses `grind`, proper docstrings).
- `Propositional/NaturalDeduction/Basic.lean` — Clean theory-based natural deduction with cut, weakening, substitution. Mature code by Thomas Waring.
- Propositional Hilbert theorems (Task 20) — Once ported as `[PropositionalHilbert S]` lemmas, these are completely standalone and prove basic facts about any Hilbert system.

**Medium candidates** (useful but more specialized):
- `HML/Basic.lean` — Nice theory with bisimilarity characterization, but HML is more niche.
- Modal Hilbert theorems (Task 21) — S4/S5 derived theorems are well-established but need proof system instances.

**Unlikely candidates** (too specialized for Mathlib):
- Bimodal task frame semantics — novel formalism specific to the JPL paper
- Separation theorem, decidability — too specialized
- Perpetuity theorems — inherently bimodal

**Implication**: Keeping Modal/ and Propositional/ semantics separate and clean maximizes their Mathlib-contribution potential. Entangling them with bimodal infrastructure would reduce this potential.

### 5. The Embedding Lattice Is the Right Composition Mechanism

CSLib already has the right architecture for connecting logics — embeddings:

```
PL.Proposition.toModal  : PL.Proposition → Modal.Proposition
PL.Proposition.toTemporal : PL.Proposition → Temporal.Formula
Modal.Proposition.toBimodal : Modal.Proposition → Bimodal.Formula
Temporal.Formula.toBimodal : Temporal.Formula → Bimodal.Formula
```

Task 15 plans to complete this lattice (add `PL.toBimodal`, triangle-commutes). This is the right composition mechanism because:

- Embeddings are *syntactic* — they map formulas, not models
- The separation theorem (Task 10) characterizes exactly when a bimodal formula is equivalent to a pure modal or temporal formula, closing the loop
- New logics (epistemic, deontic) would add their own embeddings without touching existing semantics

### 6. Future Logic Extensions: What Reuse Looks Like

Consider someone adding epistemic-temporal logic (knowledge + time, like `KT45` + linear time):

**With separate semantics**: They define `EpistemicTemporal.Formula` (extending both), write their own semantics (Kripke frames with temporal structure — not task frames), and import:
- `PropositionalHilbert` theorems from Foundations/
- `ModalS5Hilbert` theorems from Modal/ (knowledge is S5)
- `TemporalBXHilbert` theorems from Temporal/ (if their temporal fragment matches)
- Their own interaction axioms and metalogic

**With unified semantics**: They'd need to fit into an abstract framework that may not match their semantic structure, or fight against it.

The first path is clearly better. The typeclass hierarchy provides theorem reuse; semantics are bespoke per logic family.

### 7. Creative Alternative Considered and Rejected: Generic Semantics Typeclass

I considered whether a generic `Semantics` typeclass at the Foundations level could work:

```lean
class Semantics (M : Type*) (F : Type*) where
  satisfies : M → F → Prop
```

This is too thin to be useful. The interesting properties (frame conditions, validity, soundness) all depend on the *structure* of `M`, which varies per logic. A `Semantics` typeclass would just be a wrapper around `Prop` with no additional leverage for proofs. The existing `InferenceSystem` is the right level of abstraction — it works because derivability has a uniform structure (trees of inference rules), unlike semantic evaluation.

---

## Recommended Approach

**Keep semantics strictly separate per logic module. Do not attempt semantic composition or abstraction.**

Specifically:

1. **Modal/Semantics/**: Already exists (`Basic.lean` Kripke semantics, `Cube.lean` frame correspondence, `Denotation.lean`). Keep as-is. This is CSLib's most Mathlib-ready module.

2. **Temporal/Semantics/**: Create new, independent temporal semantics on linear orders. This is NOT a port from BimodalLogic — it's new infrastructure. Use Mathlib's `LinearOrder` for the time domain. Define `Temporal.Satisfies` recursively on `Temporal.Formula`. This enables standalone temporal soundness/completeness proofs.

3. **Bimodal/Semantics/**: Port task frame semantics from BimodalLogic (task 3). This is the specialized bimodal case that combines modal and temporal evaluation in a single `truth_at`.

4. **Foundations/Logic/**: Keep the typeclass hierarchy (`PropositionalHilbert`, `ModalHilbert`, etc.) for proof system composition. Do NOT add semantic typeclasses here. The `InferenceSystem` typeclass is the right abstraction for proof systems; there is no analogous right abstraction for semantics.

5. **Embeddings/**: Continue the embedding lattice approach. Add semantic preservation theorems where appropriate (e.g., if `φ : Modal.Proposition` is valid in all Kripke frames, then `φ.toBimodal : Bimodal.Formula` is valid in all task models — this bridges the semantic gap via syntactic embedding).

**The principle**: Syntax and proof theory share structure → use typeclasses. Semantics have diverse structure → use separate definitions connected by embedding preservation theorems.

### Impact on Task Graph

This recommendation aligns with and strengthens the existing plan:
- Tasks 20-22 (propositional/modal/temporal theorem extraction) work exactly as planned — theorems use typeclass signatures, independent of semantics
- Task 3 (bimodal semantics) stays entirely within `Bimodal/Semantics/`
- Tasks 6, 8 (soundness, completeness) stay bimodal — they connect bimodal proof system to bimodal semantics
- The existing Modal semantics (`Cube.lean`) becomes reusable for Modal/ soundness results independent of the bimodal porting

### One Strategic Addition

Consider adding a **Task 23: Temporal Kripke Semantics** that creates standalone temporal semantics on linear orders (not task frames). This would:
- Fill the gap noted in the research synthesis ("Temporal/ needs Semantics — new, not from BimodalLogic")
- Enable standalone temporal soundness proofs
- Make Temporal/ a complete standalone module (syntax + proof system + semantics + theorems)
- Position temporal logic for independent Mathlib contribution

This would be a medium-effort task (~4-6 hours), could depend on Task 22 (temporal axioms), and would NOT block the bimodal porting pipeline.

---

## Evidence/Examples

1. **CSLib's own pattern**: HML, Modal, and Linear Logic all define their own semantics independently. This is already the project convention.

2. **The FormalizedFormalLogic project** (referenced in Connectives.lean docstring): Uses the Foundation pattern with connective typeclasses for syntax but separate semantic definitions per logic family.

3. **Mathlib's model theory**: `Mathlib.ModelTheory` defines structures, languages, and interpretations in a general first-order setting. Modal/temporal logics are inherently *not* first-order (they have accessibility relations, time structures), so they can't use this framework. This confirms that semantic abstraction across logic families is not productive.

4. **The embedding lattice**: CSLib already has `PL→Modal→Bimodal` and `PL→Temporal→Bimodal` embeddings with simp lemmas. These provide the composition mechanism that a unified semantics would attempt (and fail) to provide.

5. **Bimodal truth evaluation** (Truth.lean in BimodalLogic): The `truth_at M Omega τ t φ` function takes 4 parameters and handles 6 constructors with modal quantification over shift-closed history sets. This is structurally nothing like modal `Satisfies m w φ` (2+1 parameters, 4 constructors, simple accessibility). No useful abstraction covers both.

---

## Confidence Level

**High** — based on three converging lines of evidence:

1. **Empirical**: CSLib already has 4+ logic modules with separate semantics (HML, Modal, PL, Linear Logic). The pattern is established and working.
2. **Mathematical**: The semantic structures genuinely differ (accessibility relations vs. linear orders vs. task frames). This isn't a matter of implementation convenience but structural incompatibility.
3. **Practical**: Separate semantics maximize Mathlib-contribution potential and enable independent development tracks, which is critical for a multi-contributor library.

The only scenario where unified semantics would be preferable is if CSLib were building a "logic framework" rather than a "logic library" — but the project structure (concrete logics with specific metalogical results) clearly indicates the latter.
