# Teammate C Findings: Critical Gaps and Blind Spots

**Task**: 19 — Explore modular logic factoring
**Role**: Critic
**Date**: 2026-06-08

---

## Key Findings

### Gap 1: TemporalBXHilbert is a Shell — The "~20 axiom abbrevs" Estimate is Wrong

The research synthesis claims ~20 temporal axiom `abbrev`s are needed in `Axioms.lean`. The actual BimodalLogic axiom set has **22 temporal axiom constructors** (see `Axioms.lean` lines 110–288), but the real gap is far larger than axiom definitions.

**Current state** of `TemporalBXHilbert` in `ProofSystem.lean:165-168`:
```lean
class TemporalBXHilbert (S : Type*) [HasBot F] [HasImp F] [HasUntil F]
    [HasSince F] [InferenceSystem S F]
    extends PropositionalHilbert S (F := F),
            TemporalNecessitation S (F := F)
```

It extends `PropositionalHilbert` and `TemporalNecessitation` — and **nothing else**. There are zero temporal axiom requirements. Compare to `ModalS5Hilbert` which extends `ModalHilbert` (which includes `HasAxiomK`, `Necessitation`) plus `HasAxiomT`, `HasAxiom4`, `HasAxiomB`.

**What's actually needed to fill `TemporalBXHilbert`:**

1. **Axiom `abbrev`s in `Axioms.lean`**: Currently only 2 temporal abbrevs exist (`SerialFuture`, `SerialPast`). The BimodalLogic axiom set contains at minimum these temporal axiom schemas that need abbrevs:
   - BX1/BX1': `SerialFuture`/`SerialPast` (already exist) — **2 done**
   - BX2G/BX2H: left mono G/H — **2 needed**
   - BX3/BX3': right mono event — **2 needed**
   - BX4/BX4': temporal connectedness — **2 needed**
   - BX5/BX5': self-accumulation — **2 needed**
   - BX6/BX6': absorption — **2 needed**
   - BX7/BX7': linearity — **2 needed**
   - BX10/BX10': until→F / since→P — **2 needed**
   - BX11/BX11': temporal linearity — **2 needed**
   - BX12/BX12': F-Until/P-Since bridge — **2 needed**
   - BX13/BX13': enrichment — **2 needed**

   That's **22 needed** (of which 2 exist). So the estimate is roughly correct for abbrevs.

2. **`HasAxiom*` typeclasses in `ProofSystem.lean`**: For each axiom schema, a typeclass like `HasAxiomSerialFuture`, `HasAxiomLeftMonoUntilG`, etc. must be created. That's **~20 new typeclasses** (grouping the existing 2 serial ones).

3. **`TemporalBXHilbert` must extend all of them**: The class needs to be rewritten to extend ~20 `HasAxiom*` classes.

4. **`TemporalNecessitation` is a marker class with no content**: At `ProofSystem.lean:72-73`, it's defined as:
   ```lean
   class TemporalNecessitation (S : Type*) [HasUntil F] [HasSince F]
       [InferenceSystem S F]
   ```
   This is a **marker class** — no fields, no method. Temporal necessitation (from `⊢ φ` derive `⊢ Gφ`) needs an actual method with a derivation rule. Similarly, temporal duality (from `⊢ φ` derive `⊢ swap_temporal φ`) may need a typeclass too.

**Impact**: Task 22 is significantly underestimated. The "complete temporal axiom `abbrev`s" sub-task is roughly 30% of the actual typeclass infrastructure work needed.

---

### Gap 2: Semantics Are NOT Addressed by the Plan — This is the User's Central Concern

The plan is entirely about **syntactic refactoring** (moving proof system components and derived theorems). It does not address the user's core question: **what boundaries should semantics maintain?**

**Current semantics state across repos:**

| Logic | Semantics Location | Status |
|-------|-------------------|--------|
| Propositional | CSLib `Cslib/Logics/Propositional/Defs.lean` | Theory-based (sets of propositions), NOT truth-functional |
| Modal | CSLib `Cslib/Logics/Modal/Basic.lean` | Kripke models, full: Satisfies, validity, frame correspondence |
| Temporal | **Nowhere** | Does not exist in either repo standalone |
| Bimodal | BimodalLogic `Theories/Bimodal/Semantics/` | Task frame semantics (TaskFrame, WorldHistory, truth_at) |

**Critical observations:**

1. **Temporal semantics is completely missing.** CSLib has `Temporal.Formula` but no semantics. BimodalLogic defines temporal truth only within the bimodal `truth_at` function (which takes `TaskModel`, `WorldHistory`, time `D`). There is no standalone temporal semantics.

2. **Standalone temporal semantics would look fundamentally different from bimodal semantics.** Bimodal temporal truth quantifies over world histories in a task frame. Pure temporal semantics would use truth at a point in a linear order — no worlds, no histories, no task relations. The semantic model would be:
   ```lean
   structure TemporalModel (D : Type*) [LinearOrder D] (Atom : Type*) where
     valuation : D → Atom → Prop
   
   def truth_at (M : TemporalModel D Atom) (t : D) : Temporal.Formula Atom → Prop
     | .atom p => M.valuation t p
     | .bot => False
     | .imp φ ψ => truth_at M t φ → truth_at M t ψ
     | .untl φ ψ => ∃ s, t < s ∧ truth_at M s φ ∧ ∀ r, t < r → r < s → truth_at M r ψ
     | .snce φ ψ => ∃ s, s < t ∧ truth_at M s φ ∧ ∀ r, s < r → r < t → truth_at M r ψ
   ```

3. **Temporal soundness requires temporal semantics.** Without it, Task 22's temporal theorems are syntactic-only — you can't state or prove that they're sound.

4. **Modal soundness is possible because CSLib already has Kripke semantics.** Modal theorems from Task 21 could potentially be linked to the existing `Satisfies` relation in `Modal.Basic`.

5. **Propositional soundness would need truth-table semantics or a separate development.** The existing `Theory`-based approach in `Propositional/Defs.lean` is not a truth-functional semantics.

**Recommendation**: The plan should explicitly decide:
- Is temporal semantics in scope for Task 22, or is it a separate task?
- Should the plan include a task for propositional truth-table semantics?
- Should soundness proofs be per-logic or only for the combined bimodal system?

---

### Gap 3: The Proof Portability Assumption is Partially Validated but Has Real Obstacles

The plan recommends Option 2 (port directly to typeclasses). Let me examine what this actually involves.

**BimodalLogic proofs use concrete `DerivationTree`:**

```lean
-- Combinators.lean:83-90 (imp_trans)
def imp_trans {fc : FrameClass} {A B C : Formula}
    (h1 : DerivationTree fc [] (A.imp B))
    (h2 : DerivationTree fc [] (B.imp C)) : DerivationTree fc [] (A.imp C) := by
  have s_axiom := DerivationTree.axiom (fc := fc) [] _ (Axiom.prop_s ...) ...
  have k_axiom := DerivationTree.axiom (fc := fc) [] _ (Axiom.prop_k ...) ...
  ...
```

**The generic version would be:**
```lean
theorem imp_trans [HasBot F] [HasImp F] [InferenceSystem S F] [PropositionalHilbert S (F := F)]
    {A B C : F} 
    (h1 : InferenceSystem.DerivableIn S (HasImp.imp A B))
    (h2 : InferenceSystem.DerivableIn S (HasImp.imp B C)) :
    InferenceSystem.DerivableIn S (HasImp.imp A C) := by
  have s := HasAxiomImplyK.implyK (S := S) (φ := ...) (ψ := ...)
  have k := HasAxiomImplyS.implyS (S := S) ...
  exact ModusPonens.mp (ModusPonens.mp k (ModusPonens.mp s h2)) h1
```

**Real obstacles:**

1. **Type-valued vs Prop-valued**: BimodalLogic's `Combinators.lean` uses `DerivationTree` (Type-valued) and constructs actual derivation tree terms. The generic `PropositionalHilbert` uses `DerivableIn` which is `Nonempty (S⇓a)` — Prop-valued. This means:
   - You can't pattern-match on the proof
   - You need `Classical.choice` to extract witnesses
   - All proofs become `noncomputable` unless you restructure to avoid tree extraction

2. **Formula abstraction**: BimodalLogic proofs reference `Formula.imp`, `Formula.bot` etc. directly. Generic versions must use `HasImp.imp`, `HasBot.bot` etc. This is a systematic but mechanical rewrite.

3. **Context handling**: BimodalLogic has `Context` (`List Formula`) and contextual proofs (weakening, cut). The generic version needs a generic context concept. Currently CSLib's `Foundations/Syntax/Context.lean` exists but it's unclear if it's compatible.

4. **The DeductionTheorem is the hardest to port.** It requires induction on `DerivationTree` — directly inspecting proof structure. A generic version would need either:
   - A generic `DerivationTree` in Foundations (major new infrastructure)
   - Working only at the `DerivableIn` (Prop) level, which makes the deduction theorem unprovable without axiomatizing it

**Assessment**: The propositional combinators (I, B, C, S, `imp_trans`, `identity`) are mechanically portable — they only use MP + axioms. The deeper results (deduction theorem, contextual proofs, cut) will require significant design work that isn't accounted for in the plan.

---

### Gap 4: Typeclass Diamond — Already Addressed in Connectives, But Not in ProofSystem

The `Connectives.lean:71` explicitly documents the diamond avoidance:
```lean
class BimodalConnectives (F : Type*) extends ModalConnectives F, HasUntil F, HasSince F
```
Comment: "we extend `ModalConnectives` and add `HasUntil`/`HasSince` directly rather than extending `TemporalConnectives`, to avoid a typeclass diamond."

However, the proof system hierarchy has a **structural asymmetry** that could cause issues:

- `BimodalTMHilbert` extends `ModalS5Hilbert` and `TemporalNecessitation` and `HasAxiomMF`
- But it does NOT extend `TemporalBXHilbert`

This means a theorem proven for `[TemporalBXHilbert S]` cannot be directly applied in a `[BimodalTMHilbert S]` context, because `BimodalTMHilbert` doesn't extend `TemporalBXHilbert`. You'd need an explicit instance:
```lean
instance [BimodalTMHilbert S (F := F)] : TemporalBXHilbert S (F := F) := ...
```

This instance would need to prove that `BimodalTMHilbert` satisfies all the temporal axiom requirements that `TemporalBXHilbert` demands. **If `TemporalBXHilbert` is extended with ~20 HasAxiom* classes, then `BimodalTMHilbert` must also extend all of them or provide the instance.**

**Current workaround**: Since `TemporalBXHilbert` is essentially empty (no temporal axioms), this isn't a problem today. But once Task 22 fills it out, this becomes a real architectural issue.

**Options:**
1. Make `BimodalTMHilbert` extend `TemporalBXHilbert` (risks typeclass diamond with `PropositionalHilbert`)
2. Provide a manual instance (requires repeating all axiom proofs)
3. Use a different hierarchy design

---

### Gap 5: Tableau Systems Are Entirely Out of Scope — But the User Asked About Them

The user specifically asked about "tableau systems for Propositional/, Modal/, Temporal/, and Bimodal/." The plan doesn't mention tableau at all. BimodalLogic has a bimodal tableau system (`Metalogic/Decidability/Tableau.lean`), but:

1. There is no standalone propositional tableau in either repo
2. There is no standalone modal tableau
3. There is no standalone temporal tableau
4. The bimodal tableau handles all formula constructors together

**The tableau rules are inherently per-logic:**
- Propositional rules (and/or/imp/neg decomposition) are universal
- Modal S5 rules require equivalence-class semantics
- Temporal rules require linear order structure
- The bimodal tableau combines all three with interaction

Factoring the tableau into standalone components is possible in principle (propositional rules are reusable) but is a separate design effort not addressed by Tasks 20-22.

---

## Recommended Approach

1. **Add a "Temporal Semantics" task** (or scope it within Task 22): Define `Temporal.Model`, `Temporal.Satisfies`, and basic validity. This is prerequisite to any temporal soundness.

2. **Explicitly decide the soundness boundary**: Should each standalone module (Propositional, Modal, Temporal) have its own soundness theorem? Or should soundness only be proven for the combined bimodal system? The answer shapes the entire architecture.

3. **Revise TemporalBXHilbert scope estimate**: Task 22's "complete temporal axiom abbrevs" is ~30% of the actual work. The typeclass infrastructure (HasAxiom* classes, TemporalBXHilbert restructuring, BimodalTMHilbert compatibility) is the bulk.

4. **Address the BimodalTMHilbert → TemporalBXHilbert instance gap**: Decide now whether BimodalTMHilbert should extend TemporalBXHilbert or provide a manual instance.

5. **Acknowledge the DeductionTheorem portability risk**: The plan assumes all propositional theorems port uniformly. The deduction theorem is structurally different — it requires induction on derivation trees — and may need a different approach at the generic level.

6. **Create a separate task for tableau factoring** if that's desired — it's a significant independent effort.

## Evidence/Examples

- **TemporalBXHilbert emptiness**: `ProofSystem.lean:165-168` — only extends `PropositionalHilbert` + marker `TemporalNecessitation`
- **TemporalNecessitation is contentless**: `ProofSystem.lean:72-73` — marker class with no fields
- **Only 2 of ~22 temporal axiom abbrevs exist**: `Axioms.lean:109-121` — `SerialFuture` and `SerialPast` only
- **BimodalLogic has 22 temporal axiom constructors**: `Axioms.lean:116-288` — see Layer 3 BX Temporal section
- **No temporal semantics in CSLib**: Only `Temporal/Syntax/Formula.lean` exists
- **BimodalTMHilbert does not extend TemporalBXHilbert**: `ProofSystem.lean:171-175`
- **DerivationTree proofs are Type-valued**: `Combinators.lean:83-90` uses pattern-matching construction
- **Generic DerivableIn is Prop-valued**: `InferenceSystem.lean:45` — `Nonempty (S⇓a)`
- **Bimodal tableau rules** are logic-coupled: `Tableau.lean:17-48` — propositional, modal, and temporal rules are all constructors of one `TableauRule` type

## Confidence Level

**High**. Every gap identified is backed by direct code inspection of the specific files and line numbers. The gaps are structural (missing types, missing instances, asymmetric hierarchies) not speculative. The most critical finding — the soundness boundary question — is confirmed by the complete absence of temporal semantics in both repos at the standalone level.
