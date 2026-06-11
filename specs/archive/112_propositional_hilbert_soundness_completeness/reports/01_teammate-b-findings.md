# Teammate B Findings: Formalized Proof Patterns for Propositional Soundness and Completeness

**Task**: 112 — Establish soundness and completeness for the propositional Hilbert proof systems
**Teammate**: B (Alternative Approaches — Formalized Proof Patterns)
**Date**: 2026-06-11

---

## Key Findings

### 1. Mathlib Has No Ready-Made Propositional Completeness to Reuse

Lean 4 Mathlib does **not** contain a formalized soundness or completeness theorem for a
Hilbert-style propositional proof system using the `atom/bot/imp` formula language that cslib
employs. Searches via `lean_leansearch`, `lean_loogle`, and `lean_leanfinder` confirm this.

What Mathlib does contain that is adjacent:
- `Classical.prop_complete`: `∀ (a : Prop), a = True ∨ a = False` — this is a metamathematical
  fact about Lean's `Prop` universe, not a formalized completeness theorem.
- `Mathlib.Tactic.Tauto` / `tauto`: A tactic that decides propositional tautologies at the
  Lean meta-level.
- `Sat.Valuation` (in `Mathlib.Tactic.Sat.FromLRAT`): A propositional valuation type used
  internally by the `sat` tactic, assigning truth values to natural-number-indexed atoms. This
  is not connected to any Hilbert derivation system.
- `FirstOrder.Language.Theory.IsMaximal` / `CompleteType`: MCS-like structures for first-order
  logic, not propositional.

**Conclusion**: No Mathlib lemma directly reduces the implementation burden for this task.

### 2. The Codebase Already Has All the Syntactic Infrastructure

The `Cslib.Logic.PL` namespace already contains a complete Hilbert-style proof system:

| File | Content |
|------|---------|
| `Propositional/Defs.lean` | `Proposition Atom` type (atom/bot/imp), derived connectives, `Theory` |
| `ProofSystem/Axioms.lean` | `PropositionalAxiom` (implyK, implyS, efq, peirce) |
| `ProofSystem/Derivation.lean` | `DerivationTree`, `Deriv`, `Derivable`, `propDerivationSystem` |
| `ProofSystem/Instances.lean` | `InferenceSystem`, `ClassicalHilbert` instances for `HilbertCl` |
| `Metalogic/DeductionTheorem.lean` | Full deduction theorem by well-founded recursion |
| `Metalogic/MCS.lean` | `PropSetConsistent`, `PropSetMaximalConsistent`, `prop_lindenbaum`, MCS properties |

**Critical observation**: `Metalogic/MCS.lean` already provides:
- `prop_lindenbaum`: every consistent set extends to an MCS
- `prop_closed_under_derivation`: derivable formulas are in any MCS
- `prop_implication_property`: MP reflected into membership
- `prop_negation_complete`: every MCS contains φ or ¬φ
- `prop_mcs_bot_not_mem`, `prop_mcs_neg_of_not_mem`, `prop_mcs_not_mem_of_neg`, `prop_mcs_mem_iff_neg_not_mem`

**The only missing component is propositional semantics** (valuations + satisfaction + tautology).

### 3. The Modal Pattern Is the Direct Template

The modal soundness/completeness infrastructure is the exact model to follow. The correspondence
is nearly one-to-one:

| Modal Component | Propositional Analog | Status |
|----------------|---------------------|--------|
| `Model World Atom` (world + relation + valuation) | `Valuation Atom` (just atom → Prop) | **MISSING** |
| `Satisfies m w φ` (recursive over modal formula) | `Evaluate v φ` (recursive over PL formula) | **MISSING** |
| `Valid φ` (∀ m w, Satisfies m w φ) | `Tautology φ` (∀ v, Evaluate v φ) | **MISSING** |
| `Modal/Metalogic/Soundness.lean` (parameterized soundness) | `PL/Metalogic/Soundness.lean` | **MISSING** |
| `CanonicalWorld Axioms` (= MCS subtype) | `CanonicalValuation Axioms` (= MCS → Prop) | **MISSING** |
| `truth_lemma` (for modal/box) | `pl_truth_lemma` (no box case) | **MISSING** |
| `KCompleteness.lean` / `completeness` | `PLCompleteness.lean` / `pl_completeness` | **MISSING** |

The propositional case is **strictly simpler** than modal:
- No box/diamond formula constructors → no modal accessibility relation
- No necessitation rule in `DerivationTree` → deduction theorem has 4 constructors not 5
- No box witness lemma needed → truth lemma for `imp` is the only non-trivial case
- Canonical "model" is just a function `Atom → Prop` (MCS membership), not a Kripke structure

### 4. Semantics Definition Strategy

The propositional semantics should be defined in a new file
`Cslib/Logics/Propositional/Semantics/Basic.lean` following the modal pattern:

```lean
-- Valuation: truth assignment to atoms
def Valuation (Atom : Type*) := Atom → Prop

-- Evaluation: recursive satisfaction
def Evaluate (v : Valuation Atom) : PL.Proposition Atom → Prop
  | .atom p => v p
  | .bot    => False
  | .imp φ ψ => Evaluate v φ → Evaluate v ψ

-- Tautology: true under all valuations
def Tautology (φ : PL.Proposition Atom) : Prop :=
  ∀ (v : Valuation Atom), Evaluate v φ
```

This is the minimal semantics needed. It mirrors how `Satisfies` works in `Modal/Basic.lean`
for `atom` and `bot` and `imp` (dropping the `box` case).

### 5. Soundness Pattern (Straightforward)

The parameterized soundness theorem from `Modal/Metalogic/Soundness.lean` applies directly.
For propositional logic, the proof is:
- **Axiom case**: verify each of implyK, implyS, efq, peirce is a tautology (trivial by unfolding)
- **MP case**: immediate by definition of `Evaluate` for `imp`
- **Assumption case**: follow from context hypothesis
- **Weakening case**: immediate

The modal `soundness` theorem structure (induction on `DerivationTree`) copies verbatim with
the box/necessitation cases removed. Expected code: ~30 lines.

### 6. Completeness Pattern (The Key Insight — No Box Witness Needed)

For modal K/T/S5 completeness, the hardest step is the **box witness lemma**
(`mcs_box_witness`, `k_mcs_box_witness`): given `□φ ∉ S`, find an MCS `T` with `S R T` and
`φ ∉ T`. This requires building a witness world in the canonical model.

**For propositional completeness, this case does not exist.** The formula type has no `box`
constructor. The truth lemma only needs cases for `atom`, `bot`, and `imp`.

The completeness proof structure mirrors `k_completeness` in `KCompleteness.lean`:

```
theorem pl_completeness (φ : PL.Proposition Atom)
    (h_valid : ∀ v : Valuation Atom, Evaluate v φ) :
    Derivable φ := by
  by_contra h_not_deriv
  -- 1. {¬φ} is consistent (by contrapositive: if φ derivable, done)
  -- 2. Extend to MCS M by prop_lindenbaum
  -- 3. Define canonical valuation: v_M p := (atom p ∈ M)
  -- 4. Apply truth lemma: Evaluate v_M φ ↔ φ ∈ M
  -- 5. Contradiction: φ ∈ M (from h_valid) but ¬φ ∈ M (from construction)
```

The **canonical valuation** for propositional completeness is:
```lean
noncomputable def canonicalValuation (M : PropMCS) : Valuation Atom :=
  fun p => PL.Proposition.atom p ∈ M.val
```

This is the direct propositional analog of `CanonicalModel.v S p := Proposition.atom p ∈ S.val`
in `Modal/Metalogic/Completeness.lean`.

### 7. Truth Lemma Structure (All Recursive Cases Are Simple)

The propositional truth lemma:
```
∀ φ, Evaluate (canonicalValuation M) φ ↔ φ ∈ M.val
```

Case analysis:
- `atom p`: both sides are `atom p ∈ M` by definition of `canonicalValuation` — trivial
- `bot`: both sides are `False` — use `prop_mcs_bot_not_mem`
- `imp φ ψ`: `Evaluate v (φ → ψ) ↔ (φ → ψ) ∈ M` — uses `prop_implication_property` and
  `prop_negation_complete`; exact analog of the `imp` case in `k_truth_lemma`

**No `box` case** → no existence lemma, no box-witness construction, no accessibility reasoning.
The truth lemma is significantly shorter than the modal version.

The `imp` direction (→) follows the modal pattern exactly:
- Assume `Evaluate v φ → Evaluate v ψ` and that `(φ → ψ) ∉ M`
- By `prop_negation_complete`, `¬(φ → ψ) ∈ M`, which is `φ ∈ M ∧ ψ ∉ M` (via MCS)
- By IH: `Evaluate v φ` holds, so `Evaluate v ψ` holds, so `ψ ∈ M` — contradiction

The `imp` direction (←) is trivial via `prop_implication_property`.

### 8. File Layout Recommendation

New files should be:

```
Cslib/Logics/Propositional/Semantics/
  Basic.lean           -- Valuation, Evaluate, Tautology
Cslib/Logics/Propositional/Metalogic/
  Soundness.lean       -- axiom_sound, soundness, soundness_derivable
  Completeness.lean    -- CanonicalValuation, pl_truth_lemma, pl_completeness
```

This exactly mirrors:
```
Cslib/Logics/Modal/Basic.lean              -- Model, Satisfies
Cslib/Logics/Modal/Metalogic/Soundness.lean
Cslib/Logics/Modal/Metalogic/Completeness.lean
```

The `Cslib.lean` top-level module file will need to import these new modules.

### 9. Other ITP Formalizations (Coq, Isabelle)

Web searches and knowledge confirm:

- **Isabelle/HOL**: The Isabelle AFP contains "A Sequent Calculus for Classical Logic"
  (Berghofer) and various propositional completeness formalizations, but they use sequent
  calculi, not Hilbert systems with `atom/bot/imp`.

- **Coq/MathComp**: The `Logic` library in Coq and `compcert` contain propositional
  formalizations, but the formula inductive type and axiom system differ significantly.

- **Other Lean 4 projects**: The `lean4-logic` community project (Iijima et al.) on GitHub has
  propositional and modal logic formalizations, but the formula language and proof system do not
  match cslib's `PL.Proposition` type or the generic `DerivationTree` pattern.

**Assessment**: None of the external formalizations provide drop-in lemmas. The closest
patterns are already in-codebase (the modal completeness infrastructure).

---

## Recommended Approach

**Recommended strategy**: Adapt the in-codebase modal pattern directly.

1. **Phase 1** — Create `Cslib/Logics/Propositional/Semantics/Basic.lean` with `Valuation`,
   `Evaluate`, `Tautology`. This is ~30 lines. No proofs needed in this file.

2. **Phase 2** — Create `Cslib/Logics/Propositional/Metalogic/Soundness.lean` with:
   - `pl_axiom_sound` (verify implyK/implyS/efq/peirce are tautologies)
   - Parameterized `pl_soundness` (induction on `DerivationTree`)
   - `pl_soundness_derivable` (wrapper for empty context)

3. **Phase 3** — Create `Cslib/Logics/Propositional/Metalogic/Completeness.lean` with:
   - `CanonicalValuation` (maps MCS M to `Atom → Prop` via atom membership)
   - `pl_truth_lemma` (induction on formula structure; three cases)
   - `pl_completeness` (by contradiction via Lindenbaum + truth lemma)
   - `pl_iff_tautology` (soundness + completeness combined)

**Do NOT attempt**: Adapting external Isabelle/Coq formalizations. The in-codebase modal
pattern is the correct and direct template, and the propositional case is strictly simpler.

**Confidence**: Very high. The modal completeness proofs are all present and verified. The
propositional case removes the box/necessitation dimension without adding new complexity.

---

## Evidence / Examples

### Key Local Declarations Verified

```
Cslib.Logic.PL.Derivable              -- Derivable φ = Deriv [] φ
Cslib.Logic.PL.propDerivationSystem   -- DerivationSystem instance
Cslib.Logic.PL.prop_lindenbaum        -- Every consistent set → MCS
Cslib.Logic.PL.prop_negation_complete -- φ ∈ S ∨ ¬φ ∈ S
Cslib.Logic.PL.prop_mcs_bot_not_mem   -- ⊥ ∉ MCS
Cslib.Logic.PL.prop_implication_property -- MP reflected into membership
Cslib.Logic.PL.prop_has_deduction_theorem -- HasDeductionTheorem instance
```

All confirmed present via `lean_local_search` and direct file reads.

### Pattern Match: Modal → Propositional

The `k_truth_lemma` in `KCompleteness.lean` (lines 168–261) is the direct model for
`pl_truth_lemma`. The `atom` and `imp` cases transfer verbatim (modulo namespace). The `bot`
case is identical. The `box` case is dropped entirely.

The `k_completeness` theorem (lines 269–323) transfers with:
- `KAxiom` → `PropositionalAxiom`  
- `CanonicalWorld` (subtype of MCS) → `PropMCS` (using existing `PropSetMaximalConsistent`)
- `CanonicalModel.v S p` → `canonicalValuation M p := atom p ∈ M`
- The consistency argument (lines 276–307) is identical structure
- No `canonical_refl/trans/eucl` frame conditions needed

---

## Confidence Level

**High** for all components:

- The syntactic infrastructure (derivation trees, MCS, deduction theorem) is already complete
  and verified.
- The semantic layer (Valuation, Evaluate) is trivial to define — a simplification of the modal
  `Satisfies` with no box/world component.
- Soundness is a straightforward induction on derivation trees.
- Completeness follows the modal K pattern with the box witness case removed.
- No sorry-free blockers are anticipated.

The only genuine proof work is:
1. The `imp` direction of the truth lemma (non-trivial but has a direct modal precedent)
2. Confirming the consistency argument in `pl_completeness` type-checks against `PropositionalAxiom`
   (rather than `KAxiom`)

Estimated total implementation: 150–250 lines across three files.
