# Research Report: Propositional Completeness Integration (Task 118)

## Summary

Task 118 requires three deliverables:
1. Update `Cslib.lean` imports to include all new propositional metalogic modules
2. Prove a semantic coherence theorem connecting propositional tautology to modal validity
3. Verify all completeness theorems are sorry-free with standard axioms only

All three deliverables are achievable. The coherence theorem has been prototyped and compiles successfully at ~25 lines. The build passes clean with no sorry or non-standard axioms in any of the completeness theorems.

## 1. Missing Imports in Cslib.lean

### Currently Present (Propositional section, lines 300-311)
```
Cslib.Logics.Propositional.Defs
Cslib.Logics.Propositional.Metalogic.DeductionTheorem
Cslib.Logics.Propositional.Metalogic.MCS
Cslib.Logics.Propositional.NaturalDeduction.Basic
Cslib.Logics.Propositional.NaturalDeduction.DerivedRules
Cslib.Logics.Propositional.NaturalDeduction.Equivalence
Cslib.Logics.Propositional.NaturalDeduction.FromHilbert
Cslib.Logics.Propositional.NaturalDeduction.HilbertDerivedRules
Cslib.Logics.Propositional.ProofSystem.Axioms
Cslib.Logics.Propositional.ProofSystem.Derivation
Cslib.Logics.Propositional.ProofSystem.Instances
Cslib.Logics.Propositional.ProofSystem.IntMinInstances  (already added by task 113)
```

### Missing Imports (8 files to add)
```
Cslib.Logics.Propositional.Semantics.Basic         (task 114)
Cslib.Logics.Propositional.Semantics.Kripke         (task 115)
Cslib.Logics.Propositional.Metalogic.Soundness      (task 114)
Cslib.Logics.Propositional.Metalogic.Completeness   (task 114)
Cslib.Logics.Propositional.Metalogic.IntSoundness   (task 116)
Cslib.Logics.Propositional.Metalogic.IntLindenbaum  (task 116)
Cslib.Logics.Propositional.Metalogic.IntCompleteness (task 116)
Cslib.Logics.Propositional.Metalogic.MinSoundness   (task 117)
Cslib.Logics.Propositional.Metalogic.MinLindenbaum  (task 117)
Cslib.Logics.Propositional.Metalogic.MinCompleteness (task 117)
```

### Insertion Point

Insert **after line 302** (after `Cslib.Logics.Propositional.Metalogic.MCS`) in alphabetical/logical order within each group:

- Semantics group: insert between `Defs` and `Metalogic` entries (after line 300, before line 301)
- Metalogic group: insert after `MCS` (after line 302, before NaturalDeduction)

Recommended insertion order within `Cslib.lean` (maintaining the existing pattern of grouping by subdirectory):

```
public import Cslib.Logics.Propositional.Defs
public import Cslib.Logics.Propositional.Metalogic.Completeness
public import Cslib.Logics.Propositional.Metalogic.DeductionTheorem
public import Cslib.Logics.Propositional.Metalogic.IntCompleteness
public import Cslib.Logics.Propositional.Metalogic.IntLindenbaum
public import Cslib.Logics.Propositional.Metalogic.IntSoundness
public import Cslib.Logics.Propositional.Metalogic.MCS
public import Cslib.Logics.Propositional.Metalogic.MinCompleteness
public import Cslib.Logics.Propositional.Metalogic.MinLindenbaum
public import Cslib.Logics.Propositional.Metalogic.MinSoundness
public import Cslib.Logics.Propositional.Metalogic.Soundness
public import Cslib.Logics.Propositional.NaturalDeduction.Basic
...
public import Cslib.Logics.Propositional.ProofSystem.IntMinInstances
public import Cslib.Logics.Propositional.Semantics.Basic
public import Cslib.Logics.Propositional.Semantics.Kripke
```

## 2. Semantic Coherence Theorem

### Design

The coherence theorem connects two semantics:
- **Propositional**: `PL.Evaluate (v : Atom -> Prop) (phi : PL.Proposition Atom) : Prop`
- **Modal**: `Modal.Satisfies (m : Modal.Model World Atom) (w : World) (phi.toModal : Modal.Proposition Atom) : Prop`

The key insight is that `toModal` maps `atom/bot/imp` to `atom/bot/imp` (never introducing `box`), so `Modal.Satisfies m w phi.toModal` depends **only on `m.v w`**, not on the accessibility relation. This makes the connection exact.

### Theorem Statements (4 theorems, ~25 lines total)

1. **Bridge Lemma** (`modal_satisfies_toModal_iff_evaluate`):
   ```
   Modal.Satisfies m w phi.toModal <-> PL.Evaluate (m.v w) phi
   ```
   Proof: structural induction on `phi` (3 cases: atom, bot, imp). Each base case is `rfl`. The imp case uses `Iff.intro` with the inductive hypotheses.

2. **Forward Direction** (`tautology_toModal_valid`):
   ```
   PL.Tautology phi -> Modal.Satisfies m w phi.toModal
   ```
   Proof: apply bridge lemma backward, then instantiate the tautology at `m.v w`.

3. **Backward Direction** (`toModal_valid_implies_tautology`):
   ```
   (forall World m w, Modal.Satisfies m w phi.toModal) -> PL.Tautology phi
   ```
   Proof: given valuation `v`, construct trivial model `<fun _ _ => False, fun _ => v>` over `Unit`, apply bridge lemma forward.

4. **Full Coherence** (`tautology_iff_toModal_valid`):
   ```
   PL.Tautology phi <-> (forall (World : Type) m w, Modal.Satisfies m w phi.toModal)
   ```

### Location

These theorems should go in **`Cslib/Logics/Modal/FromPropositional.lean`** since that file already defines `toModal` and the simp lemmas for it. The file currently imports `Cslib.Logics.Propositional.Defs` and `Cslib.Logics.Modal.Basic`. To add the coherence theorem, it needs one additional import: `Cslib.Logics.Propositional.Semantics.Basic` (for `Evaluate` and `Tautology`).

### Universe Considerations

- The forward direction (`tautology_toModal_valid`) works for any `World : Type*` (universe-polymorphic).
- The backward direction (`toModal_valid_implies_tautology`) quantifies over `World : Type` (universe 0) to allow constructing the witness `Unit` model. This is not a restriction in practice since the biconditional quantifies at the same level.

### Prototype (verified compiles)

```lean
theorem modal_satisfies_toModal_iff_evaluate
    {World : Type*} {Atom : Type*}
    (m : Modal.Model World Atom) (w : World)
    (phi : PL.Proposition Atom) :
    Modal.Satisfies m w phi.toModal <-> PL.Evaluate (m.v w) phi := by
  induction phi with
  | atom p => rfl
  | bot => rfl
  | imp phi psi ih1 ih2 =>
    simp only [PL.Proposition.toModal, Modal.Satisfies, PL.Evaluate]
    exact <| fun h he => ih2.mp (h (ih1.mpr he)),
             fun h hm => ih2.mpr (h (ih1.mp hm)) |>

theorem tautology_toModal_valid {Atom : Type*}
    {phi : PL.Proposition Atom} (h : PL.Tautology phi)
    {World : Type*} (m : Modal.Model World Atom) (w : World) :
    Modal.Satisfies m w phi.toModal :=
  (modal_satisfies_toModal_iff_evaluate m w phi).mpr (h (m.v w))

theorem toModal_valid_implies_tautology {Atom : Type*}
    {phi : PL.Proposition Atom}
    (h : forall (World : Type) (m : Modal.Model World Atom) (w : World),
      Modal.Satisfies m w phi.toModal) :
    PL.Tautology phi := by
  intro v
  let m : Modal.Model Unit Atom := <| fun _ _ => False, fun _ => v |>
  exact (modal_satisfies_toModal_iff_evaluate m () phi).mp (h Unit m ())

theorem tautology_iff_toModal_valid {Atom : Type*}
    {phi : PL.Proposition Atom} :
    PL.Tautology phi <->
    (forall (World : Type) (m : Modal.Model World Atom) (w : World),
      Modal.Satisfies m w phi.toModal) :=
  <| fun h _ m w => tautology_toModal_valid h m w, toModal_valid_implies_tautology |>
```

## 3. Verification Results

### Axiom Checks (lean_verify)

All completeness/soundness theorems verified with no sorry and only standard axioms:

| Theorem | Axioms | Sorry |
|---------|--------|-------|
| `prop_completeness` | propext, Classical.choice, Quot.sound | None |
| `completeness_iff_tautology` | propext, Classical.choice, Quot.sound | None |
| `soundness_tautology` | propext, Classical.choice, Quot.sound | None |
| `int_completeness` | propext, Classical.choice, Quot.sound | None |
| `int_soundness_completeness` | propext, Classical.choice, Quot.sound | None |
| `int_soundness_derivable` | (none) | None |
| `min_completeness` | propext, Classical.choice, Quot.sound | None |
| `min_soundness_completeness` | propext, Classical.choice, Quot.sound | None |
| `min_soundness_derivable` | (none) | None |

The axioms used are all standard Lean 4 / Mathlib axioms:
- `propext`: Propositional extensionality (built-in)
- `Classical.choice`: Classical choice (used for `by_contra`)
- `Quot.sound`: Quotient soundness (built-in)

### Full Build

`lake build` passes with 2957 jobs, only warnings about deprecated `push_neg` in temporal logic files (unrelated).

## 4. Implementation Plan

### Phase 1: Add imports to Cslib.lean (~5 min)

Insert the 8 missing imports (Semantics.Basic, Semantics.Kripke, Soundness, Completeness, IntSoundness, IntLindenbaum, IntCompleteness, MinSoundness, MinLindenbaum, MinCompleteness) at the correct positions in `Cslib.lean`, maintaining alphabetical order within subdirectory groups.

### Phase 2: Add coherence theorem to FromPropositional.lean (~10 min)

1. Add `public import Cslib.Logics.Propositional.Semantics.Basic` to the imports
2. Add the 4 theorems (bridge lemma + forward + backward + biconditional) after the existing `toModal_neg` theorem
3. ~25 lines of new code

### Phase 3: Verify (~5 min)

1. `lake build` to confirm everything compiles
2. `lean_verify` on the new theorems to confirm no sorry, no non-standard axioms

### Risks

- **None identified**: The prototype compiles, the imports exist, and the build is clean. No new dependencies beyond what already exists.

## 5. File Dependency Graph

```
Semantics.Basic -----> Soundness -----> Completeness
       |                                    |
       |           (uses MCS, DT)           |
       v                                    v
Semantics.Kripke -> IntSoundness -------> IntCompleteness
       |                                    |
       |           (uses IntLindenbaum)     |
       v                                    v
Semantics.Kripke -> MinSoundness -------> MinCompleteness
                    (uses MinLindenbaum)

FromPropositional + Semantics.Basic --> Coherence Theorems
```
