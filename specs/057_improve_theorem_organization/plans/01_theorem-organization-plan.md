# Implementation Plan: Task #57

- **Task**: 57 - Improve theorem organization: move misplaced generic theorems to Foundations and eliminate concrete duplicates in Bimodal
- **Status**: [NOT STARTED]
- **Effort**: 4 hours
- **Dependencies**: None
- **Research Inputs**: specs/057_improve_theorem_organization/reports/01_theorem-organization-research.md
- **Artifacts**: plans/01_theorem-organization-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: true

## Overview

This plan reorganizes theorem files in the cslib Lean 4 repository to place generic theorems at the correct abstraction level and eliminate ~600 lines of redundant concrete proofs. Two fully generic files (`TemporalDerived.lean` and `FrameConditions.lean`) are moved from `Logics/Temporal/Theorems/` to `Foundations/Logic/Theorems/Temporal/`. Then 32 redundant concrete theorems across three Bimodal files are replaced with 1-line wrap/unwrap bridge wrappers that delegate to the generic Foundations equivalents, while preserving all API signatures so downstream consumers remain unaffected. Eight theorems that genuinely require concrete types are retained as-is.

### Research Integration

The research report (01_theorem-organization-research.md) provided:
- Complete import dependency map for all affected files (Section 1)
- Theorem-by-theorem overlap analysis confirming 32 of 40 theorems are redundant (Section 3)
- Identification of 8 concrete-only theorems that must be kept (Section 7)
- Validation of the wrap/unwrap bridge pattern already used in `Perpetuity/Helpers.lean` (Section 4)
- FrameClass lifting pattern: `DerivationTree.lift (FrameClass.base_le fc)` for `fc`-polymorphic theorems (Section 10.1)
- Confirmation of zero namespace conflicts for the proposed moves (Section 5)

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

Aligns with the Foundations module organization effort. Moving generic temporal theorems to Foundations strengthens the modular architecture where content lives at the most general level it can compile at.

## Goals & Non-Goals

**Goals**:
- Move `TemporalDerived.lean` and `FrameConditions.lean` to `Foundations/Logic/Theorems/Temporal/`
- Replace 32 redundant concrete theorem proofs in Bimodal with wrap/unwrap bridge wrappers
- Preserve all API signatures (function names, types) so no downstream consumer changes are needed
- Achieve clean `lake build` after each phase

**Non-Goals**:
- Refactoring the 8 concrete-only theorems (they must remain as-is)
- Changing any downstream Metalogic files beyond import path updates
- Moving the Bimodal theorem files themselves (they stay in `Logics/Bimodal/Theorems/`)
- Creating new generic Foundations theorems (all needed ones already exist)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `noncomputable` propagation breaks downstream | H | L | Perpetuity/Helpers.lean already uses `noncomputable section` with the same pattern; verify downstream files also use `noncomputable` |
| Bridge wrappers change definitional equality | M | M | Bridge wrappers are `noncomputable def`, not `theorem`; downstream uses `DerivationTree` values opaquely (never reduce). Verify no `rfl`-dependent proofs exist |
| `fc`-polymorphic lift pattern fails for some theorem | H | L | The `unwrap + lift` pattern is proven to work in Perpetuity/Helpers.lean and Combinators.lean itself (see `pairing` using `.lift`). Test each wrapper immediately |
| Barrel import changes break transitive imports | M | L | Update barrel files atomically with the file moves; run `lake build` after each phase |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |

Phases within the same wave can execute in parallel.

### Phase 1: Move Generic Temporal Files to Foundations [COMPLETED]

**Goal**: Relocate `TemporalDerived.lean` and `FrameConditions.lean` to `Foundations/Logic/Theorems/Temporal/` and update all imports.

**Tasks**:
- [ ] Create directory `Cslib/Foundations/Logic/Theorems/Temporal/`
- [ ] Move `Cslib/Logics/Temporal/Theorems/TemporalDerived.lean` to `Cslib/Foundations/Logic/Theorems/Temporal/TemporalDerived.lean` (no content changes needed -- namespace `Cslib.Logic.Theorems.Temporal.TemporalDerived` already matches the Foundations convention)
- [ ] Move `Cslib/Logics/Temporal/Theorems/FrameConditions.lean` to `Cslib/Foundations/Logic/Theorems/Temporal/FrameConditions.lean` (no content changes needed -- namespace `Cslib.Logic.Temporal.FrameConditions` is independent of file path)
- [ ] Update `Cslib/Foundations/Logic/Theorems.lean` (barrel): add `import Cslib.Foundations.Logic.Theorems.Temporal.TemporalDerived` and `import Cslib.Foundations.Logic.Theorems.Temporal.FrameConditions`
- [ ] Update `Cslib/Logics/Temporal/Theorems.lean` (barrel): change import paths from `Cslib.Logics.Temporal.Theorems.TemporalDerived` to `Cslib.Foundations.Logic.Theorems.Temporal.TemporalDerived`, and similarly for `FrameConditions`
- [ ] Update `Cslib/Logics/Bimodal/Theorems/Perpetuity/Principles.lean`: change `import Cslib.Logics.Temporal.Theorems.TemporalDerived` to `import Cslib.Foundations.Logic.Theorems.Temporal.TemporalDerived`
- [ ] Run `lake exe mk_all` to register new module paths in `Cslib.lean`
- [ ] Run `lake build` to verify zero errors

**Timing**: 0.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Foundations/Logic/Theorems/Temporal/TemporalDerived.lean` - new file (moved)
- `Cslib/Foundations/Logic/Theorems/Temporal/FrameConditions.lean` - new file (moved)
- `Cslib/Foundations/Logic/Theorems.lean` - add two barrel imports
- `Cslib/Logics/Temporal/Theorems.lean` - update two import paths
- `Cslib/Logics/Bimodal/Theorems/Perpetuity/Principles.lean` - update one import path

**Verification**:
- `lake build` passes with zero errors
- `grep -r "Logics.Temporal.Theorems.TemporalDerived" Cslib/` returns zero hits (old path fully removed)
- `grep -r "Logics.Temporal.Theorems.FrameConditions" Cslib/` returns zero hits (old path fully removed)

---

### Phase 2: Replace Redundant Bimodal Theorems with Bridge Wrappers [COMPLETED]

**Goal**: Replace 32 redundant concrete theorem implementations in three Bimodal files with wrap/unwrap bridge wrappers that delegate to Foundations generic equivalents, preserving all API signatures.

**Tasks**:
- [ ] **2a: Refactor `Combinators.lean`** (11 of 12 theorems):
  - Add `import Cslib.Logics.Bimodal.ProofSystem.Instances` (provides typeclass instances for `HilbertTM`)
  - Add `import Cslib.Foundations.Logic.Theorems.Combinators` (provides generic equivalents)
  - Add local `wrap`/`unwrap` helper definitions (same pattern as `Perpetuity/Helpers.lean`)
  - Wrap entire file in `noncomputable section`
  - Replace each of the 11 redundant theorems with the bridge pattern:
    ```lean
    def identity {fc : FrameClass} (A : Formula Atom) : DerivationTree fc [] (A.imp A) :=
      DerivationTree.lift (FrameClass.base_le fc)
        (unwrap (@Theorems.Combinators.identity _ _ _ Bimodal.HilbertTM _ _ A))
    ```
  - Keep `temp_future_derived` unchanged (uses concrete modal axioms)
  - Remove imports that are no longer needed (`Cslib.Logics.Bimodal.Syntax.Formula` may still be needed for `Formula Atom` type)
  - Theorems to replace: `imp_trans`, `mp`, `identity`, `b_combinator`, `theorem_flip`, `theorem_app1`, `theorem_app2`, `pairing`, `dni`, `combine_imp_conj`, `combine_imp_conj_3` *(deviation: altered -- `mp` kept as-is since it is a trivial 1-line wrapper with no Foundations equivalent; `combine_imp_conj` and `combine_imp_conj_3` use bridged primitives internally but retain structural logic for S-axiom application)*
- [ ] **2b: Refactor `Propositional/Core.lean`** (9 of 14 theorems):
  - Add `import Cslib.Logics.Bimodal.ProofSystem.Instances`
  - Add `import Cslib.Foundations.Logic.Theorems.Propositional.Core`
  - Add local `wrap`/`unwrap` helpers (or import from a shared location)
  - Wrap redundant section in `noncomputable section`
  - Replace 9 theorems: `lem`, `efq_axiom`, `peirce_axiom`, `double_negation`, `raa`, `efq_neg`, `rcp`, `lce_imp`, `rce_imp` *(deviation: altered -- `rcp` kept as-is because its signature includes context parameter `Gamma` and fc-polymorphism with a derivation input, which has no direct Foundations equivalent; 8 of 9 were bridged)*
  - Keep 5 concrete theorems unchanged: `ecq`, `ldi`, `rdi`, `lce`, `rce`
  - Note: `rcp` in Bimodal takes explicit `Gamma` parameter but the Foundations version works with empty context -- verify the Bimodal `rcp` is called with `[]` context only, or adapt the bridge accordingly
- [ ] **2c: Refactor `Propositional/Connectives.lean`** (12 of 14 theorems):
  - Add `import Cslib.Logics.Bimodal.ProofSystem.Instances`
  - Add `import Cslib.Foundations.Logic.Theorems.Propositional.Connectives`
  - Add local `wrap`/`unwrap` helpers
  - Wrap redundant section in `noncomputable section`
  - Replace 12 theorems: `classical_merge`, `iff_intro`, `contrapose_imp`, `contraposition`, `contrapose_iff`, `iff_neg_intro`, `demorgan_conj_neg_forward`, `demorgan_conj_neg_backward`, `demorgan_conj_neg`, `demorgan_disj_neg_forward`, `demorgan_disj_neg_backward`, `demorgan_disj_neg`
  - Keep 2 concrete theorems unchanged: `iff_elim_left`, `iff_elim_right`
- [ ] Run `lake build` after completing all three files to verify zero errors

**Timing**: 2.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Bimodal/Theorems/Combinators.lean` - replace 11 theorem bodies with bridge wrappers, add Instances import
- `Cslib/Logics/Bimodal/Theorems/Propositional/Core.lean` - replace 9 theorem bodies with bridge wrappers, add Instances import
- `Cslib/Logics/Bimodal/Theorems/Propositional/Connectives.lean` - replace 12 theorem bodies with bridge wrappers, add Instances import

**Verification**:
- `lake build` passes with zero errors
- All 32 replaced theorems compile and have identical type signatures to the originals
- The 8 retained concrete theorems (`temp_future_derived`, `ecq`, `ldi`, `rdi`, `lce`, `rce`, `iff_elim_left`, `iff_elim_right`) remain unchanged
- No downstream files require modification (API signatures preserved)

**Key Technical Details**:

The bridge pattern for `fc`-polymorphic theorems (most theorems in Combinators.lean):
```lean
noncomputable def imp_trans {fc : FrameClass} {A B C : Formula Atom}
    (h1 : DerivationTree fc [] (A.imp B))
    (h2 : DerivationTree fc [] (B.imp C)) : DerivationTree fc [] (A.imp C) :=
  DerivationTree.lift (FrameClass.base_le fc)
    (unwrap (Theorems.Combinators.imp_trans (wrap (h1.lift (le_refl fc) |>.lift ...)) ...))
```

However, the simpler approach (following Perpetuity/Helpers.lean exactly) is to:
1. First `lift` inputs down to `.Base` if needed, OR
2. Produce the result at `.Base` and then `lift` to `fc`

Since `h1 : DerivationTree fc [] (...)` cannot be directly downcast to `.Base`, the correct pattern is:
1. Call the Foundations generic theorem (which produces an abstract `InferenceSystem.DerivableIn HilbertTM` result -- no dependency on inputs)
2. `unwrap` to get `DerivationTree .Base [] ...`
3. `lift (FrameClass.base_le fc)` to get `DerivationTree fc [] ...`

For theorems that take derivation tree *inputs* (like `imp_trans`), the inputs are not needed by the generic version -- the generic version only needs the *existence* (Nonempty) of the derivation. So `wrap` converts input derivations to `Nonempty` terms, the generic theorem produces a `Nonempty` result, and `unwrap + lift` produces the concrete output.

Wait -- `wrap` as defined in Helpers.lean converts `DerivationTree .Base [] phi` to `Nonempty`, but inputs here are `DerivationTree fc [] phi`. The agent must handle this by:
- For theorems with no derivation inputs (like `identity`, `lem`, `dni`): straightforward `unwrap + lift`
- For theorems with derivation inputs (like `imp_trans`, `mp`): need to first lift inputs to abstract level. Since `InferenceSystem.DerivableIn HilbertTM phi` is `Nonempty (DerivationTree .Base [] phi)`, and we have `DerivationTree fc [] phi`, we need `Nonempty.intro` on the input. But we cannot downcast `fc` to `.Base`.

**Resolution**: The generic theorems work over typeclasses, not over specific derivation trees. `Theorems.Combinators.imp_trans` takes `InferenceSystem.DerivableIn S (phi.imp psi)` -- which is `Nonempty (S => phi.imp psi)`. For `S = HilbertTM`, this is `Nonempty (DerivationTree .Base [] ...)`. We need `⟨DerivationTree .Base [] ...⟩` but we have `DerivationTree fc [] ...`.

The correct approach (already validated in Perpetuity/Helpers.lean line 61-62):
```lean
def imp_trans {phi psi chi : Bimodal.Formula Atom}
    (h1 : base phi.imp psi) (h2 : base psi.imp chi) : base phi.imp chi :=
  unwrap (Theorems.Combinators.imp_trans (wrap h1) (wrap h2))
```
This works because Helpers.lean uses `Base`-only notation `⊢ phi`. The Combinators.lean versions are `fc`-polymorphic.

**Final correct pattern for fc-polymorphic bridge wrappers**:
For theorems with no derivation inputs (e.g., `identity`):
```lean
noncomputable def identity {fc : FrameClass} (A : Formula Atom) :
    DerivationTree fc [] (A.imp A) :=
  DerivationTree.lift (FrameClass.base_le fc)
    (unwrap (@Theorems.Combinators.identity _ _ _ Bimodal.HilbertTM _ _ A))
```

For theorems with derivation inputs (e.g., `imp_trans`):
```lean
noncomputable def imp_trans {fc : FrameClass} {A B C : Formula Atom}
    (h1 : DerivationTree fc [] (A.imp B))
    (h2 : DerivationTree fc [] (B.imp C)) : DerivationTree fc [] (A.imp C) :=
  DerivationTree.lift (FrameClass.base_le fc)
    (unwrap (Theorems.Combinators.imp_trans ⟨h1.lift (le_refl fc)⟩ ⟨h2.lift (le_refl fc)⟩))
```
Wait -- `h1.lift (le_refl fc)` produces `DerivationTree fc [] ...`, not `.Base`. We need `.Base`.

Actually, the correct insight is: for theorems with inputs, we do NOT need the inputs at `.Base` level. We only need `Nonempty` at the abstract level. Since `InferenceSystem.DerivableIn HilbertTM (A.imp B) = Nonempty (DerivationTree .Base [] (A.imp B))`, we need a `DerivationTree .Base [] (A.imp B)`. But we only have `DerivationTree fc [] (A.imp B)`.

However, any theorem provable at `fc` is provable at `.Base` (since `.Base` is the most inclusive frame class: `Base <= fc` for all `fc`). Actually wait -- `FrameClass.base_le fc` says `Base <= fc`, meaning `.Base` has *fewer* axioms, not more. So a derivation at `fc` uses axioms available at `fc`, which may not be available at `.Base`.

**But**: All 32 redundant theorems only use propositional axioms (imp_k, imp_s, efq, etc.) which are in `.Base`. The Foundations generic versions prove them using only typeclasses that `HilbertTM` satisfies. So the generic theorem already produces a `.Base`-level derivation. We do NOT need the inputs at all -- the generic theorem constructs the derivation from scratch.

For `identity`: no inputs, just produce the result generically and lift.
For `imp_trans`: takes two derivation inputs, but the generic version ALSO takes derivation inputs (as `InferenceSystem.DerivableIn`). We need to convert our concrete inputs to abstract ones. Since `DerivationTree fc [] (A.imp B)` and we need `Nonempty (DerivationTree .Base [] (A.imp B))`, we cannot directly convert. BUT -- `imp_trans` itself is provable without any inputs from the user; it produces `⊢ (A → B) → (B → C) → (A → C)`. The *input-taking* form of `imp_trans` is a convenience wrapper.

Looking more carefully at the Foundations `imp_trans`:
```
def imp_trans : InferenceSystem.DerivableIn S (phi.imp psi) → 
                InferenceSystem.DerivableIn S (psi.imp chi) → 
                InferenceSystem.DerivableIn S (phi.imp chi)
```
It takes inputs. So we need to wrap our concrete inputs. The issue is converting `DerivationTree fc [] X` to `InferenceSystem.DerivableIn HilbertTM X`.

Since `InferenceSystem.DerivableIn HilbertTM X = Nonempty (DerivationTree .Base [] X)`:
- From `DerivationTree fc [] X`, we cannot directly get `DerivationTree .Base [] X`
- But we CAN if the derivation only uses `.Base`-level axioms

This is a real technical concern. The implementation agent should handle it by defining `wrap` to work at `fc` level, constructing `Nonempty` directly: `⟨h1⟩` gives `Nonempty (DerivationTree fc [] X)`, but we need `Nonempty (DerivationTree .Base [] X)`.

**ACTUAL RESOLUTION**: The agent should follow the Perpetuity/Helpers.lean approach exactly. That file defines `wrap`/`unwrap` at `.Base` level only, and all its bridge theorems also work at `.Base` level only. The Combinators.lean theorems are `fc`-polymorphic. The simplest correct approach:

For theorems WITHOUT inputs: `unwrap (generic_theorem @args) |> .lift (base_le fc)`
For theorems WITH inputs: the implementation agent must determine the correct wrapping. The safest approach is:
1. Re-derive input-taking theorems as: first derive the curried form generically (e.g., `⊢ (A→B) → (B→C) → (A→C)`), then use modus ponens at `fc` level with the concrete inputs.
2. Or: since the concrete inputs `h1 : DerivationTree fc [] (A.imp B)` and `h2 : DerivationTree fc [] (B.imp C)` are available, and we have the generic curried theorem at `.Base`, lift it to `fc` and apply modus ponens.

Pattern:
```lean
noncomputable def imp_trans {fc : FrameClass} {A B C : Formula Atom}
    (h1 : DerivationTree fc [] (A.imp B))
    (h2 : DerivationTree fc [] (B.imp C)) : DerivationTree fc [] (A.imp C) :=
  let curried := DerivationTree.lift (FrameClass.base_le fc)
    (unwrap (@Theorems.Combinators.imp_trans_curried ...))  -- if curried form exists
  DerivationTree.modus_ponens [] _ _ (DerivationTree.modus_ponens [] _ _ curried h1) h2
```

OR more simply, if the agent can confirm that `Nonempty.intro` coercion works:
```lean
noncomputable def imp_trans {fc : FrameClass} {A B C : Formula Atom}
    (h1 : DerivationTree fc [] (A.imp B))
    (h2 : DerivationTree fc [] (B.imp C)) : DerivationTree fc [] (A.imp C) :=
  DerivationTree.lift (FrameClass.base_le fc)
    (unwrap (Theorems.Combinators.imp_trans ⟨h1.lift (le_refl _)⟩ ⟨h2.lift (le_refl _)⟩))
```
Wait -- `le_refl` on `fc` gives `fc <= fc`, so `h1.lift (le_refl fc) : DerivationTree fc [] ...` -- that does nothing. We need `h1` at `.Base`, but `Base <= fc` means we can lift FROM `.Base` TO `fc`, not the other way.

**FINAL ANSWER**: For theorems with derivation-tree inputs, the bridge cannot directly reuse those inputs. The correct approach is the **curried form + modus ponens** pattern:

```lean
noncomputable def imp_trans {fc : FrameClass} {A B C : Formula Atom}
    (h1 : DerivationTree fc [] (A.imp B))
    (h2 : DerivationTree fc [] (B.imp C)) : DerivationTree fc [] (A.imp C) :=
  -- Get the curried form: ⊢ (A→B) → (B→C) → (A→C) at Base, lift to fc
  have b_comb : DerivationTree fc [] ((A.imp B).imp ((B.imp C).imp (A.imp C))) :=
    DerivationTree.lift (FrameClass.base_le fc)
      (unwrap (@Theorems.Combinators.b_combinator _ _ _ Bimodal.HilbertTM _ _ (A := A) (B := B) (C := C)))
  DerivationTree.modus_ponens [] _ _
    (DerivationTree.modus_ponens [] _ _ b_comb h1) h2
```

The implementation agent should determine the exact approach for each theorem. The key insight is that **no-input theorems** use the simple `unwrap + lift` pattern, while **input-taking theorems** use the curried generic form + modus ponens at `fc` level.

---

### Phase 3: Cleanup and Final Verification [NOT STARTED]

**Goal**: Run full build verification, clean up any remaining issues, and confirm no downstream breakage.

**Tasks**:
- [ ] Run full `lake build` to verify zero errors across the entire project
- [ ] Verify no `sorry` was introduced: `grep -rn "sorry" Cslib/Logics/Bimodal/Theorems/ Cslib/Foundations/Logic/Theorems/Temporal/`
- [ ] Verify the old file locations are gone: confirm `Cslib/Logics/Temporal/Theorems/TemporalDerived.lean` and `Cslib/Logics/Temporal/Theorems/FrameConditions.lean` no longer exist
- [ ] Run `lake exe mk_all` to ensure `Cslib.lean` is up to date with all module paths
- [ ] Verify downstream Metalogic files still build correctly (spot-check a few key consumers):
  - `lake build Cslib.Logics.Bimodal.Metalogic.Algebraic.LindenbaumQuotient`
  - `lake build Cslib.Logics.Bimodal.Metalogic.BXCanonical.Frame`
  - `lake build Cslib.Logics.Bimodal.Theorems.Perpetuity.Principles`
- [ ] Confirm `Cslib/Logics/Bimodal/Theorems/TemporalDerived.lean` (the Bimodal-specific temporal derived theorems file) still builds correctly -- it imports from `Combinators` and `Propositional.Connectives` which were refactored

**Timing**: 1 hour

**Depends on**: 2

**Files to modify**:
- No files modified in this phase (verification only)
- Possible minor fixups if build reveals issues

**Verification**:
- `lake build` passes with zero errors
- Zero `sorry` occurrences in modified files
- All downstream consumers build successfully
- Old file paths no longer exist in the repository

## Testing & Validation

- [ ] `lake build` passes with zero errors after Phase 1
- [ ] `lake build` passes with zero errors after Phase 2
- [ ] Full `lake build` passes with zero errors after Phase 3
- [ ] No `sorry` introduced anywhere
- [ ] `grep -r "Logics.Temporal.Theorems.TemporalDerived" Cslib/` returns empty (old paths removed)
- [ ] `grep -r "Logics.Temporal.Theorems.FrameConditions" Cslib/` returns empty (old paths removed)
- [ ] All 8 concrete-only theorems remain with their original proof bodies
- [ ] All 32 replaced theorems have identical type signatures to originals

## Artifacts & Outputs

- `specs/057_improve_theorem_organization/plans/01_theorem-organization-plan.md` (this file)
- `Cslib/Foundations/Logic/Theorems/Temporal/TemporalDerived.lean` (moved from Logics/Temporal/)
- `Cslib/Foundations/Logic/Theorems/Temporal/FrameConditions.lean` (moved from Logics/Temporal/)
- Modified: `Cslib/Logics/Bimodal/Theorems/Combinators.lean` (11 theorems bridged)
- Modified: `Cslib/Logics/Bimodal/Theorems/Propositional/Core.lean` (9 theorems bridged)
- Modified: `Cslib/Logics/Bimodal/Theorems/Propositional/Connectives.lean` (12 theorems bridged)
- Modified: barrel imports in `Theorems.lean` files

## Rollback/Contingency

All changes are file moves and edits to existing files. Rollback via `git checkout` on any affected files. The original theorem proofs can be restored from git history if any bridge wrapper causes issues. Since each phase ends with a `lake build` check, problems are caught early and the rollback scope is limited to the current phase.
