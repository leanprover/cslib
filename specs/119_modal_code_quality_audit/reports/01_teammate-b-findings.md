# Teammate B Findings: Cross-Logic Consistency and Conventions

**Task 119 — Modal Code Quality Audit**
**Focus: Consistency within Modal/ and between Temporal/, Bimodal/**

---

## Key Findings

### 1. Aggregator File Structure: Modal vs Temporal

**Finding**: The `Modal/Metalogic.lean` aggregator diverges significantly from
`Temporal/Metalogic.lean` in three ways:

**a) Modal aggregator lacks a module-level docstring**

`Modal/Metalogic.lean` has the `/-! # Modal Metalogic Module ... -/` docstring *after*
the `@[expose] public section` line (lines 44-51), while `Temporal/Metalogic.lean` has
*no* docstring at all. By contrast, `Temporal/ProofSystem.lean` places the docstring
*before* `@[expose] public section` (lines 13-21, then line 22), which is the correct
convention seen throughout the codebase.

In `Modal/Metalogic.lean` the layout is:
```
module
public import ...   -- imports (lines 9-42)
/-! # Modal Metalogic Module ... -/  -- docstring AFTER imports
@[expose] public section             -- section
```

In `Temporal/ProofSystem.lean` the layout is:
```
module
public import ...   -- imports (lines 8-11)
/-! # Temporal Proof System ... -/  -- docstring BEFORE @[expose]
@[expose] public section
```

**Recommendation**: Move the `/-! ... -/` block in `Modal/Metalogic.lean` to precede
`@[expose] public section`, matching the Temporal/ProofSystem.lean convention.

**b) Modal aggregator missing docstring in Temporal/Metalogic.lean comparison**

`Temporal/Metalogic.lean` has *no* module-level docstring at all — neither before nor
after `@[expose]`. This is an existing inconsistency in the Temporal directory that
should be treated as a separate issue, not a model to emulate.

**c) Modal/Metalogic.lean ends with blank line after `@[expose] public section`**

The file ends at line 53 with only the `@[expose] public section` declaration and a blank
line, no `end` or closing content. Compare to `Temporal/ProofSystem.lean` which also ends
this way (line 23 is the last line after `@[expose] public section`). This is consistent.

---

### 2. Instances File: Modal Uses One File vs Temporal Uses One File

**Finding**: Both logics consolidate instance registrations in a single
`ProofSystem/Instances.lean` file. Modal's `Instances.lean` is vastly larger (1532 lines
vs Temporal's 215 lines) due to the 15+ distinct axiom systems (K, T, D, S4, S5, KB,
K4, K5, K45, TB, KB5, D4, D5, D45, DB), each requiring 8-10 instance declarations.

**Structural match**: Both files follow the same pattern:
- `/-! ### System X Instances -/` subsection headers
- `instance : InferenceSystem Tag Formula where`
- Individual instances for each typeclass

**Discrepancy**: Temporal/Instances.lean opens with `-- Do not open Cslib.Logic.Temporal`
guard comment (line 31) to avoid scoped notation conflicts. Modal/Instances.lean has no
analogous guard. This is probably fine for Modal since it doesn't use scoped temporal
notation, but the comment documents an important convention.

---

### 3. Soundness File Structure: Modal vs Temporal (Consistent Pattern)

**Finding**: The Modal soundness files (`KSoundness.lean`, `TSoundness.lean`,
`S4Soundness.lean`, etc.) follow a *highly consistent* internal pattern across all 15
systems:

1. Copyright header
2. `module`
3. Imports (always `Soundness` + `Instances`)
4. `/-! # Soundness Theorem for Modal Logic X ... -/` docstring with:
   - Description of frame class
   - `## Main Results` list (`x_axiom_sound`, `x_soundness`, `x_soundness_derivable`)
   - `## References` (BRV reference + Soundness.lean)
5. `@[expose] public section`
6. `namespace Cslib.Logic.Modal`
7. `open Cslib.Logic`
8. `variable {Atom : Type*}`
9. `/-! ## X Axiom Soundness (BRV Definition 4.9 for X) -/` subsection
10. Single `theorem x_axiom_sound` with frame conditions as hypotheses
11. `/-! ## X Soundness Theorems -/` subsection
12. `theorem x_soundness` (context version)
13. `theorem x_soundness_derivable` (empty context version)
14. `end Cslib.Logic.Modal`

This is **excellent and consistent** across all 15 soundness files. The pattern is
stable and uniform.

**Comparison with Temporal/Metalogic/Soundness.lean**: The Temporal soundness file
has a somewhat different structure due to domain complexity (26 axioms, duality theorem,
two namespaces), but the fundamental elements match: docstring before `@[expose]`,
`namespace`, `open`, `variable`, subsection headers, main theorems.

One notable structural difference: Temporal/Soundness uses `set_option maxHeartbeats`
(lines 31-32) before `@[expose]`. No Modal soundness file uses `set_option`. This
reflects the higher computational complexity of temporal proofs and is expected, not
an inconsistency.

---

### 4. Completeness File Structure: Two Tiers (Expected but Worth Documenting)

**Finding**: Modal completeness files fall into two structural tiers:

**Tier 1 — Base files** (`Completeness.lean`, `KCompleteness.lean`, `DCompleteness.lean`):
These contain the canonical model definition, canonical frame property theorems
(`canonical_refl`, `canonical_trans`, `canonical_symm`, `canonical_eucl`,
`canonical_eucl_from_5`, `canonical_serial`, truth lemmas, and the S5/K/D completeness
theorems themselves).

**Tier 2 — Derived system files** (`S4Completeness.lean`, `K45Completeness.lean`,
`TCompleteness.lean`, etc.): These are thin wrappers that import the base files and
provide one completeness theorem, calling the machinery from Tier 1. They follow a
consistent structure:
1. Imports: `Completeness.lean` + optionally `KCompleteness.lean` + `Instances.lean`
2. Docstring explaining which truth lemma is used and why
3. `@[expose] public section`
4. `universe u; variable {Atom : Type u}` (note `universe u` vs `variable {Atom : Type*}` in soundness)
5. Commented step-by-step proof walkthrough (`-- Step 1:`, `-- Step 2:`, etc.)
6. Single completeness theorem

**Universe variable inconsistency**: Soundness files use `variable {Atom : Type*}` while
completeness files use `universe u; variable {Atom : Type u}`. This is intentional — the
completeness theorems quantify over `Type u` worlds for the validity hypothesis, requiring
an explicit universe. The soundness theorems use `{World : Type*}` locally instead. This
is correct but could be documented in a design note.

**Missing systems from `Modal/Metalogic.lean` aggregator**: The aggregator lists all 15
soundness/completeness pairs. Inspection confirms they are all present on disk.

---

### 5. Import Order: Consistent Within Modal, Matches Temporal

**Finding**: Modal files follow a consistent import order:
1. Core system imports (DerivationTree, Soundness, Completeness, MCS)
2. Instance registration import (ProofSystem.Instances)
3. No Mathlib imports in metalogic files

Temporal metalogic files have one exception: `Temporal/Metalogic/Soundness.lean` imports
`Mathlib.Order.Max` (line 12), needed for `NoMaxOrder`/`NoMinOrder` typeclasses. This is
domain-appropriate and not a convention violation.

---

### 6. Docstring Naming Convention: `x_axiom_sound` vs `axiom_sound`

**Finding**: The naming convention for axiom soundness theorems differs across tiers:

- `Soundness.lean` (S5/parameterized): `theorem axiom_sound` (no prefix)
- All other soundness files: `theorem k_axiom_sound`, `theorem t_axiom_sound`, etc.

This is correct by design — `axiom_sound` in `Soundness.lean` is the S5-specific
axiom soundness callback, and the parameterized `soundness` theorem takes a generic
callback. Each system-specific file provides its own named `x_axiom_sound`.

However, the Soundness.lean docstring says "Each of the 8 S5 axiom schemata is valid
over S5 frames" in the `## Main Results` section header for `axiom_sound`, even though
`axiom_sound` is the concrete S5 proof while `soundness` is the parameterized one. This
is potentially confusing — the parameterized soundness is the more important result, but
the docstring front-loads the S5-specific theorem.

---

### 7. Comparison with Bimodal/ (Spot-check)

**Finding**: The Bimodal metalogic has a much richer structure
(`Completeness/`, `Soundness/`, `Core/`, `BXCanonical/`, `Bundle/`, `Algebraic/`,
`Decidability/`, `Separation/`, `ConservativeExtension/`) reflecting its greater
complexity. Direct comparisons to Modal at the file-by-file level are not meaningful
because Bimodal is a different level of formalization.

The conventions that *do* apply across both:
- Copyright headers: identical format (consistent)
- `@[expose] public section` at module top: consistent
- `namespace Cslib.Logic.Bimodal` / `namespace Cslib.Logic.Modal`: consistent
- `open Cslib.Logic`: consistent (both use this)
- `/-! ## Section Name -/` subsection markers: consistent

---

### 8. One Structural Anomaly: `Soundness.lean` Contains S5-Specific Code

**Finding**: `Modal/Metalogic/Soundness.lean` is named as if it is the *parameterized*
soundness file, but it contains:
1. The parameterized `soundness` theorem (correct)
2. `axiom_sound` for S5 specifically (correct companion)
3. **`s5_soundness` and `s5_soundness_derivable` wrappers** (lines 122-143)

The docstring `## Main Results` section lists `axiom_sound`, `soundness`, `s5_soundness`
as if they are equally important. But this creates a subtle design issue: `s5_soundness`
lives in `Soundness.lean` while `k_soundness` lives in `KSoundness.lean`. This means S5
is treated asymmetrically — its soundness wrapper is colocated with the parameterized
machinery rather than in a dedicated `S5Soundness.lean` file.

This is a minor inconsistency worth noting: the modal cube includes K, T, D, S4, K4, K5,
K45, TB, KB5, D4, D5, D45, DB, B — all with dedicated `XSoundness.lean` files — but S5
does not have its own `S5Soundness.lean`. S5 soundness is instead in `Soundness.lean`.

---

## Recommended Approach

1. **Fix docstring placement in `Modal/Metalogic.lean`** (high priority, one-line move):
   Move the `/-! # Modal Metalogic Module ... -/` block from after the imports to
   between the last import and `@[expose] public section`, matching the convention in
   `Temporal/ProofSystem.lean`.

2. **Add docstring to `Temporal/Metalogic.lean`** (separate task, cross-logic consistency):
   The Temporal aggregator currently has no module-level docstring, unlike the Modal
   aggregator and Temporal/ProofSystem.lean. A brief docstring listing the Chronicle
   construction components would improve consistency.

3. **Consider creating `S5Soundness.lean`** (low priority, cosmetic):
   To make all 15+ modal systems fully parallel, the S5-specific wrappers
   (`s5_soundness`, `s5_soundness_derivable`) could be moved to a dedicated
   `S5Soundness.lean`. This would make `Soundness.lean` purely parameterized machinery
   and make the system directory symmetric.

4. **Add design note on universe variable convention** (documentation):
   The soundness vs completeness files use different universe variable patterns
   (`Type*` vs `universe u; Type u`). This is correct but warrants a brief comment in
   the relevant files or the project documentation.

---

## Evidence/Examples

**Docstring placement difference** — correct (Temporal/ProofSystem.lean, lines 13-22):
```lean
module
public import Cslib.Logics.Temporal.ProofSystem.Axioms
...

/-! # Temporal Proof System
...
-/

@[expose] public section
```

**Docstring placement anomaly** (Modal/Metalogic.lean, lines 7-52):
```lean
module

public import Cslib.Logics.Modal.Metalogic.DerivationTree
...
public import Cslib.Logics.Modal.ProofSystem.Instances  -- line 42

/-! # Modal Metalogic Module  <-- docstring AFTER all imports
...                           <-- should be before @[expose]
-/

@[expose] public section  <-- line 52
```

**Consistent soundness pattern** (all 15 systems follow this):
- `KSoundness.lean`: `theorem k_axiom_sound` + `k_soundness` + `k_soundness_derivable`
- `TSoundness.lean`: `theorem t_axiom_sound` + `t_soundness` + `t_soundness_derivable`
- `S4Soundness.lean`: `theorem s4_axiom_sound` + `s4_soundness` + `s4_soundness_derivable`
- All at `@[expose] public section`, `namespace Cslib.Logic.Modal`, `open Cslib.Logic`

**Universe variable asymmetry** (by design, not a bug):
```lean
-- Soundness files use:
variable {Atom : Type*}

-- Completeness files use:
universe u
variable {Atom : Type u}
```

**S5 asymmetry**: All 14 non-S5 systems have `XSoundness.lean`; S5 soundness lives in
`Soundness.lean` alongside the parameterized machinery.

---

## Confidence Level

- **Docstring placement finding**: High confidence. The `/-! ... -/` in `Modal/Metalogic.lean`
  appears after the imports list and just before `@[expose]`, which does not match the pattern
  in `Temporal/ProofSystem.lean` where the docstring precedes `@[expose]`. (The section begins
  at line 52, docstring at line 44.)

- **Internal soundness consistency**: High confidence. All 15 soundness files were
  inspected (K, T, D, S4, K4, K5, K45, TB, KB5, D4, D5, D45, DB, B) and follow
  identical structural conventions.

- **S5 asymmetry finding**: High confidence. No `S5Soundness.lean` file exists on disk;
  the directory listing confirms this.

- **Cross-logic namespace/open consistency**: High confidence. All Modal, Temporal, and
  Bimodal files use `namespace Cslib.Logic.{Domain}` and `open Cslib.Logic`.

- **Universe variable convention**: Medium confidence that the asymmetry is intentional
  (completeness requires quantifying over worlds at universe `u`), but the absence of a
  comment explaining this may lead to confusion.
