# Teammate A Findings: Implementation Quality and Proof Patterns

**Task**: 119 — Modal code quality audit
**Angle**: Implementation quality, proof patterns, duplication, linter warnings
**Scope**: `Cslib/Logics/Modal/Metalogic/` (all files), `Cslib/Logics/Modal/ProofSystem/Instances.lean`, `Cslib/Foundations/Logic/ProofSystem.lean`

---

## Key Findings

### 1. Severe Copy-Paste Duplication in `*Completeness.lean` (High Severity)

The `h_cons` block — proving that `{¬φ}` is consistent for a given axiom set — is copy-pasted verbatim across **every** completeness file:

- `KCompleteness.lean` (lines 75–107)
- `BCompleteness.lean` (lines 65–98)
- `K4Completeness.lean` (lines 74–107)
- `K5Completeness.lean` (lines 65–98)
- `K45Completeness.lean` (same pattern)
- `TBCompleteness.lean` (same pattern)
- `D4Completeness.lean` (lines 71–104)
- `D5Completeness.lean` (same pattern)
- `D45Completeness.lean` (same pattern)
- `DBCompleteness.lean` (same pattern)

The block is always the same 30-line derivation: `d_weak`, `d_dne`, `efq_ax`, `ik`, `step_k`, `is_ax`, `step_s`, `step3`, `peirce_ax`, `d_phi`, `exact h_not_deriv ⟨d_phi⟩`. This proves that if `φ` is not derivable then `{¬φ}` is consistent, using only the classical propositional axioms (K, S, EFQ, Peirce). The block is parameterized only by the concrete axiom type (e.g., `@K4Axiom Atom`).

This is the single largest quality issue in the codebase. Ten files each carry a 30-line proof that is semantically identical.

**Recommended fix**: Extract a shared lemma in `KCompleteness.lean` (or a new `Completeness/Boilerplate.lean`):

```lean
/-- If `phi` is not derivable, then `{neg phi}` is consistent.
Requires only the classical propositional axioms K, S, EFQ, Peirce. -/
theorem neg_consistent_of_not_derivable
    {Axioms : Proposition Atom → Prop}
    (h_implyK : ...)
    (h_implyS : ...)
    (h_efq : ...)
    (h_peirce : ...)
    {φ : Proposition Atom}
    (h_not_deriv : ¬Derivable Axioms φ) :
    Modal.SetConsistent Axioms {Proposition.neg φ} := ...
```

Every completeness file can then replace its `h_cons` block with one line.

### 2. Copy-Paste in `*Soundness.lean`: The 5-Case Propositional Block (Medium Severity)

Every soundness file's `*_axiom_sound` theorem contains the same 5 sub-proofs for the shared propositional/K axioms:

```lean
| implyK φ ψ =>  intro hφ _; exact hφ
| implyS φ ψ χ => intro h₁ h₂ h₃; exact h₁ h₃ (h₂ h₃)
| efq φ =>        intro h; exact absurd h id
| peirce φ ψ =>   intro h; by_contra h_not; exact h_not (h (fun hφ => absurd hφ h_not))
| modalK φ ψ =>   intro h_box_imp h_box_phi w' hr; exact h_box_imp w' hr (h_box_phi w' hr)
```

This appears in **all 13 soundness files** (K, T, D, S4, S5, B, K4, K5, K45, KB5, TB, D4, D5, D45, DB). Since each axiom inductive has the K-subset as its first N constructors, every file re-proves these identical cases.

**Evidence**: Compare `KSoundness.lean` lines 45–61 with `K4Soundness.lean` lines 54–69, `BSoundness.lean` lines 46–68, `K45Soundness.lean` lines 57–73, `D45Soundness.lean` lines 53–75. All contain this identical 5-case block.

**Recommended fix**: Factor these into a shared helper lemma
`k_axiom_sound_shared` that proves validity for any axiom set containing the K-sub-predicates. The per-logic files then only need to handle their unique axiom cases (T, 4, 5, B, D) and delegate the shared cases.

This is a style improvement rather than a correctness issue; the current approach is not wrong, just verbose.

### 3. Linter Warnings: All Confirmed Fixable (Medium Severity)

`lake build Cslib.Logics.Modal.Metalogic 2>&1 | grep -i warning` yields 51 warnings. Grouped by type:

**a. `push_neg` deprecation (1 warning):**
- `Basic.lean:115:4` — `push_neg` deprecated, prefer `push Not`

**b. `show` tactic used for non-readability (10 warnings), all in `Basic.lean`:**
- Lines 122, 132, 227, 234, 241, 265, 279, 303, 333, 361
- The Lean 4 convention says `show` should only indicate intermediate goal states. These uses are effectively rewriting the goal to unfold definitions rather than using `unfold` or `simp only`.

**c. `simp_wf` does nothing (2 warnings), in `DeductionTheorem.lean`:**
- Lines 116 and 183 — `simp_wf` tactic does nothing (produces no change). These should be removed.

**d. Flexible `simp` warnings (12 warnings):**
- `DeductionTheorem.lean`: 2 flexible simp calls (`simp [List.mem_cons]`, `simp [this]`, `simp at h ⊢`)
- `MCS.lean`: 3 flexible simp calls
- `Completeness.lean`: 3 flexible simp calls
- `KCompleteness.lean`: 2 flexible simp calls
- `TCompleteness.lean`, `DCompleteness.lean`, `S4Completeness.lean`, `K4Completeness.lean`, `D45Completeness.lean`: 1 each
- Each recommends converting to `simp only [...]` or `suffices`

**e. Unused variable `ψ` (10 warnings):**
- `Soundness.lean:131`, `Soundness.lean:142`
- `KSoundness.lean:72`, `KSoundness.lean:80`
- `TSoundness.lean:78`, `TSoundness.lean:87`
- `DSoundness.lean:80`, `DSoundness.lean:88`
- `S4Soundness.lean:93`, `S4Soundness.lean:104`
- `K4Soundness.lean:85`, `K4Soundness.lean:95`
- `BSoundness.lean:80`

These occur in the wrapper theorems `k_soundness` and `k_soundness_derivable` (and their per-logic analogues). The `ψ` parameter is implicit in the lambda `fun ψ h_ax w => ...` but not referenced. It should be replaced with `_` (or `fun h_ax w => ...` using anonymous syntax).

**f. Duplicated namespace warning (2 warnings in MCS.lean):**
- Lines 47 and 52: `Modal.SetConsistent` and `Modal.SetMaximalConsistent` are being declared inside namespace `Cslib.Logic.Modal`, producing `Cslib.Logic.Modal.Modal.SetConsistent` instead of `Cslib.Logic.Modal.SetConsistent`. This is a genuine naming bug.

### 4. Inconsistent Naming of Soundness Wrappers (Low Severity)

`KSoundness.lean` uses `/-! ## K Soundness Theorems -/` as its section header.
`BSoundness.lean` uses `/-! ## B Soundness Wrappers -/`.
`K4Soundness.lean` uses `/-! ## K4 Soundness Theorems -/`.
`K5Soundness.lean` uses `/-! ## K5 Soundness Wrappers -/`.

The inconsistency between "Theorems" and "Wrappers" in the section headers is minor but inconsistent. The "Wrappers" name is accurate (these are thin wrappers delegating to the parameterized `soundness`), so consolidating on `/-! ## X Soundness Wrappers -/` is slightly preferable. This is a cosmetic issue.

### 5. `Instances.lean`: The Instance Block Repetition (Medium Severity)

Each of the 15 modal proof systems (K, T, D, S4, S5, KB, K4, K5, K45, TB, KB5, D4, D5, D45, DB) has the same 3-instance cluster repeated: `ModusPonens`, `Necessitation`, and for each axiom one `HasAxiom*` instance. The `ModusPonens` and `Necessitation` instances are structurally identical across all 15 systems — the only difference is the axiom tag type (e.g., `Modal.HilbertK4` vs `Modal.HilbertS4`) and the underlying axiom type (e.g., `@Modal.K4Axiom Atom` vs `@Modal.S4Axiom Atom`). The proof body is always:

```lean
mp := fun h1 h2 => by
  obtain ⟨d1⟩ := h1; obtain ⟨d2⟩ := h2
  exact ⟨Modal.DerivationTree.modus_ponens [] _ _ d1 d2⟩
```

This cannot easily be abstracted without Lean 4 instance generation macros, but it is worth documenting. As a fallback, a `macro` or `def` helper for these repetitive instance bodies could reduce boilerplate.

### 6. `Completeness.lean` Module Header: Stale Description (Low Severity)

The module header in `Completeness.lean` still says "S5 Modal Logic" in its title, but the file now also contains `canonical_symm` and `canonical_eucl_from_5` which are used by B, K5, K45, KB5, TB, and DB completeness. The header should be updated to reflect that the file is the parameterized completeness infrastructure for all 15 logics, not just S5.

Similarly, `Soundness.lean` still describes itself as "S5 Axiom Soundness" in its opening section but now serves as the parameterized soundness module for all logics. The section `/-! ## S5 Axiom Soundness -/` should become `/-! ## S5 Axiom Soundness (instantiated) -/` or similar.

### 7. Inconsistency in Frame Condition Style: `Relation.Serial` vs Lambda (Low Severity)

The D-series soundness files (D4, D5, D45, DB) use `Relation.Serial m.r` as the seriality condition:
```lean
(h_serial : Relation.Serial m.r)
```
Then dereference it as `h_serial.serial w` to get `∃ w', m.r w w'`.

This is correct and more idiomatic than an inline lambda, but the style deviates from the reflexivity/symmetry/transitivity/Euclidean conditions, which are all expressed as explicit lambdas:
```lean
(h_refl : ∀ w, m.r w w)
(h_symm : ∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁)
```

Having one frame condition use a Mathlib typeclass structure and the others use explicit quantifiers creates friction when reading across files. A consistent choice should be made; either use `Relation.Serial` everywhere (leveraging the Mathlib struct), or unfold it to `∀ w, ∃ w', m.r w w'` to match the other frame conditions. The current inconsistency appears intentional (the `Relation.Serial` was already used in earlier D soundness), but it should be at least documented as a deliberate choice.

---

## Recommended Approach

**Priority 1 (High impact, easy)**: Fix the unused `ψ` variable warnings in all soundness wrapper theorems — replace `fun ψ h_ax w => ...` with `fun _ h_ax w => ...` or `fun h_ax w => ...`. This removes 10+ warnings with a trivial one-character change per site.

**Priority 2 (High impact, medium effort)**: Extract `neg_consistent_of_not_derivable` to remove the 30-line copy-pasted `h_cons` block from the 10 completeness files that do not have T. This is the single biggest deduplication opportunity.

**Priority 3 (Medium impact, medium effort)**: Convert flexible `simp` calls to `simp only [...]` to address the 12 "flexible simp" warnings. Using `simp?` at each site will produce the recommended lemma list.

**Priority 4 (Low impact, easy)**: Fix the `Modal.Modal.SetConsistent` namespace collision in `MCS.lean` (two warnings), remove the dead `simp_wf` calls in `DeductionTheorem.lean`, and replace `push_neg` with `push Not` in `Basic.lean`.

**Priority 5 (Low impact, cosmetic)**: Update `Completeness.lean` and `Soundness.lean` module headers to reflect their actual scope across all 15 logics rather than just S5.

---

## Evidence / Examples

### Evidence for finding 1 (h_cons copy-paste)

`K4Completeness.lean` lines 74–107 and `K5Completeness.lean` lines 65–98 are character-for-character identical except for the axiom type annotation (`@K4Axiom` vs `@K5Axiom`). Same for `BCompleteness.lean` vs `KCompleteness.lean` in their `h_cons` blocks. The same 30-line block appears in at least 10 files.

### Evidence for finding 3e (unused `ψ` variable)

From `KSoundness.lean` lines 66–80:
```lean
theorem k_soundness ... :=
  soundness d m (fun ψ h_ax w => k_axiom_sound h_ax m w) w h_ctx
                     ^^ unused
```
The `ψ` is bound but only `h_ax` and `w` are used in the body `k_axiom_sound h_ax m w`. The fix is `fun _ h_ax w => ...`.

### Evidence for finding 3f (namespace collision)

From `MCS.lean`:
```
warning: The namespace 'Modal' is duplicated in the declaration 'Cslib.Logic.Modal.Modal.SetConsistent'
warning: The namespace 'Modal' is duplicated in the declaration 'Cslib.Logic.Modal.Modal.SetMaximalConsistent'
```
This means these are accessible as both `Modal.Modal.SetConsistent` and `Modal.SetConsistent`, which is confusing. The `abbrev` should be declared inside `namespace Cslib.Logic` (not `namespace Cslib.Logic.Modal`) or the `Modal.` prefix should be dropped from the `abbrev` name.

### Evidence for finding 7 (Relation.Serial inconsistency)

`D4Soundness.lean` line 47:
```lean
(h_serial : Relation.Serial m.r)
```
vs `TBSoundness.lean` line 54:
```lean
(h_refl : ∀ w, m.r w w)
(h_symm : ∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁)
```

---

## Confidence Level

- **Finding 1** (h_cons duplication): Certain — verified by direct comparison of K4Completeness, K5Completeness, BCompleteness, D4Completeness. All 10 non-T completeness files share the block.
- **Finding 2** (propositional case duplication in soundness): Certain — verified by reading all soundness files.
- **Finding 3** (linter warnings): Certain — reproduced from `lake build` output (51 warnings total).
- **Finding 4** (section header inconsistency): Certain — confirmed by reading all soundness files.
- **Finding 5** (Instances.lean repetition): Certain — confirmed from reading Instances.lean (1532 lines for 15 systems).
- **Finding 6** (stale module headers): Certain — `Completeness.lean` header references S5 only but `canonical_symm` and `canonical_eucl_from_5` serve B, K5, etc.
- **Finding 7** (Relation.Serial inconsistency): Certain — verified by comparing D4Soundness.lean vs TBSoundness.lean.
