# PR Description Template

**Usage**: Copy the "PR Description" section below into your GitHub PR description. Fill in the bracketed sections.

---

## PR Description

### [feat/fix/doc]([Area]): [Brief description]

#### Summary

[2-4 sentences describing what this PR adds. Include:
- What modules/files are added
- What they prove or define (theorem names, key definitions)
- Approximate scope (number of files, line count)
]

#### Scope

**Files added**:
```
Cslib/[Path/To/Module]/
  File1.lean     — [one-line description]
  File2.lean     — [one-line description]
  ...
```

**Key definitions**:
- `[DefinitionName]` — [brief description]
- `[TheoremName]` — [brief description]

#### Dependencies

This PR depends on:
- [PR title or "no dependencies"] ([PR URL or "merged" / "submitted"])

This PR is depended on by:
- [PR title] ([PR URL or "not yet submitted"])

#### Relationship to Existing Code

[Explain how this fits into the existing cslib structure. Reference existing modules this extends or imports from.]

---

#### AI Assistance Disclosure

Portions of the source code in this PR were developed with AI assistance (Claude, by Anthropic).
The AI was used for: initial formalization drafts, proof search, and code structuring.
All proofs were reviewed and verified by the author. Per the Mathlib AI policy, this is disclosed
to help reviewers calibrate their review depth.

---

#### CI Verification

Before submission, the following CI checks were run locally and passed:
- [x] `lake build` — zero errors
- [x] `lake test` — CslibTests pass
- [x] `lake exe checkInitImports` — all files import `Cslib.Init`
- [x] `lake lint` — no linter errors
- [x] `lake exe lint-style` — no style violations
- [x] `lake shake --add-public --keep-implied --keep-prefix` — imports minimized
- [x] Zero `sorry` in submitted files (see note if exception applies)
- [x] All files have Apache 2.0 copyright header

---

## Special Section: Sorry Disclosure (PR 8 Only)

Add this section to the PR 8 (Completeness) description INSTEAD of marking "Zero sorry" above:

> **Note on sorry**: This PR contains one `sorry` in the chronicle construction
> (`Cslib/Logics/Bimodal/Metalogic/Completeness/ChronicleConstruction.lean`, approximately line [N]).
> The sorry corresponds to a lemma in the completeness proof that has not yet been formally verified
> in Lean 4 (though the argument is standard in the literature). This is disclosed proactively.
>
> Plans for elimination:
> - [ ] Track as issue #[N] in cslib
> - [ ] Complete the formal proof in a follow-up PR once the construction is better understood
>
> If the sorry blocks merge, I can submit a version of the PR without the sorry-containing file
> and track the remaining lemma separately.

---

## Template Usage Notes

1. Replace all `[bracketed text]` with actual content
2. Adjust the "Files added" list to match actual PR contents
3. The AI disclosure section must appear verbatim in every PR
4. The CI checklist must reflect actual local CI results (all checked = passed)
5. For PRs that are part of a wave: be explicit about which dependency PRs are merged vs. pending
6. Keep the PR title to the conventional commit format: `type(area): description`
   - Valid types: `feat`, `fix`, `doc`, `style`, `refactor`, `test`, `chore`, `perf`
   - Area uses path notation: `Logics/Bimodal`, `Foundations/Logic`, etc.

---

## PR Title Reference

| Task | PR Title |
|------|----------|
| 20 | `feat(Foundations/Logic): add Hilbert theorem infrastructure (Combinators, Propositional, ContextualProofs, BigConj)` |
| 21 | `feat(Logics/Modal): add Modal proof system and theorems (DerivationTree, S4/S5, GenNec)` |
| 22 | `feat(Logics/Temporal): add Temporal proof system infrastructure and theorems` |
| 23 | `feat(Logics/Temporal): add Temporal semantics on linear orders` |
| 2 | `feat(Logics/Bimodal): add Syntax module (Context, BigConj, Subformulas)` |
| 3 | `feat(Logics/Bimodal): add Semantics module (TaskFrame, WorldHistory, Truth, Validity)` |
| 4 | `feat(Logics/Bimodal): add ProofSystem module (42-axiom Axiom, DerivationTree)` |
| 5 | `feat(Logics/Bimodal): add Theorems/Perpetuity module` |
| 6 | `feat(Logics/Bimodal): add FrameConditions and Soundness modules` |
| 7 | `feat(Logics/Bimodal): add Metalogic/Core module (DeductionTheorem, MCS)` |
| 8 | `feat(Logics/Bimodal): add Completeness theorem` |
| 9a | `feat(Logics/Bimodal): add Metalogic/Decidability (Core tableau, decision procedure)` |
| 9b | `feat(Logics/Bimodal): add Metalogic/Decidability (FMP, finite model property)` |
| 10 | `feat(Logics/Bimodal): add Metalogic/Separation module` |
| 11 | `feat(Logics/Bimodal): add Metalogic/ConservativeExtension module` |
