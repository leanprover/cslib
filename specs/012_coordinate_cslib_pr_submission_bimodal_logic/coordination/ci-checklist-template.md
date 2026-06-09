# CI Validation Checklist — Per-PR Template

**Usage**: Copy this file to `coordination/ci-checks/pr-{TASK}-{name}.md` for each PR before submission.  
**Run all checks from the cslib repo root** (not the BimodalLogic repo).

---

## PR Identification

- **Task number**: _e.g., Task 2_
- **PR title**: _e.g., feat(Logics/Bimodal): add Syntax module_
- **Branch name**: _e.g., bimodal/syntax_
- **Files changed**: _list files_
- **Approximate line count**: ___

---

## Pre-Submission CI Checklist

Run each command and record the result. All must pass before submitting the PR.

### 1. Build Check

```bash
cd ~/Projects/cslib
lake build
```

- [ ] **PASS** — Zero errors, zero warnings (or only expected warnings)
- [ ] FAIL — Record error: ___

### 2. Test Suite

```bash
lake test
```

- [ ] **PASS** — CslibTests suite passes
- [ ] FAIL — Record error: ___

### 3. Init Imports Check

```bash
lake exe checkInitImports
```

- [ ] **PASS** — All modified/added files import `Cslib.Init` as first import
- [ ] FAIL — Record which files are missing the import: ___

### 4. Environment Linters

```bash
lake lint
```

- [ ] **PASS** — No linter errors
- [ ] FAIL — Record error: ___

### 5. Text Style Linters

```bash
lake exe lint-style
```

- [ ] **PASS** — No style violations
- [ ] If failures: `lake exe lint-style --fix` to auto-fix, then re-run to confirm
- [ ] FAIL (unfixable) — Record: ___

### 6. Import Shake

```bash
lake shake --add-public --keep-implied --keep-prefix
```

- [ ] **PASS** — No unused imports suggested, or all suggestions applied
- [ ] If suggestions: apply them, add `-- shake: keep` comments for tactic-required imports, re-run to confirm
- [ ] FAIL — Record: ___

### 7. Sorry Check

```bash
grep -rn "sorry" Cslib/Logics/Bimodal/     # adjust path per PR
```

- [ ] **PASS** — Zero sorry occurrences in submitted files
- [ ] EXCEPTION — PR 8 (Completeness): sorry present in chronicle construction (pre-disclosed in PR description)
- [ ] FAIL (unexpected sorry) — Record location: ___

### 8. Copyright Header Check

For every new Lean file in the PR, verify it begins with:

```lean
/-
Copyright (c) 2026 Benjamin Brastmckie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brastmckie
-/
```

- [ ] **PASS** — All new files have correct Apache 2.0 header
- [ ] FAIL — Files missing header: ___

---

## Per-File Checklist

For each new Lean file added in this PR:

| File path | Copyright header | `import Cslib.Init` first | Namespace correct | `lake shake` clean | `lake lint` clean |
|-----------|-----------------|--------------------------|-------------------|--------------------|-------------------|
| _example/file.lean_ | [ ] | [ ] | [ ] | [ ] | [ ] |

**Confirmed namespace**: _Fill in after Zulip confirmation — `Cslib.Logic.*` or `Cslib.Logics.*`_

---

## PR Description Pre-Check

Before submitting, verify the PR description includes:

- [ ] Clear title with conventional commit prefix (`feat:`, `fix:`, etc.) and area in parentheses
- [ ] Scope summary: what modules are added, what they prove/define
- [ ] Dependency note: which PRs this depends on (if any)
- [ ] AI usage disclosure (see template below)
- [ ] For PR 8 only: sorry disclosure with planned elimination timeline

### AI Disclosure Section (include verbatim in every PR description)

```markdown
## AI Assistance Disclosure

Portions of the source code in this PR were developed with AI assistance (Claude, by Anthropic).
The AI was used for: initial formalization drafts, proof search, and code structuring.
All proofs were reviewed and verified by the author. Per the Mathlib AI policy, this is disclosed
to help reviewers calibrate their review depth.
```

---

## Final Submission Checklist

- [ ] All 8 CI checks above pass (or exception documented for PR 8)
- [ ] PR description complete with AI disclosure
- [ ] Branch is up to date with cslib main
- [ ] All dependency PRs are merged to cslib main (check coordination-log.md)
- [ ] PR submitted to `github.com/leanprover/cslib`
- [ ] PR URL recorded in `coordination/coordination-log.md`

---

## Post-Submission Tracking

After submitting:

- **Submitted date**: ___
- **PR URL**: ___
- **Initial reviewer assigned**: ___
- **48-hour follow-up due**: _(submitted date + 48h)_
- **1-week Zulip ping due if no activity**: _(submitted date + 7d)_
