# PR Submission Workflow — Bimodal Temporal Logic Integration

**Scope**: 14 PRs to `github.com/leanprover/cslib`  
**Reference**: `coordination-log.md` for current status

---

## Phase Gate: Before Any PR Submission

You MUST complete these steps before submitting Task 2 (the first porting PR):

1. **Post Zulip proposal** (see `zulip-proposal-draft.md`)
2. **Obtain maintainer response** — wait for at least one response from @fmontesi, @kim-em, or @eric-wieser
3. **Confirm namespace** — get a clear answer to: `Cslib.Logic.*` vs `Cslib.Logics.*`
4. **Record decisions** in `coordination-log.md`

If maintainers raise architectural concerns, pause all porting work and address concerns first.

---

## Per-PR Submission Procedure

Follow this procedure for each of the 14 PRs:

### Step 1: Verify Prerequisites

- [ ] All dependency PRs are merged to cslib main (check `coordination-log.md`)
- [ ] The porting task (e.g., Task 2) is complete in this repo (`cslib` project)
- [ ] No open blocking issues for this PR

### Step 2: Prepare the Branch

```bash
# From cslib repo:
cd ~/Projects/cslib
git fetch origin
git checkout -b [branch-name] origin/main   # e.g., bimodal/syntax

# Copy ported files from the task directory or BimodalLogic repo
# Files should already be in their cslib paths
```

### Step 3: Run CI Validation

```bash
# From cslib repo root:
./specs/012_coordinate_cslib_pr_submission_bimodal_logic/coordination/validate-pr-ci.sh [path/to/new/files]
```

Alternatively, run checks manually (see `ci-checklist-template.md`).

All checks must pass before proceeding. For PR 8 only: the sorry in chronicle construction is allowed with pre-disclosure.

### Step 4: Write the PR Description

1. Open `coordination/pr-description-template.md`
2. Copy the template and fill in all bracketed sections
3. Verify the AI disclosure section is present verbatim
4. For PR 8: add the sorry disclosure section

### Step 5: Submit the PR

```bash
# Using gh CLI:
gh pr create \
  --repo leanprover/cslib \
  --title "feat(Logics/Bimodal): add Syntax module (Context, BigConj, Subformulas)" \
  --body "$(cat /path/to/pr-description.md)" \
  --base main
```

Or use the GitHub web interface.

### Step 6: Record in Coordination Log

Update `coordination/coordination-log.md`:
- Add PR URL to the tracking table
- Set status to "SUBMITTED"
- Record submission date

### Step 7: Monitor Review

- Check for reviewer comments daily
- Address any comments within **48 hours** of receiving them
- Push updates to the same branch (do not force-push unless absolutely necessary)
- If no activity after **7 days**: post a polite follow-up in the Zulip working group thread

---

## Wave-by-Wave Submission Guide

### Wave 1 — Start here after Zulip confirmation

**PR-Foundations (Task 20)**
- Dependencies: none (only Zulip pre-coordination)
- Branch: `foundations/logic-theorems`
- Target path: `Cslib/Foundations/Logic/Theorems/`
- Size: ~2,400 lines

Wait for this to be merged before Wave 2.

---

### Wave 2 — After Foundations merged

Submit these three in parallel (order among them doesn't matter, but all depend on Foundations):

**PR-Modal (Task 21)**
- Branch: `modal/proof-system`
- Target: `Cslib/Logics/Modal/ProofSystem/`, `Cslib/Logics/Modal/Theorems/`
- Size: ~1,600 lines

**PR-Temporal-Infra (Task 22)**
- Branch: `temporal/proof-system`
- Target: `Cslib/Logics/Temporal/ProofSystem/`, `Cslib/Logics/Temporal/Theorems/`
- Size: ~1,500 lines

**PR-Syntax (Task 2)** — may submit in parallel with 21 and 22 if namespace confirmed
- Branch: `bimodal/syntax`
- Target: `Cslib/Logics/Bimodal/Syntax/`
- Size: ~2,500 lines

Wait for all three Wave 2 PRs to merge before Wave 3.

---

### Wave 3 — After all Wave 2 PRs merged

**PR-TempSem (Task 23)** — depends on Task 22
- Branch: `temporal/semantics`
- Target: `Cslib/Logics/Temporal/Semantics/`
- Size: ~400-600 lines

**PR-Semantics (Task 3)** — depends on Task 2
- Branch: `bimodal/semantics`
- Target: `Cslib/Logics/Bimodal/Semantics/`
- Size: ~2,200 lines

**PR-ProofSystem (Task 4)** — depends on Tasks 2, 20, 22
- Branch: `bimodal/proof-system`
- Target: `Cslib/Logics/Bimodal/ProofSystem/`
- Size: ~2,000 lines

Wait for all three Wave 3 PRs to merge before Wave 4.

---

### Wave 4 — After all Wave 3 PRs merged

**PR-Perpetuity (Task 5)** — depends on Tasks 4, 21, 22
- Branch: `bimodal/theorems-perpetuity`
- Target: `Cslib/Logics/Bimodal/Theorems/`
- Size: ~800 lines

**PR-FrameConditions (Task 6)** — depends on Tasks 3, 4
- Branch: `bimodal/frame-conditions`
- Target: `Cslib/Logics/Bimodal/FrameConditions/`, `Cslib/Logics/Bimodal/Soundness/`
- Size: ~2,370 lines

**PR-ConservativeExt (Task 11)** — depends on Task 4 (independent of 5-10)
- Branch: `bimodal/conservative-extension`
- Target: `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/`
- Size: ~1,500 lines

---

### Wave 5 — After Wave 4 merged

**PR-MCS (Task 7)** — depends on Tasks 4, 5
- Branch: `bimodal/metalogic-core`
- Target: `Cslib/Logics/Bimodal/Metalogic/Core/`
- Size: ~2,500 lines

---

### Wave 6 — After Wave 5 merged

**PR-Completeness (Task 8)** — depends on Tasks 6, 7
- **Special handling**: Contains sorry in chronicle construction
- Branch: `bimodal/completeness`
- Target: `Cslib/Logics/Bimodal/Metalogic/Completeness/`
- Size: ~15,000+ lines — discuss with maintainers before submitting
- Include sorry disclosure section in PR description
- If maintainers request splitting: split into 8a (basic completeness) and 8b (chronicle/sorry)

**PR-Decidability (Task 9)** — depends on Tasks 4, 7
- **Special handling**: Large PR (~10k lines), may need splitting
- Branch: `bimodal/decidability` (or `bimodal/decidability-9a` and `bimodal/decidability-9b`)
- Target: `Cslib/Logics/Bimodal/Metalogic/Decidability/`
- Proposed split if needed:
  - 9a: Core tableau + decision procedure (~5k lines)
  - 9b: Finite model property (FMP) (~4k lines)

**PR-Separation (Task 10)** — depends on Tasks 4, 5, 7
- Branch: `bimodal/separation`
- Target: `Cslib/Logics/Bimodal/Metalogic/Separation/`
- Size: ~3,500 lines

---

## Review Cycle Management

### Response Time Commitments

| Event | Action | Timing |
|-------|--------|--------|
| Reviewer leaves comment | Respond / push fix | Within 48 hours |
| No review activity | Ping Zulip | After 7 days |
| Reviewer requests changes | Fix and re-request review | Within 48 hours |
| CI fails during review | Fix locally, push, update PR | Within 24 hours |

### Zulip Follow-Up Template

For PRs with no activity after 7 days, post to the working group channel:

> Hi @[maintainer], gentle ping on [PR title] (#[PR URL]) — happy to address any feedback or concerns. Thank you for your time!

---

## Completion Criteria

The task is complete when:
- [ ] All 14 PRs have status "MERGED" in `coordination-log.md`
- [ ] Completion message posted to Zulip working group thread
- [ ] ROADMAP.md PR pipeline milestone updated
