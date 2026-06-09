# PR Coordination Log — Task 12

**Project**: Bimodal Temporal Logic (TM) integration into cslib  
**Total PRs**: 14 (4 standalone + 10 bimodal)  
**Target repo**: `github.com/leanprover/cslib`  
**Zulip**: leanprover.zulipchat.com `#CSLib`

---

## Zulip Pre-Coordination

| Item | Status | Date | Notes |
|------|--------|------|-------|
| Working group proposal posted | PENDING | — | See `zulip-proposal-draft.md` for draft |
| Zulip thread URL | — | — | Record here after posting |
| Namespace confirmed | PENDING | — | `Cslib.Logic.*` vs `Cslib.Logics.*` |
| Working group channel created | PENDING | — | If approved by maintainers |
| Large PR strategy agreed | PENDING | — | Task 8 (~15k), task 9 (~10k) split strategy |
| Any blocking concerns raised | — | — | Record any architectural concerns |

**Confirmed namespace**: _Record here after maintainer response_  
**Working group Zulip channel**: _Record here if created_

---

## PR Status Tracking Table

| Task | PR Title | PR URL | Submitted | Review Status | Merge Date |
|------|----------|--------|-----------|---------------|------------|
| 20 | feat(Foundations/Logic): add Hilbert theorem infrastructure | — | PENDING | — | — |
| 21 | feat(Logics/Modal): add Modal proof system and theorems | — | PENDING | — | — |
| 22 | feat(Logics/Temporal): add Temporal proof system infrastructure | — | PENDING | — | — |
| 23 | feat(Logics/Temporal): add Temporal semantics on linear orders | — | PENDING | — | — |
| 2 | feat(Logics/Bimodal): add Syntax module | — | PENDING | — | — |
| 3 | feat(Logics/Bimodal): add Semantics module | — | PENDING | — | — |
| 4 | feat(Logics/Bimodal): add ProofSystem module | — | PENDING | — | — |
| 5 | feat(Logics/Bimodal): add Theorems/Perpetuity module | — | PENDING | — | — |
| 6 | feat(Logics/Bimodal): add FrameConditions and Soundness modules | — | PENDING | — | — |
| 11 | feat(Logics/Bimodal): add Metalogic/ConservativeExtension module | — | PENDING | — | — |
| 7 | feat(Logics/Bimodal): add Metalogic/Core module | — | PENDING | — | — |
| 8 | feat(Logics/Bimodal): add Completeness theorem | — | PENDING | — | — |
| 9 | feat(Logics/Bimodal): add Metalogic/Decidability module | — | PENDING | — | — |
| 10 | feat(Logics/Bimodal): add Metalogic/Separation module | — | PENDING | — | — |

**Review Status values**: PENDING | SUBMITTED | IN REVIEW | CHANGES REQUESTED | APPROVED | MERGED | BLOCKED

---

## Wave Submission Plan

The dependency graph determines the order of PR submission. Do NOT submit a PR before all its dependency PRs have been merged to cslib main.

```
Wave 1 (no dependencies):
  Task 20: PR-Foundations

Wave 2 (after Foundations merged):
  Task 21: PR-Modal       ←── independent of each other
  Task 22: PR-Temporal-Infra
  Task 2:  PR-Syntax      ←── depends only on namespace confirmation

Wave 3 (after respective Wave 2 PRs merged):
  Task 23: PR-TempSem     ←── after 22
  Task 3:  PR-Semantics   ←── after 2
  Task 4:  PR-ProofSystem ←── after 2, 20, 22

Wave 4 (after Wave 3 merged):
  Task 5:  PR-Perpetuity        ←── after 4, 21, 22
  Task 6:  PR-FrameConditions   ←── after 3, 4
  Task 11: PR-ConservativeExt   ←── after 4

Wave 5 (after Wave 4 merged):
  Task 7:  PR-MCS               ←── after 4, 5

Wave 6 (after Wave 5 merged):
  Task 8:  PR-Completeness  ←── after 6, 7  (NOTE: sorry disclosure required)
  Task 9:  PR-Decidability  ←── after 4, 7  (NOTE: may need 9a/9b split)
  Task 10: PR-Separation    ←── after 4, 5, 7
```

---

## Maintainer Feedback Log

Record all significant maintainer feedback here as it comes in.

| Date | Maintainer | Topic | Decision/Feedback |
|------|------------|-------|-------------------|
| — | — | — | _No responses yet — Zulip thread not yet posted_ |

---

## Open Issues / Blockers

| Issue | Severity | Status | Resolution |
|-------|----------|--------|------------|
| Namespace `Cslib.Logic.*` vs `Cslib.Logics.*` | HIGH | OPEN | Pending Zulip response |
| Task 8 sorry in chronicle construction | HIGH | OPEN | Will disclose in PR description; track upstream elimination |
| Task 8 size (~15k lines) — split strategy | MEDIUM | OPEN | Pending maintainer guidance |
| Task 9 size (~10k lines) — split strategy | MEDIUM | OPEN | Pre-plan 9a/9b split; confirm with maintainers |

---

## Completion Checklist

- [ ] Zulip thread posted
- [ ] Namespace confirmed
- [ ] All 14 PRs submitted in correct order
- [ ] All 14 PRs merged to cslib main
- [ ] Completion summary posted to Zulip working group thread
- [ ] ROADMAP.md PR pipeline milestone marked complete
