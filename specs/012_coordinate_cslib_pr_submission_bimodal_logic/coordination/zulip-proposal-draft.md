# Zulip Working Group Proposal — Draft

**Status**: DRAFT — requires human review and posting  
**Target channel**: `#CSLib` (or `#new streams` for working group creation)  
**Audience**: @fmontesi, @kim-em, @eric-wieser, @arademaker  
**Action**: Post this message manually; wait for responses before starting task 2

---

## Message Draft

**Topic**: Bimodal Temporal Logic (TM) formalization — working group proposal

---

Hi everyone,

I'm planning to contribute a formalization of **Bimodal Temporal Logic (TM)** to cslib. Before starting any porting work, I wanted to get feedback on the proposed structure and confirm a few key decisions.

**Background**: TM is a logic combining S5 modal logic with linear temporal logic (Until/Since operators) over "task frames" — Kripke structures with both an accessibility relation and a linear time ordering. The BimodalLogic project (~30,000 lines of Lean 4) contains:
- A verified decision procedure (tableau method)
- A completeness theorem
- A separation theorem
- Soundness proofs and frame conditions

**Proposed modular structure (14 PRs, wave-based)**:

Wave 1 (independent):
- PR-Foundations: Propositional Hilbert theorem infrastructure → `Cslib/Foundations/Logic/Theorems/` (~2,400 lines)

Wave 2 (after Foundations merged):
- PR-Modal: Modal proof system + theorems → `Cslib/Logics/Modal/ProofSystem/` + `Theorems/` (~1,600 lines)
- PR-Temporal-Infra: Temporal proof system infrastructure + theorems → `Cslib/Logics/Temporal/ProofSystem/` + `Theorems/` (~1,500 lines)
- PR-Bimodal-Syntax: Bimodal syntax infrastructure → `Cslib/Logics/Bimodal/Syntax/` (~2,500 lines)

Wave 3 (after Wave 2 merged):
- PR-TempSem: Temporal semantics on linear orders (~400-600 lines)
- PR-Semantics: Bimodal semantics → `Cslib/Logics/Bimodal/Semantics/` (~2,200 lines)
- PR-ProofSystem: Bimodal proof system (42-axiom schema) (~2,000 lines)

Waves 4-6 (Metalogic — dependent on Wave 3):
- PR-FrameConditions + Soundness (~2,370 lines)
- PR-Perpetuity theorems (~800 lines)
- PR-ConservativeExtension (~1,500 lines)
- PR-MCS (MaxConsistentSets, DeductionTheorem) (~2,500 lines)
- PR-Completeness (~15,000+ lines — see note below)
- PR-Decidability (~10,000 lines — see note below)
- PR-Separation (~3,500 lines)

**Three questions before I start:**

1. **Namespace**: Should I use `Cslib.Logic.Bimodal.*` or `Cslib.Logics.Bimodal.*`? The existing `Formula.lean` uses `Cslib.Logic.Bimodal` but the directory is `Cslib/Logics/Bimodal/`. Which convention should porting work follow?

2. **Working group**: Would a dedicated Zulip channel (e.g., `#CSLib: Bimodal Temporal Logic`) be appropriate for coordinating this 14-PR series?

3. **Large PRs**: The Completeness PR (~15k lines) and Decidability PR (~10k lines) are large. Should I plan to split them upfront (e.g., Decidability → 9a core tableau + 9b FMP), or submit as-is and split on reviewer request?

**Note on AI assistance**: Portions of the BimodalLogic source were developed with Claude (AI assistant). I will disclose this clearly in every PR description per the Mathlib AI policy.

Thanks for any feedback!

— Benjamin Brastmckie

---

## Pre-Post Checklist

Before posting this message, confirm:
- [ ] You have a Zulip account at leanprover.zulipchat.com
- [ ] You have access to the `#CSLib` stream
- [ ] Review the draft above and personalize as needed
- [ ] Post to `#CSLib` stream with topic "Bimodal Temporal Logic formalization proposal"

## Post-Post Actions

After posting:
- [ ] Record the Zulip message URL in `coordination/coordination-log.md`
- [ ] Wait for responses from @fmontesi, @kim-em, @eric-wieser before starting task 2
- [ ] Record maintainer decisions (especially namespace choice) in `coordination/coordination-log.md`
- [ ] Update porting task descriptions (tasks 2-11, 20-23) in state.json/TODO.md if namespace differs from current descriptions

## Key Contacts

| Handle | Name | Role |
|--------|------|------|
| @fmontesi | Fabrizio Montesi | Lead maintainer |
| @kim-em | Kim Morrison | CI/CD area |
| @eric-wieser | Eric Wieser | Technical reviewer |
| @arademaker | Alexandre Rademaker | Technical lead |
| @sorrachai | Sorrachai Yingchareonthawornchai | Technical lead |
