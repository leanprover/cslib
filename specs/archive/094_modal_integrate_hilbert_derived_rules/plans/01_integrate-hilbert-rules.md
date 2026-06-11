# Task 94: Integrate HilbertDerivedRules into Module Graph

## Phase 1: Add Imports to Cslib.lean [NOT STARTED]

### Steps
- [ ] Add `import Cslib.Logics.Propositional.NaturalDeduction.DerivedRules` to Cslib.lean
- [ ] Add `import Cslib.Logics.Propositional.NaturalDeduction.Equivalence` to Cslib.lean
- [ ] Add `import Cslib.Logics.Propositional.NaturalDeduction.HilbertDerivedRules` to Cslib.lean
- [ ] Insert at lines ~295-297, between existing Basic and FromHilbert entries, maintaining alphabetical order

### Verification
- [ ] `lake build` passes with zero errors
- [ ] All 3 files appear in build output
