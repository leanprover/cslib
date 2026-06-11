# Teammate D Findings: Horizons Perspective
# Task 112 — Propositional Hilbert Soundness and Completeness

**Angle**: Strategic direction, long-term alignment, unconventional approaches
**Date**: 2026-06-10
**Session**: sess_1781155000_a3b4c5

---

## Executive Summary

Task 112 is not merely a gap-fill exercise. It sits at a strategic inflection point in the
project's architecture — the propositional base layer that the entire modal, bimodal, and
temporal stack ultimately rests on conceptually. Done well, it can unlock a coherent
lattice-theoretic view of all three Hilbert levels (minimal, intuitionistic, classical) and
open the door to the Godel-translation connection between intuitionistic and modal logic
that the advanced modal logic literature (AML Section 3) identifies as one of the most
structurally powerful tools in the field.

Done minimally — as a quick three-file classical-only implementation — it leaves the
project in an asymmetric state: deep modal and bimodal metalogic, but no propositional
metalogic for the two weaker systems despite their typeclass infrastructure already being
defined.

The key strategic question is not **whether** to do all three levels, but **in what order**
and **how to make the intermediate levels serve the upper levels**, not just be standalone
results.

---

## 1. Dependency Ordering: Technical vs. Conceptual

### Technical Dependency (the answer is: none)

Task 112 has no technical dependencies on the modal cube tasks (100-111), and they have
no technical dependencies on task 112. The modal completeness proofs in
`Cslib/Logics/Modal/Metalogic/` operate entirely on `Modal.Proposition` and are
self-contained. The propositional metalogic operates on `PL.Proposition`. They share the
generic MCS framework in `Foundations/Logic/Metalogic/Consistency.lean`, but each
instantiates it independently.

This means tasks 100-111 and task 112 can proceed in parallel — as they are currently
structured in the task list (all in Wave 1 with no dependencies).

### Conceptual Dependency (the answer is: 112 should logically precede, but practically follows)

From a mathematical standpoint, classical propositional completeness underlies classical
modal completeness — the modal proof systems extend the propositional ones via
`ClassicalHilbert`. The completeness proofs for all modal systems presuppose that the
propositional fragment is semantically complete. In cslib, this is currently **assumed but
not proven**.

The practical reality is that the modal proofs were built without relying on propositional
completeness (they re-derive what they need internally), so there is no urgent unblocking
dependency. However, completing task 112 first would let future modal completeness work
appeal to propositional results rather than reinventing them.

**Recommendation**: Task 112 can run in parallel with 100-111 as currently structured.
However, if resources allow prioritization, completing the classical case (Sub-task A)
before finalizing 100-111 would create a cleaner dependency structure and allow the
coherence theorem in `FromPropositional.lean` to be formalized.

---

## 2. The Three-Level Decomposition: Is the Proposed Structure Right?

The Round 1 team report proposed the following decomposition:
- Sub-task A: Classical soundness/completeness (truth-value semantics)
- Sub-task B: Propositional Kripke semantics
- Sub-task C: Intuitionistic soundness/completeness
- Sub-task D: Minimal soundness/completeness
- Sub-task E: Module integration

This structure is reasonable but has a hidden ordering problem: **Sub-task B (Kripke
semantics) should precede both C and D**, but the plan puts it as a separate task after A.
The semantics for intuitionistic and minimal logic are Kripke-based, not truth-value-based,
so Sub-tasks C and D depend directly on B.

### Proposed Revised Decomposition

A more dependency-aware ordering:

```
Sub-task A: Classical soundness/completeness (~250 lines)
  - New files: Semantics/Basic.lean, Metalogic/Soundness.lean, Metalogic/Completeness.lean
  - Bivalent valuation semantics
  - No Kripke infrastructure needed
  - Can be done immediately, follows modal completeness pattern exactly

Sub-task B: Propositional Kripke semantics (~150-200 lines)
  - New file: Semantics/Kripke.lean (or Semantics/IntFrame.lean)
  - Defines intuitionistic frames: partial orders + persistence condition
  - Defines forcing relation for minimal/intuitionistic formulas
  - This is the semantic foundation for C and D
  - CAN share or lift directly from modal Kripke infrastructure

Sub-task C: Minimal soundness/completeness (~300-400 lines)
  - Soundness: All HilbertMin axioms + MP preserve Kripke forcing
  - Completeness: Prime filter construction (not MCS — different machinery!)
  - Depends on Sub-task B

Sub-task D: Intuitionistic soundness/completeness (~300-400 lines)
  - Extends C with EFQ soundness
  - Completeness via prime theories with explosion
  - Depends on Sub-task B, can share with C

Sub-task E: Module integration and registration
  - Register HilbertMin and HilbertInt inference system instances
  - Update Cslib.lean imports
  - Depends on A, C, D
```

**Critical observation about B vs. C vs. D ordering**: The MCS approach used for
classical and modal logic does NOT work for intuitionistic and minimal logic. MCS
(maximally consistent sets) give bivalent sets — every formula or its negation is in the
set. This is exactly the classical excluded middle. For intuitionistic logic, the correct
construction is **prime theories**: deductively closed sets where `φ ∨ ψ ∈ T implies φ ∈ T
or ψ ∈ T`. For minimal logic (no EFQ), the construction is similar but the explosion case
must be handled separately.

This means **the existing MCS infrastructure (`prop_lindenbaum`, `prop_negation_complete`,
etc.) is specifically classical and cannot be reused for Sub-tasks C and D**. New
prime-theory infrastructure will need to be created for those sub-tasks.

---

## 3. The Advanced Modal Logic Literature: What's Relevant Here?

The two new sources (`advanced_modal_logic.md` and `advanced_modal_logic_2.md`) are the
Zakharyaschev-Wolter-Chagrov chapter from the Handbook of Philosophical Logic. The chapter
is primarily about:

1. The lattice structure of normal modal logics (NExtK)
2. Canonical formulas and completeness theory for large classes of logics
3. The Godel-translation connection between modal logics above S4 and superintuitionistic
   (intermediate) logics

**What is directly relevant to task 112:**

### Section 3 (lines 6140-6530): Superintuitionistic Logics and the Godel Translation

This section is directly relevant to the intuitionistic sub-tasks (B, C, D). Key results:

1. **Intuitionistic Kripke frames** (Section 3.1, line 6243): Defined as partial orders
   with upward-closed valuations. The forcing relation for implication is:
   `x ⊩ φ → ψ iff for all y ≥ x: y ⊩ φ implies y ⊩ ψ`
   This is the standard definition needed for Sub-task B.

2. **Godel translation T** (line 6437): The translation prefixing □ to all subformulas
   of an intuitionistic formula, establishing `φ ∈ Int iff T(φ) ∈ S4`. This means:
   - Once task 112 Sub-tasks B-D are done, the Godel translation provides a natural
     coherence theorem connecting `HilbertInt` derivability to `HilbertS4` derivability
   - The embedding in `FromPropositional.lean` (PL → Modal) is the syntax-level
     infrastructure already in place for exactly this kind of coherence result

3. **Skeleton Lemma** (Lemma 3.1, line 6448): For every S4 model M and intuitionistic
   formula φ, `(M, C(x)) ⊩_Int φ iff (M, x) ⊩_S4 T(φ)`. This is the semantic
   equivalence behind the syntactic Godel translation.

4. **Superintuitionistic logics** (line 6225): Extensions of Int between Int and Cl.
   The framework built for task 112 Sub-task D (minimal) and C (intuitionistic) will
   directly support formalizing any superintuitionistic logic by adding axioms to
   `HilbertInt`. This is a high-value future direction.

**What is NOT relevant to task 112:**

The bulk of the AML chapter (Sections 1-2) covers general completeness theory, canonical
formulas, Sahlqvist correspondence, and the lattice structure of NExtK. This is relevant
to the modal cube work (tasks 100-111) but not to the propositional completeness task.

**Assessment**: The AML literature does not contain anything that changes the proposed
implementation for Sub-task A (classical). It provides theoretical context for Sub-tasks
B-D but the actual proof method (prime filter completeness for intuitionistic logic) is
covered in standard references (Dummett's "Elements of Intuitionism", Troelstra-van Dalen).
The AML section's treatment of intuitionistic frames confirms the standard approach.

---

## 4. Infrastructure Asymmetry: The HilbertMin/HilbertInt Gap

A critical observation that the Round 1 report did not fully surface:

The `HilbertMin` and `HilbertInt` tag types are **defined** in `ProofSystem.lean` (lines
367-370), and the `MinimalHilbert` and `IntuitionisticHilbert` typeclasses are defined and
used extensively in `Foundations/Logic/Theorems/`. However:

- **There is no `DerivationTree` for `HilbertMin` or `HilbertInt`**. The only concrete
  derivation tree in the propositional subsystem is `PL.DerivationTree`, which corresponds
  to `HilbertCl` (see `ProofSystem/Derivation.lean` and `ProofSystem/Instances.lean`).

- **The `NaturalDeduction/` module** uses a different inference system (`Theory.Derivation`)
  parameterized by a `Theory` (set of axioms), which is closer to the minimal/intuitionistic
  approach but is separate from the typeclass hierarchy.

This means that for Sub-tasks C and D, one of two approaches must be taken:
1. **Create new derivation trees** for `HilbertMin` and `HilbertInt` (matching the `PL.DerivationTree` pattern but with different axiom sets), then register inference system instances
2. **Reuse `NaturalDeduction/`** machinery by identifying `HilbertInt` with `IPL`-derivability and `HilbertMin` with `MPL`-derivability from `Defs.lean`

Option 2 is strategically preferable because it unifies two currently parallel proof
systems (the natural deduction system from `NaturalDeduction/` and the Hilbert system from
`ProofSystem/`). The `NaturalDeduction/Equivalence.lean` file presumably already contains
work connecting these, making this unification viable.

---

## 5. Shared Kripke Frame Abstraction: Strategic Opportunity

The existing modal Kripke semantics in `Modal/Basic.lean` defines:
```lean
structure Model (World : Type*) (Atom : Type*) where
  r : World → World → Prop
  v : World → Atom → Prop
```

Intuitionistic Kripke frames have an additional **persistence constraint**: if `w ⊩ p` and
`w R w'`, then `w' ⊩ p`. This is a semantic constraint not a structural one.

The strategic question is: should we create a unified `KripkeFrame` abstraction in
`Foundations/Logic/` that:
1. Defines a frame as `(World, Relation)` with an optional persistence constraint
2. Provides a typeclass `PersistentFrame` for frames with the monotonicity property
3. Allows `Modal.Model` to be specialized from this abstraction

This would allow propositional Kripke semantics (for Int/Min) and modal Kripke semantics
(for K, T, S4, etc.) to share the same underlying frame infrastructure.

**Assessment**: This abstraction is theoretically attractive but would require refactoring
existing modal code, creating technical debt risk. For task 112 specifically, the pragmatic
approach is to define `IntFrame` (intuitionistic frame) in `Propositional/Semantics/Kripke.lean`
as a separate structure, and note the abstraction opportunity for a future `Foundations/`
task. The coherence connection (via Godel translation) makes the relationship explicit
without requiring structural unification.

---

## 6. Coherence Theorems: Importance and Timing

The `FromPropositional.lean` file defines `PL.Proposition.toModal` and establishes:
- `toModal_atom`, `toModal_bot`, `toModal_imp` (preservation of constructors)

What is missing is the **semantic coherence theorem**:
> If `v : World → Atom → Prop` is the modal valuation and `v' : Atom → Prop` is the
> propositional valuation defined by `v' p = v w p`, then
> `Eval v' φ ↔ (w ⊩_Modal φ.toModal)` for all worlds `w`.

Once task 112 Sub-task A is complete (bivalent semantics defined), this coherence theorem
becomes provable in ~20 lines. It would belong in a new file
`Propositional/Metalogic/Embedding.lean` or directly in `Modal/FromPropositional.lean`.

**Strategic importance**: This theorem establishes that the propositional-to-modal embedding
is semantically faithful, not just syntactically. Without it, `FromPropositional.lean` is
a syntactic convenience without semantic content. With it, any validity result proved in
propositional logic automatically lifts to modal logic via the embedding.

**Recommendation**: Add this coherence theorem as part of Sub-task E (module integration),
not as a separate task. It is small (20-30 lines) and creates significant architectural
value.

---

## 7. The Intuitionistic Case: Prime Filters vs. MCS

This is the most technically important strategic consideration for the planner.

For the **classical** case (Sub-task A), completeness goes through:
1. Assume `⊬ φ`
2. `{¬φ}` is consistent
3. Lindenbaum: extend to MCS `M`
4. Canonical valuation: `v p = (atom p ∈ M)`
5. Truth Lemma: `Eval v ψ ↔ ψ ∈ M`
6. Contradiction: `Eval v φ = False` but `v` is arbitrary

For the **intuitionistic** case (Sub-task C), completeness goes through:
1. Assume `⊬_Int φ`
2. `{φ}` is not a theorem, so it is not in every prime theory extending `∅`
3. By the prime filter completion (analog of Lindenbaum for prime theories), there exists a
   prime theory `T` not containing `φ`
4. The **canonical model** has worlds = prime theories, accessibility = set inclusion
5. Truth Lemma: `T ⊩ ψ ↔ ψ ∈ T` (proved by induction, with the `→` case using primeness)
6. `T ⊩ φ` fails at the specific `T` from step 3

The **Lindenbaum lemma for prime theories** (Zorn-based) is structurally similar to
`set_lindenbaum` in `Consistency.lean`, but uses a different maximality criterion
(primeness with respect to disjunction, not classical maximal consistency). This will
require a new lemma, approximately 50-80 lines.

**Key difference**: For intuitionistic logic, the canonical model has **multiple worlds**
(one per prime theory), with accessibility given by theory inclusion. For classical logic,
the canonical "model" is a single valuation. This structural difference means Sub-tasks C
and D require qualitatively different machinery than Sub-task A.

---

## 8. Recommended Implementation Ordering

Given all the above analysis, the strategic recommendation is:

### Phase 1 (Immediate — Sub-task A): Classical completeness
- Implement the three files identified in the Round 1 report
- Estimated: 250 lines, 1-2 implementation cycles
- Unblocks: coherence theorem with modal logic, PR submission readiness

### Phase 2 (Short-term — Sub-task B): Intuitionistic Kripke semantics
- Create `Propositional/Semantics/Kripke.lean` with:
  - `IntFrame`: partial order with accessibility relation
  - `PersistentValuation`: valuations monotone under accessibility
  - `Forces`: forcing relation for all formula constructors
  - `IntValid`: validity over all intuitionistic frames
- Estimated: 150-200 lines
- Enables: Sub-tasks C and D

### Phase 3 (Medium-term — Sub-tasks C and D): Intuitionistic and minimal completeness
- Create prime filter Lindenbaum lemma
- Canonical model construction with prime theory worlds
- Truth lemma for intuitionistic forcing
- Separate sub-tasks for Int vs. Min (different axiom assumptions)
- Estimated: 600-800 lines across both
- Enables: Godel translation coherence theorem

### Phase 4 (Integration — Sub-task E):
- Register `HilbertMin` and `HilbertInt` inference system instances
  (requires resolving the derivation tree gap identified above)
- Coherence theorem for classical embedding into modal
- Cslib.lean imports

### Expansion Decision
**Recommendation**: Task 112 should be EXPANDED into 5 sub-tasks as above before the
implementation phase begins. The classical case (Sub-task A) should be a standalone
immediately-actionable task, while the intuitionistic/minimal cases require additional
design work (prime filter infrastructure, derivation tree choice for Int/Min).

---

## 9. Risk Inventory

| Risk | Severity | Mitigation |
|------|----------|------------|
| MCS infrastructure not reusable for Int/Min | High | New prime filter Lindenbaum lemma needed; plan for this explicitly |
| No DerivationTree for HilbertMin/HilbertInt | Medium | Decision needed on NatDed vs. new HilbertTree |
| Intuitionistic forcing is recursive, persistence requires care | Medium | Follow standard reference (Troelstra-van Dalen) step-by-step |
| Coherence theorem scope creep | Low | Cap to 30 lines, defer if blocking |
| Godel translation formalization temptation | Low | Defer to a future task (task 113?) |

---

## 10. Broader Strategic Alignment

Looking further ahead: the cslib project's stated scope (ROADMAP.md) is propositional +
modal + temporal + bimodal. Within this scope, task 112 fills the last semantic gap at
the propositional level. But the project's true long-term potential extends to:

1. **Superintuitionistic logics**: Once Int Kripke semantics exists, adding any
   intermediate logic (LC, KC, Dummett's linear logic, etc.) is a matter of adding
   frame constraints — exactly the same pattern as modal cube extensions (tasks 100-111)

2. **Godel translation** into S4: The connection between Int and S4 established by McKinsey-
   Tarski is one of the deepest results in propositional logic. Formalizing it in Lean would
   be a significant result.

3. **Proof system unification**: The `MinimalHilbert`/`IntuitionisticHilbert`/`ClassicalHilbert`
   typeclass hierarchy is already correct. Once all three have associated semantics, the
   hierarchy becomes a semantically graded tower, not just a syntactic one.

The AML literature confirms that "the theory of intermediate logics is reducible to the
theory of logics in NExtS4" (Section 3, line 6158). This means the machinery being built
for the modal cube (NExtS4 includes S4, and intermediate logics correspond to S4-extensions)
has a natural propositional mirror image. Task 112 is the bridge between these worlds.

---

## Summary of Key Recommendations

1. **Expand task 112** into 5 sub-tasks (A through E) before implementation
2. **Start with Sub-task A** (classical) — it's the straightforward path forward
3. **Plan for new prime filter infrastructure** in Sub-task B — the MCS approach does not transfer to Int/Min
4. **Resolve the HilbertMin/HilbertInt derivation tree gap** as part of Sub-task E design
5. **Add the semantic coherence theorem** for `FromPropositional.lean` as part of Sub-task E
6. **The AML literature** is relevant primarily as background on the Godel translation and superintuitionistic logics — not directly actionable for the immediate classical implementation
7. **Task 112 and tasks 100-111** can proceed in parallel; no technical blocking relationship exists
8. **Long-term**: The Godel translation (Int → S4) is the highest-value result enabled by completing task 112, and should be tracked in the roadmap

---

## References

- `Cslib/Foundations/Logic/ProofSystem.lean` — MinimalHilbert/IntuitionisticHilbert/ClassicalHilbert hierarchy, HilbertMin/HilbertInt tag types (lines 278-374)
- `Cslib/Logics/Propositional/Defs.lean` — Theory.MPL (minimal), Theory.IPL (intuitionistic), Theory.CPL (classical) definitions
- `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` — Theory.Derivation (natural deduction infrastructure)
- `Cslib/Logics/Modal/FromPropositional.lean` — PL.Proposition.toModal embedding (coherence theorem target)
- `specs/literature/advanced_modal_logic_2.md` — Section 3 (lines 6140-6530): superintuitionistic logics, intuitionistic frames, Godel translation
- `specs/literature/advanced_modal_logic_2.md` — Lemma 3.1 (Skeleton Lemma, line 6448): semantic bridge between Int and S4
