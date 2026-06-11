# Research Report: Task #112 — Teammate C (Critic) Findings

**Task**: 112 — Establish soundness and completeness for the propositional Hilbert proof systems
**Role**: Teammate C (Critic) — gaps, risks, blind spots
**Date**: 2026-06-10

---

## Key Findings

### 1. Axiom System Is Correct and Complete

The four axiom schemata in `PropositionalAxiom` (ImplyK, ImplyS, EFQ, Peirce) together with
modus ponens constitute a standard complete axiomatization of classical propositional logic. This
is the Hilbert system CPC and is well-known to be sound and complete with respect to bivalent
truth-value semantics. **No concern here.**

### 2. There Is No Propositional Semantics File Yet

This is the single most critical gap. The entire propositional logic subtree lacks:
- A `Satisfies` (or `Eval`) definition mapping valuations to truth values
- A `Valid` or `Tautology` definition
- Any file under `Cslib/Logics/Propositional/Semantics/`

The modal logic pattern defines `Satisfies` in `Modal/Basic.lean` and a `Model` structure.
For propositional logic, the semantics is simpler: a valuation is a function
`Atom → Prop` (or `Atom → Bool`), and `Eval : (Atom → Prop) → Proposition Atom → Prop`
is defined recursively on the proposition structure. **No existing propositional semantics
infrastructure exists; it must be created from scratch.**

### 3. `Proposition` Requires `[DecidableEq Atom]`

`Defs.lean` line 43 declares `variable {Atom : Type u} [DecidableEq Atom]`. The `Proposition`
inductive derives `DecidableEq, BEq`. This constraint pervades the entire propositional module.

**Risk**: Truth-value semantics does not technically need `DecidableEq Atom` — evaluation is
purely structural. However, since the existing infrastructure commits to `[DecidableEq Atom]`
as a context variable, this constraint will implicitly appear throughout. This should be
harmless but must be explicitly noted in every definition and theorem.

**Second risk**: The completeness theorem's canonical valuation is `v(p) := (Proposition.atom p ∈ S)`
for an MCS `S`. Since `Proposition.atom p` involves the `Proposition` type (which has `DecidableEq`
via the derived instance), this is fine. But if someone tries to state completeness for an
**arbitrary** atom type without `DecidableEq`, they will be blocked by the current infrastructure.

### 4. The Completeness Proof Is Simpler Than Modal — But Watch the MCS Canonical Valuation

For classical propositional logic, the completeness proof via MCS is:
1. Suppose `φ` is not derivable from `[]`.
2. `{¬φ}` is consistent (otherwise `[] ⊢ ¬φ → ⊥`, and by Peirce/EFQ, `[] ⊢ φ`).
3. By Lindenbaum, extend `{¬φ}` to an MCS `S`.
4. Define a valuation `v(p) := (Proposition.atom p ∈ S)`.
5. Prove a Truth Lemma: `Eval v φ ↔ φ ∈ S` (by structural induction on `φ`).
6. Since `¬φ ∈ S` and `φ ∉ S` (from `prop_mcs_not_mem_of_neg`), `Eval v φ = False`, contradicting
   validity of `φ`.

**Risk**: Step 5 (Truth Lemma) for the `imp` case requires showing that `φ → ψ ∈ S` iff
`(φ ∈ S → ψ ∈ S)`. The `←` direction uses `prop_implication_property` (already proven).
The `→` direction requires showing: if `φ → ψ ∈ S` and `φ ∈ S`, then `ψ ∈ S`. This also
uses `prop_implication_property`. **But**: both directions of the implication also need to
handle the case where `φ ∉ S`. The `→` direction: if `φ → ψ ∈ S` and `φ ∉ S`, then the
implication `Eval v φ → Eval v ψ` holds vacuously. No extra lemmas needed there.

**The harder sub-case**: if `φ → ψ ∉ S`, we need `φ ∈ S` and `ψ ∉ S`. By
`prop_mcs_neg_of_not_mem`, `¬(φ → ψ) ∈ S`. Since `¬(φ → ψ) = (φ → ψ) → ⊥`, using
`prop_implication_property` and the fact that `Peirce` is an axiom... this requires deriving
`φ ∈ S` and `ψ ∉ S` from `¬(φ → ψ) ∈ S`. This is the step that requires explicit derivation
trees — **it is exactly what the modal Truth Lemma does in `Completeness.lean` lines 178–222**.
The propositional version will follow the same pattern, but without the `box` case.

**Missing MCS lemma**: The propositional `MCS.lean` does NOT have an analogue of
`modal_closed_under_derivation` that takes explicit `h_implyK`/`h_implyS` arguments.
It only has `prop_closed_under_derivation` (which passes `propDerivationSystem` directly).
This is actually fine since the propositional proof is not parameterized over an arbitrary
axiom set — but it means the proof style differs from the modal pattern. Specifically, the
inline derivation tree constructions in the Truth Lemma will need to call
`prop_closed_under_derivation` directly with `propDerivationSystem`.

### 5. Universe Polymorphism

`Defs.lean` declares `universe u` and `Proposition (Atom : Type u) : Type u`. The MCS
framework in `Consistency.lean` uses `{F : Type*}`. Lindenbaum uses `zorn_subset_nonempty`,
which does not impose universe constraints beyond `Type*`. **No universe polymorphism issues
are anticipated**, but the completeness theorem's canonical world type will be:

```lean
CanonicalWorld : Set (PL.Proposition Atom)
```

Unlike the modal case which defines a `subtype` (`{ S : Set (Proposition Atom) // MCS S }`),
the propositional completeness proof can either use a subtype or just work with `S : Set (...)`.
This is a design choice with no correctness risk, but it affects how the Truth Lemma is stated.

### 6. Scope: Should Intuitionistic/Minimal Be Proved?

The task description says "propositional Hilbert proof systems" (plural), which could mean:
- Only `ClassicalHilbert` (K, S, EFQ, Peirce, MP) — soundness/completeness w.r.t. bivalent semantics
- `IntuitionisticHilbert` (K, S, EFQ, MP) — soundness/completeness w.r.t. Kripke semantics
- `MinimalHilbert` (K, S, MP) — soundness/completeness w.r.t. Kripke semantics for minimal logic

**Critical risk**: Intuitionistic and Minimal completeness require Kripke semantics (ordered
sets of possible worlds), NOT bivalent truth-value semantics. This is a completely different
proof structure and much more complex. The bivalent semantics `Eval v φ` does NOT work for
intuitionistic logic (it validates `¬¬p → p`). **If the task intends to cover more than
`ClassicalHilbert`, the scope more than doubles and requires entirely new semantic infrastructure.**

The existing `Theory.IsIntuitionistic` and `Theory.IsClassical` in `Defs.lean` suggest the
developer is aware of the distinction. The `ClassicalHilbert`/`IntuitionisticHilbert`/
`MinimalHilbert` hierarchy in `ProofSystem.lean` is already defined. The recommendation is
to **start with ClassicalHilbert only** and create separate tasks for the intuitionistic/
minimal cases if needed.

### 7. Soundness Is Straightforward

Soundness for propositional classical logic is a simple structural induction on the derivation
tree:
- `ax`: Show each axiom schema is a tautology (5 cases, all trivial)
- `assumption`: Trivial from hypothesis
- `modus_ponens`: Follows from induction hypotheses
- `weakening`: Follows from induction hypothesis

The parameterized pattern from `Modal/Metalogic/Soundness.lean` (which takes a
callback `h_ax_sound`) can be reused verbatim: it works for any axiom set where every axiom
is valid. The propositional soundness theorem just needs to instantiate the callback with
`PropositionalAxiom` and prove each case.

**Watch point**: The `soundness` theorem in `Modal/Metalogic/Soundness.lean` pattern-matches on
`.necessitation` (line 102). There is no such constructor in the propositional `DerivationTree`.
A clean propositional soundness proof should be written fresh (not copy-paste from modal).

### 8. DerivationSystem Connection

`propDerivationSystem` in `Derivation.lean` wraps `Deriv` (i.e., `Nonempty (DerivationTree Γ φ)`)
for the generic MCS framework. The `prop_closed_under_derivation` in `MCS.lean` (line 65) calls
`Metalogic.SetMaximalConsistent.closed_under_derivation` with `propDerivationSystem` and
`prop_has_deduction_theorem`.

**Note**: The `propDerivationSystem` uses `List`-based contexts, and the MCS framework is
`Set`-based (Lindenbaum's lemma works on sets). The `closed_under_derivation` lemma bridges
this by taking a `List L ⊆ S`. **This bridge already exists and works correctly.**

### 9. The Deduction Theorem Scope

The deduction theorem (`DeductionTheorem.lean`) works for arbitrary `List`-contexts. In the
completeness proof, we only use it for `{¬φ} ⊢ ⊥ → [] ⊢ ¬φ → ⊥`, which is a single-element
list. **No issue here.**

### 10. No Missing MCS Properties for Propositional Completeness

The propositional `MCS.lean` already provides:
- `prop_lindenbaum` ✓
- `prop_closed_under_derivation` ✓
- `prop_implication_property` ✓
- `prop_negation_complete` ✓
- `prop_mcs_bot_not_mem` ✓
- `prop_mcs_neg_of_not_mem` ✓
- `prop_mcs_not_mem_of_neg` ✓
- `prop_mcs_mem_iff_neg_not_mem` ✓

**All MCS properties needed for the completeness proof are already proven.** The only missing
piece is the semantics layer and the soundness/completeness theorems themselves.

---

## Gaps and Risks Identified

| # | Gap / Risk | Severity | Notes |
|---|-----------|----------|-------|
| G1 | No propositional semantics file exists | **Critical** | Must create `Eval`, `Valid`, `Tautology` |
| G2 | Scope ambiguity: classical-only vs. intuitionistic/minimal | **High** | Intuitionistic requires Kripke semantics |
| G3 | `[DecidableEq Atom]` constraint inherited throughout | Low | Harmless but must be noted explicitly |
| G4 | Truth Lemma `imp` case requires inline derivation constructions | Medium | Follow modal pattern from `Completeness.lean` lines 178–222 |
| G5 | Soundness proof must avoid copy-pasting modal code (no `.necessitation`) | Low | Easy to avoid with fresh proof |
| G6 | No analogue of `modal_closed_under_derivation` with explicit axiom args | Low | Use `prop_closed_under_derivation` directly |
| G7 | `noncomputable` required throughout (uses `Classical.propDecidable`) | Low | Expected for Hilbert-style proofs |

---

## Questions That Need Answers

**Q1**: Does the task intend soundness/completeness for `ClassicalHilbert` only, or also for
`IntuitionisticHilbert`/`MinimalHilbert`? The answer changes the scope by 2-3x and requires
entirely different semantic machinery (Kripke models) for the non-classical cases.

**Q2**: Should the semantics be defined in terms of `Prop`-valued valuations (`Atom → Prop`)
or `Bool`-valued valuations (`Atom → Bool`)? The `Prop`-valued approach matches the rest of
the codebase (Modal uses `v : World → Atom → Prop`). The `Bool`-valued approach would make
decidability trivial but require `DecidablePred` lemmas. **Recommendation**: use `Atom → Prop`
for consistency with the modal pattern.

**Q3**: Should the canonical valuation in the completeness proof use a subtype
`{ S // PropSetMaximalConsistent S }` as the "world" (mirroring `CanonicalWorld` in the modal
case), or just use `S : Set (Proposition Atom)` directly? Both work; using a subtype is cleaner
and mirrors the existing modal infrastructure.

**Q4**: Should the soundness theorem be stated at the `DerivationTree` level (strong form:
from a derivation tree derive satisfaction at all valuations) or only at the `Derivable`
(existential) level? The modal code has both `soundness` and `soundness_derivable`. Both are
easy to prove; including both is recommended.

**Q5**: Should there be a parameterized soundness theorem (over arbitrary axiom predicates
with a validity callback), mirroring `Modal/Metalogic/Soundness.lean`? This would allow
reuse for future sub-logics. Given that propositional logic has no frame-dependent axioms,
a concrete (non-parameterized) proof over `PropositionalAxiom` is sufficient and simpler.

---

## Confidence Level

**High confidence** that:
- The MCS infrastructure is complete and correct; no missing lemmas needed there
- Soundness will be straightforward (1–2 hours of Lean work)
- Completeness for `ClassicalHilbert` is feasible following the modal pattern exactly
- The `[DecidableEq Atom]` constraint is harmless

**Medium confidence** that:
- The Truth Lemma `imp` case can be completed without new MCS lemmas (relies on
  `prop_closed_under_derivation` and inline derivation tree constructions)

**Low confidence** / **Uncertain**:
- Whether the task intends to include intuitionistic/minimal cases (scope question)
- Whether the existing `Theory.IsClassical` / `Theory.IsIntuitionistic` definitions in
  `Defs.lean` are meant to connect to this task (they use a different style than `DerivationTree`)

---

## Recommended File Structure

```
Cslib/Logics/Propositional/
  Semantics/
    Eval.lean             -- Valuation type, Eval function, Valid/Tautology definitions
  Metalogic/
    Soundness.lean        -- Propositional soundness (axiom validity + structural induction)
    Completeness.lean     -- Propositional completeness (canonical valuation, Truth Lemma)
    MCS.lean              -- [existing, complete]
    DeductionTheorem.lean -- [existing, complete]
```

The task description already suggests this split. The Soundness and Completeness files are
independent of each other once `Semantics/Eval.lean` exists.

---

## Appendix: Key File Cross-References

- **Axioms**: `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/ProofSystem/Axioms.lean`
- **Derivation**: `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/ProofSystem/Derivation.lean`
- **MCS**: `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Metalogic/MCS.lean`
- **DeductionTheorem**: `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Metalogic/DeductionTheorem.lean`
- **ProofSystem hierarchy**: `/home/benjamin/Projects/cslib/Cslib/Foundations/Logic/ProofSystem.lean`
- **Generic MCS**: `/home/benjamin/Projects/cslib/Cslib/Foundations/Logic/Metalogic/Consistency.lean`
- **Modal Soundness pattern**: `/home/benjamin/Projects/cslib/Cslib/Logics/Modal/Metalogic/Soundness.lean`
- **Modal Completeness pattern**: `/home/benjamin/Projects/cslib/Cslib/Logics/Modal/Metalogic/Completeness.lean` (esp. lines 145–300)
- **Modal K Completeness (simpler)**: `/home/benjamin/Projects/cslib/Cslib/Logics/Modal/Metalogic/KCompleteness.lean`
