# Teammate B Findings (Round 2): Alternative Approaches and Code Reuse

**Task**: 112 — Establish soundness and completeness for ALL THREE propositional Hilbert systems
**Teammate**: B (Alternative Approaches / Code Reuse Researcher)
**Date**: 2026-06-10
**Focus**: Maximize reuse across HilbertCl / HilbertInt / HilbertMin; evaluate Gödel translation approach; assess shared Kripke infrastructure

---

## Executive Summary

This report addresses the scope expansion confirmed in round 1: ALL three levels — classical
(`HilbertCl`), intuitionistic (`HilbertInt`), and minimal (`HilbertMin`) — are in scope.
The key findings are:

1. **Classical completeness** is a direct simplification of the modal K pattern (no new issues
   from round 1).
2. **Intuitionistic/minimal completeness** requires a fundamentally different semantic layer:
   Kripke frames over partial orders with persistent (upward-closed) valuations. CZ Section 2.2
   defines this precisely and Section 2.6 provides the Hintikka-system completeness proof.
3. **The modal `Model World Atom` structure IS directly reusable** for intuitionistic Kripke
   semantics: a Kripke frame `(W, R)` with `R` a partial order is exactly
   `Modal.Model World Atom` with `r` restricted to partial orders. The intuitionistic
   `Satisfies` relation has the same shape minus the `box` case, plus the persistence
   condition on valuations.
4. **The Hintikka-system approach in CZ Section 2.6** provides a clean canonical Kripke model
   construction for Int and Min that avoids MCS entirely — it uses "prime deductively-closed
   theories" instead. This is the canonical approach in the literature and can be adapted
   from the modal infrastructure with moderate work.
5. **The Gödel translation approach** (CZ Theorem 3.83, embedding Int → S4) is **not
   recommended** for deriving Int completeness: it requires S4 completeness as a premise, adds
   a semantic detour, and produces a less direct proof. The direct Kripke approach matches
   the codebase pattern better.
6. **Code reuse estimate**: a shared `Propositional/Semantics/Kripke.lean` file (~80 lines)
   can define the intuitionistic forcing relation once, and both Int and Min can instantiate it
   with different axiom callbacks — exactly mirroring the modal `soundness` parameterization.

---

## 1. The Classical Case Is Already Well-Understood

Round 1 Teammate B established the complete picture for `HilbertCl`. The key facts are
unchanged and are not duplicated here. The relevant files are:
- Template: `Cslib/Logics/Modal/Metalogic/KCompleteness.lean` (lines 168–323)
- New file: `Cslib/Logics/Propositional/Semantics/Basic.lean` (Valuation, Evaluate, Tautology)
- New file: `Cslib/Logics/Propositional/Metalogic/Soundness.lean`
- New file: `Cslib/Logics/Propositional/Metalogic/Completeness.lean`

**Nothing new to add for the classical case.** See the round 1 synthesis report.

---

## 2. Intuitionistic Kripke Semantics: Formal Definitions from CZ

CZ Section 2.2 (page 25) gives the precise definitions needed for `HilbertInt` and `HilbertMin`.

### 2.1 Frame and Model

An **intuitionistic Kripke frame** is a pair `(W, R)` where `R` is a partial order on `W`
(reflexive, transitive, antisymmetric). CZ explicitly states: "an intuitionistic Kripke frame
is just a partially ordered set."

A **valuation** `v : Atom → W → Prop` must satisfy the **persistence condition**:
```
∀ (p : Atom) (x y : W), v p x → R x y → v p y
```
(Atom truth sets are upward-closed.)

The **forcing relation** `(m, x) ⊩ φ` is defined by induction on `φ`:
- `(m, x) ⊩ atom p`   iff `v p x`
- `(m, x) ⊩ ⊥`        iff `False`  (never forced)
- `(m, x) ⊩ φ ∧ ψ`   iff `(m, x) ⊩ φ ∧ (m, x) ⊩ ψ`
- `(m, x) ⊩ φ ∨ ψ`   iff `(m, x) ⊩ φ ∨ (m, x) ⊩ ψ`
- `(m, x) ⊩ φ → ψ`   iff `∀ y, R x y → (m, y) ⊩ φ → (m, y) ⊩ ψ`

The critical distinction from classical semantics: **implication is evaluated over all
accessible worlds**, not just the current world. This is what makes the semantics
non-classical and validates Int but not Peirce.

**For minimal logic (HilbertMin)**: the same semantics applies. Minimal logic is sound and
complete with respect to exactly the same class of Kripke frames (all partial orders). The
difference is only in the proof system: HilbertMin lacks EFQ, so `⊥ → φ` is not provable.
Both Int and Min share the semantics; they differ in which formulas are validated.

Note: CZ Section 2.1 (motivation) observes that a single-point intuitionistic frame is
equivalent to a classical model (CZ page 26, bottom). This is the connection between
classical and intuitionistic semantics.

### 2.2 Key Semantic Properties

CZ Proposition 2.1 (persistence): if `(m, x) ⊩ φ` and `R x y` then `(m, y) ⊩ φ`. This
holds for all formulas, not just atoms — and must be proved by induction on `φ`. This is
**required** for the completeness proof and must be formalized as a lemma.

---

## 3. Can the Modal `Model World Atom` Be Reused?

**Yes, directly.** The modal `Model World Atom` structure is:
```lean
structure Model (World : Type*) (Atom : Type*) where
  r : World → World → Prop
  v : World → Atom → Prop
```

An intuitionistic Kripke model is exactly this structure with the constraint that `r` is a
partial order and `v` satisfies persistence. In Lean 4, these constraints can be expressed
as typeclasses on the accessibility relation and as a `Prop`-valued hypothesis on `v`.

Concretely, the intuitionistic satisfaction relation would be:

```lean
-- Intuitionistic forcing: reuses Modal.Model, constrains r to partial orders
def IForces (m : Modal.Model World Atom) [Preorder World] [IsTrans World m.r]
    (x : World) : PL.Proposition Atom → Prop
  | .atom p  => m.v x p
  | .bot     => False
  | .imp φ ψ => ∀ y, m.r x y → IForces m y φ → IForces m y ψ
```

However, there is a **semantic mismatch**: the modal `Model.v` has type `World → Atom → Prop`
(world first), while `PL.Proposition` uses atoms as `Atom`. The indexing order is reversed.
This is cosmetic but requires attention during implementation.

A cleaner approach — avoiding the ordering issue — is to define a dedicated

```lean
structure IModel (World : Type*) (Atom : Type*) where
  r : World → World → Prop   -- partial order constraint separate
  v : Atom → World → Prop    -- atom truth set, must be upward closed
```

This mirrors the CZ convention (valuation maps atoms to sets of worlds) and avoids confusion
with the modal indexing convention. The penalty is a small new structure definition (~10
lines) rather than direct reuse.

**Recommendation**: Define a new `IModel` for intuitionistic semantics in a new file
`Cslib/Logics/Propositional/Semantics/Kripke.lean`. Import `Modal/Basic.lean` for reference
but do not inherit from it — the persistent valuation constraint makes inheritance awkward.

---

## 4. Parameterized Soundness: Direct Reuse of Modal Pattern

The modal `soundness` theorem in `Soundness.lean` is:
```lean
theorem soundness {Axioms : Proposition Atom → Prop} {World : Type*}
    {Γ : List (Proposition Atom)} {φ : Proposition Atom}
    (d : DerivationTree Axioms Γ φ)
    (m : Model World Atom)
    (h_ax_sound : ∀ (ψ : Proposition Atom), Axioms ψ → ∀ (w : World), Satisfies m w ψ)
    (w : World)
    (h_ctx : ∀ ψ ∈ Γ, Satisfies m w ψ) : Satisfies m w φ
```

For intuitionistic/minimal propositional soundness, the exact same parameterized structure
works with `IForces` replacing `Satisfies`:

```lean
theorem int_soundness {Axioms : PL.Proposition Atom → Prop} {World : Type*}
    [PartialOrder World]
    {Γ : List (PL.Proposition Atom)} {φ : PL.Proposition Atom}
    (d : PL.DerivationTree Axioms Γ φ)
    (m : IModel World Atom)
    (hm_po : IsPartialOrder World m.r)
    (hm_persist : ∀ p x y, m.v p x → m.r x y → m.v p y)  -- persistence
    (h_ax_sound : ∀ (ψ : PL.Proposition Atom), Axioms ψ →
      ∀ (w : World), IForces m w ψ)
    (w : World)
    (h_ctx : ∀ ψ ∈ Γ, IForces m w ψ) : IForces m w φ
```

The proof is again induction on `DerivationTree`. The cases are:
- `ax`: use `h_ax_sound`
- `assumption`: use `h_ctx`
- `modus_ponens`: The `IForces m w (φ → ψ)` case gives `∀ y, m.r w y → IForces m y φ →
  IForces m y ψ`. Since `m.r w w` (reflexivity from partial order), we get the result.
- `weakening`: straightforward

The **key difference from classical soundness** is the `imp` case: `IForces m w (φ → ψ)` is
`∀ y, m.r w y → IForces m y φ → IForces m y ψ`, not just `IForces m w φ → IForces m w ψ`.
The MP application needs the reflexivity of `m.r` to step from `w` to itself.

Then:
- `int_axiom_sound` for `IntuitionisticAxiom` (implyK, implyS, efq): verify each validates on
  all partial orders. The EFQ case: `⊥ → φ` — `IForces m w (⊥ → φ)` requires
  `∀ y, m.r w y → IForces m y ⊥ → IForces m y φ`, but `IForces m y ⊥ = False`, so this
  is vacuously true. This is NOT the same as classical soundness — it does not use explosion.
- `min_axiom_sound` for `MinimalAxiom` (implyK, implyS): trivially a subset of the above.

The EFQ soundness case is vacuously true (since `⊥` is never forced), which is correct
semantically for both Int and Min. The difference between Int and Min completeness is only
visible in completeness, not soundness.

**Peirce's law is NOT sound on partial orders**: `((φ → ψ) → φ) → φ` fails on any Kripke
frame with more than one point. This is the semantic explanation of why classical and
intuitionistic completeness use different semantics.

### Shared Parameterized Soundness

A single `int_soundness` theorem parameterized over `Axioms` covers both Int and Min, with
two thin wrappers:
```lean
-- For HilbertInt: instantiate with IntuitionisticAxiom (implyK + implyS + efq)
theorem int_soundness_derivable : Derivable IntAxiom φ → IValid φ := ...

-- For HilbertMin: instantiate with MinimalAxiom (implyK + implyS only)
theorem min_soundness_derivable : Derivable MinAxiom φ → IValid φ := ...
```

Both use the same `int_soundness` core with different axiom callbacks. Estimated code: ~40
lines total (shared core + two wrappers).

---

## 5. Completeness for Int and Min: The Hintikka-System Approach

CZ Section 2.6 (pages 45–46) proves completeness for Int using **Hintikka systems** — not
MCS. This is the CZ approach and is the right method to follow.

### 5.1 Why Not MCS?

Classical completeness (Section 1.5 / CZ Theorem 1.16) uses MCS because every classical
formula is either in an MCS or its negation is. MCS is a perfect canonical model construction
for bivalent semantics.

For intuitionistic semantics, **MCS does NOT work directly** because:
1. Int does NOT satisfy the law of the excluded middle — an MCS of Int formulas would validate
   `φ ∨ ¬φ`, which is not in Int.
2. The canonical world in an intuitionistic model is not a single maximally consistent set but
   a **prime deductively-closed theory** (a set closed under conjunction and under implication,
   where `φ ∨ ψ ∈ T` implies `φ ∈ T` or `ψ ∈ T`).

CZ's approach uses "Hintikka systems" (Definition 2.30, page 35) — which are essentially
canonical Kripke models built from saturated tableaux. The key facts:

### 5.2 The CZ Proof Structure (Section 2.6)

The completeness proof for Int (CZ Theorem 2.43) follows exactly the same pattern as CZ
Theorem 1.16 for classical logic:

**Step 1**: A formula `φ` fails to be Int-derivable iff the tableau `(∅, {φ})` is consistent
in Int (i.e., there is no derivation of `ψ₁ ∨ ... ∨ ψₙ` from `∅` for any `ψᵢ ∈ {φ}`).

**Step 2**: Extend the consistent tableau `t₀ = (∅, {φ})` to a disjoint saturated consistent
tableau using all subformulas of `φ`. The extension is by the same saturation procedure as
for Cl, but now without condition (S6) (classical negation completeness).

**Step 3**: The set T of all disjoint saturated consistent tableaux (with components from
`Subφ`) forms a **Hintikka system** `(T, S)` where `S` is the inclusion order on the
left-tableau components.

**Step 4**: The Hintikka system IS a Kripke model (partial order, persistent valuation,
correct forcing).

**Step 5**: By Proposition 2.31 (Hintikka systems realize formulas), `φ` is refuted at `t₀`,
so `φ ∉ Int`.

### 5.3 Lean Implementation Challenge: Hintikka vs. MCS

The Hintikka-system approach requires defining:
1. A "tableau" type (a pair of sets of formulas `(Γ, Δ)`) — this is a new type not in the
   codebase.
2. Saturation conditions (HS/1, HS/2) — properties of the tableau collection.
3. The canonical Kripke model built from the Hintikka system.

This is **more complex** than the classical MCS approach because it requires building a
structure rather than picking a single MCS.

**Alternative: Prime Filter / Prime Deductively-Closed Theory**

A cleaner formulation (used in many textbooks) avoids tableaux entirely by working with
**prime deductively-closed theories**:

A set `T` of Int-formulas is:
- **Deductively closed**: if `T ⊢_Int φ` then `φ ∈ T`
- **Prime**: if `φ ∨ ψ ∈ T` then `φ ∈ T` or `ψ ∈ T`
- **Consistent**: `⊥ ∉ T`

The canonical model worlds are prime deductively-closed consistent theories. The accessibility
relation is inclusion. This directly generalizes the MCS approach: instead of "MCS = theory
containing φ or ¬φ for all φ", we use "prime theory = theory containing φ or ψ when φ∨ψ ∈ T".

**For the codebase**, this prime-theory approach is probably cleaner because:
1. It uses `Set (PL.Proposition Atom)` as the world type — same as the modal canonical model.
2. The accessibility relation is set inclusion — a partial order automatically.
3. The Lindenbaum-style extension works: every consistent theory extends to a prime
   deductively-closed consistent theory (this is the Int analogue of Lindenbaum's lemma).
4. The truth lemma has the same structure as the classical case.

The key new ingredient is **extending a consistent theory to a prime theory**, which requires
a different Zorn's lemma application than the classical case. The classical Lindenbaum lemma
already exists in `Foundations/Logic/Metalogic/Consistency.lean`. A new `int_lindenbaum`
lemma will be needed that produces prime theories rather than MCS.

### 5.4 Minimal Logic: Same Approach

CZ does not explicitly treat minimal logic (HilbertMin) separately but the same Kripke
semantics applies. The only difference is that the proof system lacks EFQ. The canonical
model construction is identical. The truth lemma for Min works if the canonical worlds are
min-consistent (∅ not Int-derivable but only Min-derivable), which is a weaker condition.

**Uniformity**: a single `int_completeness` parameterized over an axiom predicate with an
explicit callback (analogous to the modal pattern) handles both Int and Min:

```lean
theorem int_completeness {Axioms : PL.Proposition Atom → Prop}
    (h_implyK : ...)  -- Axioms includes implyK
    (h_implyS : ...)  -- Axioms includes implyS
    -- Note: h_efq is OPTIONAL — omit for minimal, include for intuitionistic
    (φ : PL.Proposition Atom)
    (h_valid : IValid φ)
    : Derivable Axioms φ
```

Without EFQ, the proof of classical contradiction (`¬φ → (φ → ⊥) → ... → φ`) breaks, and
the canonical model construction uses a weaker consistency condition. This mirrors how the
modal K completeness differs from S5 completeness.

---

## 6. Gödel Translation Approach: Assessment

CZ Theorem 3.83 states: `φ ∈ Int iff T(φ) ∈ S4`, where `T` is the Gödel translation
(prefix `□` to every subformula and treat classical connectives classically).

Could we derive **Int completeness from S4 completeness** instead of proving it directly?

The approach would be:
1. Define `T : PL.Proposition Atom → Modal.Proposition Atom` (the Gödel translation).
2. Prove `T` embeds Int derivability into S4 derivability:
   `Derivable IntAxiom φ ↔ Derivable S4Axiom (T φ)`
3. Prove `T` preserves Kripke validity in the relevant direction.
4. Use S4 completeness (already in the codebase via `S4Completeness.lean`) to derive Int
   completeness.

**Assessment: NOT recommended for this task.** Reasons:

1. **The codebase already has S4 completeness** (`KCompleteness.lean`, `S4Completeness.lean`).
   The Gödel translation would mean importing this. But the proof of the embedding itself
   requires formalizing the skeleton lemma (CZ Lemma 3.81), which is non-trivial.

2. **The translation loses information about propositional vs. modal formulas**. The Gödel
   translation maps `PL.Proposition` to `Modal.Proposition`. Working out the semantics of
   translated formulas in modal frames, and then translating back to intuitionistic frames,
   requires substantial glue code.

3. **Direct proof is shorter and more transparent**. The Hintikka/prime-theory approach for
   Int completeness is approximately the same length as the S4→Int translation proof.

4. **For minimal logic, the translation approach is less clear**. HilbertMin has no known
   simple modal companion.

5. **Literature fidelity**: CZ Section 2.6 proves Int completeness directly. Section 3.9
   gives the Gödel embedding as a corollary. Following CZ's order means the direct proof is
   the canonical one.

**Verdict**: Use the direct prime-theory Kripke completeness approach for Int and Min.
The Gödel translation can be formalized later as a consequence, not a prerequisite.

---

## 7. Proposed Shared Infrastructure Design

Given all the above, here is the recommended file organization that maximizes reuse across
all three levels:

### Proposed New Files

```
Cslib/Logics/Propositional/
├── Semantics/
│   ├── Basic.lean          -- Valuation, Evaluate, Tautology (classical)
│   └── Kripke.lean         -- IModel, IForces, IValid (intuitionistic/minimal)
└── Metalogic/
    ├── Soundness.lean       -- Classical soundness (pl_soundness, pl_soundness_derivable)
    ├── Completeness.lean    -- Classical completeness (pl_truth_lemma, pl_completeness)
    ├── IntKripke.lean       -- Shared: persistence, IForces properties, int_soundness
    ├── IntLindenbaum.lean   -- int_lindenbaum: consistent theory → prime theory
    ├── IntCompleteness.lean -- Int completeness (int_truth_lemma, int_completeness)
    └── MinCompleteness.lean -- Min completeness (instantiation of int_completeness)
```

### Dependency Graph

```
Semantics/Basic.lean
  └── Metalogic/Soundness.lean
        └── Metalogic/Completeness.lean  (classical)

Semantics/Kripke.lean
  └── Metalogic/IntKripke.lean  (shared persistence + soundness for Int/Min)
        ├── Metalogic/IntLindenbaum.lean  (prime theory extension)
        │     └── Metalogic/IntCompleteness.lean  (Int)
        │           └── Metalogic/MinCompleteness.lean  (Min, by instantiation)
        └── (directly proves min_soundness_derivable)
```

### Shared Components

| Component | Used By |
|-----------|---------|
| `IModel World Atom` | Int, Min |
| `IForces m x φ` | Int, Min |
| `IValid φ` | Int, Min |
| `int_soundness` (parameterized) | Int, Min |
| `int_lindenbaum` (prime theory) | Int, Min |
| `ICanonicalModel Axioms` | Int, Min |
| `int_truth_lemma` (parameterized) | Int, Min |

The only components that differ between Int and Min are the axiom callbacks passed to the
parameterized theorems:
- Int: `h_implyK, h_implyS, h_efq` (three axiom hypotheses)
- Min: `h_implyK, h_implyS` (two axiom hypotheses; EFQ omitted)

This mirrors exactly how the modal code handles K vs. T vs. S4 completeness: same canonical
model, different frame condition proofs.

---

## 8. Key New Ingredients vs. What Already Exists

| Ingredient | Exists? | Source |
|------------|---------|--------|
| `PropSetMaximalConsistent`, `prop_lindenbaum` | Yes | `Metalogic/MCS.lean` |
| `prop_closed_under_derivation`, etc. | Yes | `Metalogic/MCS.lean` |
| `IModel` (intuitionistic Kripke model) | No | New: `Semantics/Kripke.lean` |
| `IForces` (forcing relation) | No | New: `Semantics/Kripke.lean` |
| Persistence lemma for `IForces` | No | New: `Metalogic/IntKripke.lean` |
| `int_soundness` (parameterized, shared) | No | New: `Metalogic/IntKripke.lean` |
| Prime deductively-closed theory definition | No | New: `Metalogic/IntLindenbaum.lean` |
| `int_lindenbaum` (consistent → prime theory) | No | New: `Metalogic/IntLindenbaum.lean` |
| Canonical Kripke model from prime theories | No | New: `Metalogic/IntCompleteness.lean` |
| `int_truth_lemma` (parameterized) | No | New: `Metalogic/IntCompleteness.lean` |
| `int_completeness` (for Int axioms) | No | New: instantiation in IntCompleteness |
| `min_completeness` (for Min axioms) | No | New: thin wrapper in MinCompleteness |
| Gödel translation `T : PL → Modal` | No | Not needed for this task |
| `PropositionalAxiom` with 4 constructors | Yes | `ProofSystem/Axioms.lean` |
| `MinimalAxiom` (implyK + implyS) | No (implicit) | Need new inductive or sub-predicate |
| `IntuitionisticAxiom` (K + S + EFQ) | No (implicit) | Need new inductive or sub-predicate |

### Note on Axiom Types

The current `PropositionalAxiom` has 4 constructors (implyK, implyS, efq, peirce). The modal
pattern uses separate `KAxiom` and `ModalAxiom` inductives. For Int and Min, we need either:
- Separate `IntuitionisticAxiom` (K + S + EFQ) and `MinimalAxiom` (K + S) inductives, or
- Predicates that carve out subsets of `PropositionalAxiom`

The separate-inductive approach is cleaner and mirrors the modal pattern. Estimated ~15 lines
to add to `ProofSystem/Axioms.lean`.

---

## 9. Effort Estimate

| Sub-task | Estimated Lines | Dependencies |
|----------|----------------|--------------|
| Classical: `Semantics/Basic.lean` | ~30 | None |
| Classical: `Metalogic/Soundness.lean` | ~60 | Basic.lean |
| Classical: `Metalogic/Completeness.lean` | ~120 | Soundness.lean, MCS.lean |
| Intuitionistic: `Semantics/Kripke.lean` | ~80 | Propositional/Defs.lean |
| Intuitionistic: `Metalogic/IntKripke.lean` | ~80 | Kripke.lean |
| Intuitionistic: `Metalogic/IntLindenbaum.lean` | ~80 | IntKripke.lean, Consistency.lean |
| Intuitionistic: `Metalogic/IntCompleteness.lean` | ~120 | IntLindenbaum.lean |
| Minimal: `Metalogic/MinCompleteness.lean` | ~30 | IntCompleteness.lean |
| New axiom types (MinimalAxiom, IntAxiom) | ~15 | ProofSystem/Axioms.lean |
| **Total** | **~615 lines** | |

This is approximately 2–2.5x the classical-only estimate from round 1. The bulk of the extra
work is `IntLindenbaum.lean` (new prime theory infrastructure) and `IntCompleteness.lean`
(the truth lemma for the Kripke semantics case, which requires the persistence lemma and
a canonical world extension argument).

---

## 10. Literature Map

| CZ Location | Content | Lean Target |
|-------------|---------|-------------|
| CZ 2.2, p.25–26 | Intuitionistic Kripke frames, valuations, forcing | `Semantics/Kripke.lean` |
| CZ Prop. 2.1, p.27 | Persistence of forcing | Lemma in `IntKripke.lean` |
| CZ 2.6 (Theorem 2.43, proof) | Completeness of Int via Hintikka | `IntCompleteness.lean` |
| CZ Def. 2.30 (Hintikka systems) | The canonical construction | `IntLindenbaum.lean` |
| CZ 2.7 (Theorem 2.47, Glivenko) | Alternative embedding — not needed | Out of scope |
| CZ 3.9 (Theorem 3.83, Gödel T) | Int → S4 embedding — not needed | Out of scope |
| CZ 1.5 / CZ Theorem 1.16 | Classical completeness via MCS | `Completeness.lean` |

---

## 11. Open Design Questions for the Planner

1. **Tableau vs. prime theory approach**: CZ uses Hintikka systems (tableau-based). An
   alternative is prime deductively-closed theories (filter-based). The prime-theory
   approach fits more naturally with the existing MCS infrastructure. **Recommendation**:
   use prime theories.

2. **Separate inductive types vs. sub-predicates**: For `MinimalAxiom` and `IntAxiom`,
   should we create new `inductive` types (like `KAxiom`, `ModalAxiom`) or sub-predicates
   of `PropositionalAxiom`? Separate inductives are cleaner for the parameterized soundness
   callback. **Recommendation**: separate inductives.

3. **File for `MinimalAxiom` / `IntAxiom`**: Should these go in `ProofSystem/Axioms.lean`
   (alongside existing `PropositionalAxiom`) or in new files? **Recommendation**: add to
   existing `ProofSystem/Axioms.lean` to keep axiom definitions together.

4. **Conjunction and disjunction in forcing**: CZ uses `∧` and `∨` in the intuitionistic
   formula language, but `PL.Proposition` only has `bot` and `imp` as primitives. Conjunction
   and disjunction are derived: `φ ∧ ψ := ¬(φ → ¬ψ)` and `φ ∨ ψ := ¬φ → ψ`. The forcing
   relation should be defined on the underlying `bot/imp` primitives. This matters because CZ
   uses `∨` in the statement of primeness. With the `bot/imp`-only language, prime theories
   are defined differently (no disjunction property needed). **Action**: Clarify with the
   implementer whether `PL.Proposition` is `bot/imp`-only or has `∧∨`. Checking `Defs.lean`:
   yes, `PL.Proposition` has only `atom | bot | imp`. Conjunction/disjunction/negation are
   `abbrev`s. The IForces relation has only three cases. This simplifies the forcing relation
   but means the CZ disjunction-property definition of "prime" does not directly apply in
   this primitive language — primeness must be reformulated in terms of `imp`/`bot`.

---

## References

- CZ Section 2.2 (pages 25–27): Intuitionistic Kripke frames, models, forcing
  (`specs/literature/modal_logic.md`, lines 1564–1642)
- CZ Section 2.6 (pages 45–46): Completeness of Int (Theorem 2.43)
  (`specs/literature/modal_logic.md`, lines 2353–2412)
- CZ Section 2.7 (pages 46–48): Glivenko's theorem and Gödel embedding
  (`specs/literature/modal_logic.md`, lines 2413–2510)
- CZ Section 3.9 (pages 96–98): Gödel translation T : Int → S4
  (`specs/literature/modal_logic.md`, lines 4437–4507)
- CZ Definition 2.30 (page 35): Hintikka systems
  (`specs/literature/modal_logic.md`, lines 2049–2070)
- `Cslib/Logics/Modal/Basic.lean`: Modal `Model` structure (reuse reference)
- `Cslib/Logics/Modal/Metalogic/Soundness.lean`: Parameterized soundness pattern to adapt
- `Cslib/Logics/Modal/Metalogic/KCompleteness.lean`: Canonical model pattern (lines 168–323)
- `Cslib/Foundations/Logic/Metalogic/Consistency.lean`: Generic MCS / Lindenbaum
