# Teammate A Findings (Round 2): Primary Implementation Research

**Task**: 112 — Establish soundness and completeness for propositional Hilbert proof systems
**Teammate**: A (Primary Angle — Working through exact proof steps for all three levels)
**Date**: 2026-06-10
**Round**: 2 (building on Round 1, consulting new literature and codebase)

---

## Key Findings

### 1. Confirmed Scope: Three Distinct Proof Structures

All three levels require fundamentally different semantic infrastructure:

| Level | Tag | Axioms | Semantics | Complexity |
|-------|-----|--------|-----------|------------|
| Classical | `HilbertCl` | K, S, EFQ, Peirce | Bivalent valuations `Atom → Prop` | Low (~280 lines, 3 files) |
| Intuitionistic | `HilbertInt` | K, S, EFQ | Kripke frames (partial orders) | High (~400 lines, 4-5 files) |
| Minimal | `HilbertMin` | K, S | Kripke frames (no EFQ) | Medium (~100 extra lines, shares Int infra) |

The classical case is a direct reduction of the modal K case. The intuitionistic and minimal cases require a completely new Kripke semantic infrastructure that does NOT yet exist in the codebase.

### 2. Critical Missing Infrastructure: HilbertMin and HilbertInt Have No Instances

A crucial gap discovered during this research round: the tag types `Propositional.HilbertMin` and `Propositional.HilbertInt` are defined in `ProofSystem.lean` (lines 367-371) but have **zero instance registrations** anywhere in the codebase. Specifically:

- `HilbertCl` has instances for `InferenceSystem`, `ModusPonens`, `HasAxiomImplyK`, `HasAxiomImplyS`, `HasAxiomEFQ`, `HasAxiomPeirce`, and `ClassicalHilbert` in `Instances.lean`
- `HilbertMin` and `HilbertInt` have **no instances at all**

This means soundness/completeness for intuitionistic and minimal levels requires:
1. Creating `MinimalPropAxiom` / `IntuitionisticPropAxiom` inductive types (subsets of `PropositionalAxiom`)
2. Creating `DerivationTree` variants (or reusing the existing one with restricted axiom predicate)
3. Registering all `InferenceSystem`, `ModusPonens`, axiom, and bundled class instances
4. Building the Kripke semantic layer
5. Proving soundness and completeness

OR, alternatively, using the parameterized approach already employed by the modal system:
- The existing `DerivationTree` in `Derivation.lean` is parameterized: it works with any axiom predicate
- The current `PropositionalAxiom` is a concrete inductive type with all 4 constructors
- For Int/Min, we can define `MinPropAxiom φ := φ = implyK ... ∨ φ = implyS ...` etc. as predicates (not new inductives)
- This follows exactly how modal logic K, T, D, S4, S5 share the same `DerivationTree` infrastructure

The modal pattern from `ProofSystem/Instances.lean` (modal side) shows each logic registers its own `InferenceSystem` instance against a specific axiom set.

### 3. Classical Completeness: Exact Proof Steps

**CZ Chapter 1, Theorem 1.16 proof structure** (from direct reading of `modal_logic.md`):

**Soundness** (lines 1147-1148 of modal_logic.md):
- Verify each of the 4 axiom schemata is valid (K, S, EFQ, Peirce are all semantic tautologies)
- Verify MP preserves validity (trivial)
- This is `prop_axiom_sound : PropositionalAxiom φ → Tautology φ`

**Completeness** (lines 1149-1179 of modal_logic.md):
The CZ proof uses "tableaux" which are pairs (Γ, Δ) — exactly our MCS framework where Γ = set of "true" formulas and Δ = set of "false" formulas. CZ's "consistent tableau" = our `PropSetConsistent`.

CZ Theorem 1.16 completeness:
1. Assume `not (Derivable φ)` (CZ: ` ⊬ φ`)
2. The tableau `(∅, {φ})` is consistent (since φ is not derivable, `¬φ` is consistent)
3. Extend to a saturated (= maximal) consistent tableau using Lindenbaum = `prop_lindenbaum`
4. The saturated tableau gives a canonical valuation `v(p) := (atom p ∈ M)`
5. Truth Lemma: `v ⊨ φ ↔ φ ∈ M` (by induction on formula structure)
6. Since `¬φ ∈ M`, we get `v ⊭ φ`, contradicting `Tautology φ`

The Truth Lemma for the classical case:
- `atom p` case: by definition of canonical valuation (trivial)
- `bot` case: uses `prop_mcs_bot_not_mem` (bot never in MCS)
- `imp φ ψ` case: the hard case. Follows KCompleteness.lean lines 183-248 exactly, using:
  - `prop_implication_property` (if `φ→ψ ∈ M` and `φ ∈ M` then `ψ ∈ M`)
  - `prop_negation_complete` (either `φ ∈ M` or `¬φ ∈ M`)
  - `prop_mcs_neg_of_not_mem` (if `φ ∉ M` then `¬φ ∈ M`)
  - Inline derivation tree construction to get the `(φ→ψ).neg ∈ M` contradiction case

The `imp` case of the Truth Lemma is the only technically hard step. The exact pattern from `KCompleteness.lean` lines 193-248 (the `| .imp φ ψ =>` case of `k_truth_lemma`) transfers verbatim with two changes:
1. Remove the `h_K`, `h_implyK`, `h_implyS`, `h_efq`, `h_peirce` parameters (use `propDerivationSystem` directly)
2. Use `prop_closed_under_derivation` instead of `modal_closed_under_derivation`
3. Use `prop_implication_property` instead of `modal_implication_property`
4. NO `.box` case

**Estimated size for classical layer:**
- `Cslib/Logics/Propositional/Semantics/Basic.lean`: ~50 lines (definitions only)
- `Cslib/Logics/Propositional/Metalogic/Soundness.lean`: ~70 lines
- `Cslib/Logics/Propositional/Metalogic/Completeness.lean`: ~130 lines
- Total: ~250 lines

### 4. Intuitionistic Completeness: Proof Structure from CZ Chapter 2

**CZ Chapter 2, Theorem 2.43 proof structure** (from direct reading of `modal_logic.md`, lines 2353-2404):

CZ proves intuitionistic soundness/completeness using **Hintikka systems**, not MCS. This is fundamentally different from the classical case.

**Key semantic definitions required (CZ Section 2.2, lines 1564-1626 of modal_logic.md):**

An intuitionistic Kripke frame is `(W, R)` where R is a **partial order** (reflexive, transitive, antisymmetric).

A valuation is a map `v : Atom → Set W` (upward closed sets of worlds), not just `Atom → Prop`.

The forcing relation:
- `(M, x) ⊩ atom p ↔ x ∈ v(p)`
- `(M, x) ⊩ ⊥` never (⊥ is false everywhere)
- `(M, x) ⊩ φ → ψ ↔ ∀ y ≥ x. (M, y) ⊩ φ → (M, y) ⊩ ψ`

**Persistence (CZ Proposition 2.1):** if `x ⊩ φ` and `xRy` then `y ⊩ φ` — this must be proved by structural induction on formulas.

**A Hintikka system** (CZ Section 2.4, lines 2049-2088) is a pair `(T, S)` where:
- T = non-empty set of disjoint saturated tableaux
- S = partial order on T
- (HS/1): if `tSt'` then `Γ(t) ⊆ Γ(t')`  (formulas at t persist to t')
- (HS/2): if `φ → ψ ∈ Δ(t)` (right part of t), then there exists t' with `tSt'`, `φ ∈ Γ(t')`, `ψ ∈ Δ(t')`

CZ Theorem 2.43 completeness (lines 2383-2404):
1. Assume `¬(⊢_Int φ)` 
2. Tableau `(∅, {φ})` is consistent in Int
3. Use saturation rules (same as classical S1-S5, but NOT S6 since Peirce is absent) to build tableaux
4. Key insight: the set T of ALL disjoint saturated consistent tableaux with `Γ∪Δ = Sub(φ)` forms a Hintikka system
5. The partial order is `tSt' ↔ Γ(t) ⊆ Γ(t')` (information growth)
6. The hard condition is (HS/2): given `φ→ψ ∈ Δ(t)`, construct t' by extending `(Γ(t)∪{φ}, {ψ})` to a maximal saturated consistent tableau

**What this means for Lean implementation:** The canonical model for intuitionistic logic is NOT a single world (as in classical) but a **Kripke frame** whose worlds are themselves (equivalents of) consistent sets. The completeness proof constructs a Kripke model whose worlds are saturated consistent tableaux ordered by inclusion.

This is analogous to the modal canonical model `CanonicalWorld` in `Completeness.lean`, but with a crucial difference: the accessibility relation is `⊆` (set inclusion / information growth), NOT the modal `boxPsi ∈ S → psi ∈ T` relation.

### 5. Reuse Analysis: Modal Infrastructure vs. New Kripke Infrastructure

**CAN reuse (modal side):**
- The `propDerivationSystem` (already exists)
- `prop_lindenbaum`, MCS infrastructure (already exists)
- The generic pattern of parameterized axiom predicates

**CANNOT reuse (need new propositional-specific infrastructure):**
- The modal `Model` structure has `r : World → World → Prop` and `v : World → Atom → Prop`
- Intuitionistic semantics needs `r : World → World → Prop` (partial order) and `v : World → Atom → Prop` (persistent)
- These could use the same `Model` structure, but:
  1. The `Satisfies` function must be different — for intuitionistic logic, `φ → ψ` forcing is `∀ y. wRy → (y ⊩ φ → y ⊩ ψ)` not `w ⊩ φ → w ⊩ ψ`
  2. The canonical model construction is fundamentally different
  3. The Truth Lemma proof structure is fundamentally different

**DECISION:** The intuitionistic semantics should be defined in a NEW file, not reuse `Modal/Basic.lean`. The `Satisfies` function for propositional Kripke semantics is different enough (no box operator, different implication forcing) that mixing them would create confusion.

### 6. What the Intuitionistic Canonical Model Looks Like in Lean

Based on CZ's construction, the canonical model for intuitionistic completeness is:

```lean
-- World = saturated consistent propositional tableau
-- (represented as a subtype of Set (Proposition Atom))
def IPLWorld := { S : Set (PL.Proposition Atom) // SaturatedConsistent S }

-- Accessibility = set inclusion
def ipl_r (w w' : IPLWorld) : Prop := w.val ⊆ w'.val

-- Valuation = upward closed (by definition of ≤ on worlds)
def ipl_v (w : IPLWorld) (p : Atom) : Prop := PL.Proposition.atom p ∈ w.val

-- Forcing relation (different from modal Satisfies!)
def IForces (w : IPLWorld) : PL.Proposition Atom → Prop
  | .atom p => ipl_v w p
  | .bot => False
  | .imp φ ψ => ∀ w', ipl_r w w' → IForces w' φ → IForces w' ψ
```

The Truth Lemma then states:
```lean
theorem ipl_truth_lemma (w : IPLWorld) (φ : PL.Proposition Atom) :
    IForces w φ ↔ φ ∈ w.val
```

The `imp` case of this Truth Lemma is the hard case:
- Forward: If `IForces w (φ→ψ)`, show `φ→ψ ∈ w`. Use negation: if `φ→ψ ∉ w`, then by CZ condition (HS/2), there exists `w' ≥ w` with `φ ∈ w'` and `ψ ∉ w'`. Apply `IForces w' φ` (by IH) and `IForces w (φ→ψ)` (with `wRw'`) to get `IForces w' ψ`, then by IH get `ψ ∈ w'`, contradiction.
- Backward: If `φ→ψ ∈ w`, show `IForces w (φ→ψ)`. For any `w' ≥ w` with `IForces w' φ`, by IH `φ ∈ w'`. By persistence of `φ→ψ` (condition HS/1), `φ→ψ ∈ w'`. By implication property of w', `ψ ∈ w'`. By IH, `IForces w' ψ`.

**Key challenge**: Building the set of "saturated consistent tableaux" is more complex than building a single MCS. Specifically, for condition (HS/2), we need: given a tableau (Γ, Δ) and `φ→ψ ∈ Δ`, show the tableau `(Γ∪{φ}, {ψ})` is consistent, then extend it. The consistency proof requires showing `Γ,φ ⊬_Int ψ` — which follows from `⊬_Int φ→ψ` by the deduction theorem.

### 7. Minimal Logic: What Changes from Intuitionistic

**Minimal logic (`HilbertMin`)** uses only axioms K and S — it removes both EFQ and Peirce. Its semantics is Kripke semantics on partial orders exactly as for intuitionistic, BUT:

- The canonical model construction does NOT need `prop_mcs_bot_not_mem` (which uses EFQ)
- The `bot` case of the Truth Lemma is different: in minimal logic, `⊥` can be true at some worlds (it's not forced to be false)
- The forcing relation for `⊥` is simply the valuation: `w ⊩ ⊥ ↔ ⊥ ∈ w` (and `⊥` may or may not be in a world)
- The accessibility relation and frame conditions are the same partial order

This means:
1. Minimal and intuitionistic Kripke semantics share the SAME model structure (partial order + upward closed valuation)
2. They differ only in which axioms are sound — Peirce fails in both, EFQ fails in minimal
3. The canonical model construction for minimal is simpler (fewer properties required of worlds)

### 8. Exact Obstacles and Hard Steps

**Classical (Low difficulty):**
- Hard step: `imp` case of Truth Lemma (inline derivation tree construction)
- Pattern: Directly from `KCompleteness.lean` lines 193-248
- Risk: Low — mechanical transcription from modal proof

**Intuitionistic (High difficulty):**
1. Defining "SaturatedConsistent" (Int version): needs saturation conditions S1-S5 but NOT S6 (no Peirce)
2. Showing the set of all Int-saturated-consistent tableaux is non-empty (for the canonical model worlds)
3. Showing condition (HS/2): given `φ→ψ ∉ w` (inconsistent case), constructing the extension — needs that `(Γ(w)∪{φ}, {ψ})` is Int-consistent, then Lindenbaum gives the world `w'`
4. Persistence lemma: by structural induction on formula, showing `w ⊩ φ` and `wRw'` implies `w' ⊩ φ` — this requires the `imp` case, which uses the fact that `w ⊩ φ→ψ` means "for all successors", so persistence follows from transitivity of R
5. The Truth Lemma `imp` case requires both (HS/1) and (HS/2) and the deduction theorem
6. The completeness theorem: assume `¬(⊢_Int φ)`, show the canonical Kripke model falsifies `φ` — uses `(∅, {φ})` is consistent and belongs to the canonical model

**Minimal (Medium difficulty):**
- Shares all intuitionistic infrastructure
- Simplified `bot` case (no `prop_mcs_bot_not_mem` needed)
- Soundness: EFQ axiom case is removed; Peirce case removed
- New challenge: Verifying Peirce axiom fails in minimal Kripke models (need countermodel)

### 9. Prerequisite: New Axiom Predicates

The codebase currently has ONE axiom type `PropositionalAxiom` with ALL 4 constructors. For Int and Min, we need axiom predicates (analogous to `KAxiom`, `S4Axiom`, etc. in the modal case):

```lean
-- For HilbertMin: only K and S
inductive MinPropAxiom : PL.Proposition Atom → Prop where
  | implyK (φ ψ) : MinPropAxiom (φ.imp (ψ.imp φ))
  | implyS (φ ψ χ) : MinPropAxiom ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ)))

-- For HilbertInt: K, S, EFQ  
inductive IntPropAxiom : PL.Proposition Atom → Prop where
  | implyK (φ ψ) : IntPropAxiom (φ.imp (ψ.imp φ))
  | implyS (φ ψ χ) : IntPropAxiom ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ)))
  | efq (φ) : IntPropAxiom (Proposition.bot.imp φ)
```

The existing `propDerivationSystem` is built on `PropositionalAxiom`. For Int and Min, we need separate `intDerivationSystem` and `minDerivationSystem` using the new axiom predicates.

Alternatively: use the SAME `DerivationTree` type with DIFFERENT axiom predicates (exactly as modal logic does with `KAxiom`, `TAxiom`, `S4Axiom`).

Critically, the generic deduction theorem in `DeductionTheorem.lean` uses only K and S axioms — it's compatible with all three levels.

### 10. File Layout Recommendation

Based on careful analysis, the recommended file layout mirrors the modal pattern:

**Phase 1 (Classical, ~280 lines, 3 files):**
```
Cslib/Logics/Propositional/Semantics/Basic.lean   -- Valuation, Evaluate, Tautology
Cslib/Logics/Propositional/Metalogic/Soundness.lean  -- prop_axiom_sound, prop_soundness
Cslib/Logics/Propositional/Metalogic/Completeness.lean -- canonicalValuation, truth_lemma, completeness
```

**Phase 2 (Intuitionistic/Minimal infrastructure, ~300 lines, 3 files):**
```
Cslib/Logics/Propositional/ProofSystem/IntMin.lean  -- IntPropAxiom, MinPropAxiom, intDerivationSystem, minDerivationSystem + instances for HilbertInt/HilbertMin
Cslib/Logics/Propositional/Semantics/Kripke.lean    -- IPLModel, IForces (intuitionistic forcing), persistence
Cslib/Logics/Propositional/Metalogic/IntSaturated.lean -- SaturatedConsistentInt, Lindenbaum-style construction, HS/2 existence property
```

**Phase 3 (Intuitionistic soundness/completeness, ~250 lines, 2 files):**
```
Cslib/Logics/Propositional/Metalogic/IntSoundness.lean  -- int_axiom_sound, int_soundness
Cslib/Logics/Propositional/Metalogic/IntCompleteness.lean -- IPLCanonicalWorld, IPLCanonicalModel, ipl_truth_lemma, int_completeness
```

**Phase 4 (Minimal soundness/completeness, ~150 lines, 2 files):**
```
Cslib/Logics/Propositional/Metalogic/MinSoundness.lean  -- min_axiom_sound, min_soundness
Cslib/Logics/Propositional/Metalogic/MinCompleteness.lean -- min_completeness (reuses IPL canonical model)
```

---

## Recommended Approach

### Priority: Start with Classical

The classical case is a near-verbatim simplification of the modal K proof. It should be implemented first to establish the pattern and verify the approach works before tackling the more complex intuitionistic/minimal cases.

**Critical insight for classical completeness**: The existing codebase has everything needed. The modal `KCompleteness.lean` proof of `k_truth_lemma` (lines 168-261) can be directly translated to propositional logic by:
1. Removing the `h_K`, `h_implyK`, `h_implyS`, `h_efq`, `h_peirce` parameters (use propositional-specific APIs)
2. Removing the `.box` case entirely
3. Replacing `CanonicalWorld/CanonicalModel` with `PropCanonicalWorld/PropCanonicalValuation`
4. Replacing `modal_*` lemma names with `prop_*` equivalents

### For Intuitionistic/Minimal: New Infrastructure Required

The intuitionistic case requires fundamentally new infrastructure. The CZ Hintikka system approach translates to Lean as follows:

**The canonical model worlds** are equivalents of `PropSetMaximalConsistent` sets, but with a DIFFERENT order (set inclusion, not bare set equality). This is a crucial architectural difference from the classical case.

For the intuitionistic canonical model, we should define:
```lean
-- A "canonical world" for intuitionistic logic is a set S that is:
-- (1) Int-consistent (does not derive bot from any finite subset)
-- (2) "Int-saturated" (closed under S1-S5, which are the non-Peirce rules)
-- This is weaker than MCS — the set is not necessarily maximal!
def IPLWorld := { S : Set (PL.Proposition Atom) // IntSaturatedConsistent S }
```

Alternatively, and more elegantly, the "worlds" can be full MCS for the intuitionistic logic (using `intDerivationSystem`). Under the intuitionistic MCS approach:
- Worlds = MCS of Int
- `wRw'` iff `w ⊆ w'` (information growth)
- Persistence follows from this definition
- The Truth Lemma for `imp` uses: `φ→ψ ∈ w` iff for all Int-MCS `w' ⊇ w`, if `φ ∈ w'` then `ψ ∈ w'`

This is essentially a different version of CZ's construction. The MCS-based approach is cleaner for Lean formalization and more consistent with the existing modal infrastructure.

---

## Evidence and Examples

### Classical Truth Lemma (`imp` case) — direct template

The relevant code from `KCompleteness.lean` (lines 193-248) translates as:
```lean
| .imp φ ψ => by
  constructor
  · intro h_sat
    -- h_sat : Evaluate (canonicalValuation M) (φ.imp ψ)
    -- Goal: φ.imp ψ ∈ M.val
    rcases prop_negation_complete M.property (φ.imp ψ) with h | h
    · exact h
    · exfalso
      -- h : (φ.imp ψ).neg ∈ M.val i.e. (φ→ψ)→⊥ ∈ M
      -- Show φ ∈ M by deriving φ from context {(φ→ψ)→⊥}:
      have h_phi_M : φ ∈ M.val := by
        apply prop_closed_under_derivation M.property
          (L := [(φ.imp ψ).imp .bot])
          (fun x hx => by simp [List.mem_cons] at hx; exact hx ▸ h)
        -- [Inline derivation tree construction -- identical to KCompleteness.lean lines 202-217]
        ...
      -- Apply truth lemma IH to get v ⊨ φ
      -- Apply h_sat to get v ⊨ ψ
      -- Apply truth lemma IH to get ψ ∈ M
      -- Derive contradiction with h : (φ→ψ)→⊥ ∈ M
      ...
  · intro h_mem h_sat_phi
    -- h_mem : φ.imp ψ ∈ M.val
    -- h_sat_phi : Evaluate (canonicalValuation M) φ
    -- Goal: Evaluate (canonicalValuation M) ψ
    exact (prop_truth_lemma M ψ).mpr
      (prop_implication_property M.property h_mem
        ((prop_truth_lemma M φ).mp h_sat_phi))
```

### Intuitionistic Semantics (`IForces`) — new definition needed

```lean
def IForces (m : IPLModel) : m.World → PL.Proposition Atom → Prop
  | w, .atom p => m.v w p
  | _, .bot => False
  | w, .imp φ ψ => ∀ w', m.r w w' → IForces m w' φ → IForces m w' ψ

-- Persistence: if w ⊩ φ and wRw' then w' ⊩ φ
theorem iforces_persistent (m : IPLModel) (h_refl : ∀ w, m.r w w)
    (h_trans : ∀ w w' w'', m.r w w' → m.r w' w'' → m.r w w'')
    {φ : PL.Proposition Atom} {w w' : m.World}
    (h_sat : IForces m w φ) (h_r : m.r w w') : IForces m w' φ := by
  induction φ with
  | atom p => exact m.v_persistent h_r h_sat  -- needs persistence axiom on model
  | bot => exact absurd h_sat id
  | imp φ ψ ih_φ ih_ψ =>
    intro w'' h_r' h_sat_φ
    exact h_sat w'' (h_trans w' w'' ... h_r h_r') h_sat_φ  -- transitivity
```

---

## Confidence Level

**Classical level**: Very high confidence. The proof is mechanical and all infrastructure exists. The only possible surprises are minor naming/type issues in the Lean translation.

**Intuitionistic level**: High confidence in the approach (CZ is authoritative), medium confidence in the Lean implementation details. The main risk is the `imp` case of the Truth Lemma under the MCS-based canonical model — specifically, showing that for an Int-MCS `w`, the set `{w' : Int-MCS | w ⊆ w'}` provides the right witness for (HS/2).

**Minimal level**: High confidence (shares structure with intuitionistic; simpler in some ways).

**Implementation risk**: The intuitionistic canonical model construction requires careful handling of:
1. Whether worlds are "all Int-MCS" or "all Int-saturated-consistent sets"
2. Whether the partial order is strict or non-strict inclusion
3. How persistence of atoms is established (needs explicit monotonicity condition on the valuation in IPLModel)

---

## Literature Proof Structure

### Source: CZ Chapter 1 (Classical)

**Source**: Chagrov & Zakharyaschev, *Modal Logic* (1997), Chapter 1, Theorem 1.16
**Strategy**: MCS canonical construction (Henkin-style)

#### Step Map
1. Define bivalent valuation `v : Atom → Prop` -- `Semantics/Basic.lean`
2. Define evaluation `Evaluate v : Proposition → Prop` -- `Semantics/Basic.lean`
3. Define `Tautology φ = ∀ v, Evaluate v φ` -- `Semantics/Basic.lean`
4. Prove each axiom is a tautology -- `Metalogic/Soundness.lean` (prop_axiom_sound)
5. Prove soundness by induction on DerivationTree -- `Metalogic/Soundness.lean` (prop_soundness)
6. Define canonical valuation `v_M(p) = (atom p ∈ M)` -- `Metalogic/Completeness.lean`
7. Prove Truth Lemma: `Evaluate v_M φ ↔ φ ∈ M` -- `Metalogic/Completeness.lean` (prop_truth_lemma)
8. Prove completeness: Tautology φ → Derivable φ -- `Metalogic/Completeness.lean` (prop_completeness)

#### Dependencies
- Step 7 depends on Steps 1-2 (Evaluate defined), Step 6 (canonical valuation), MCS.lean (all prop_mcs_* lemmas)
- Step 8 depends on Step 7, prop_lindenbaum, prop_soundness (for consistency proof)
- Step 5 depends on Steps 1-4

#### Potential Formalization Challenges
- Step 7, `imp` case: Requires inline derivation tree constructions (pattern from KCompleteness.lean lines 193-248)
- Step 8: Consistency of `{¬φ}` requires soundness — create a cycle-free argument using contrapositive

### Source: CZ Chapter 2 (Intuitionistic)

**Source**: Chagrov & Zakharyaschev, *Modal Logic* (1997), Chapter 2, Sections 2.2 and 2.6, Theorem 2.43
**Strategy**: Hintikka system / Kripke canonical model construction

#### Step Map
1. Define intuitionistic Kripke frame (W, R) with R a partial order -- `Semantics/Kripke.lean`
2. Define intuitionistic forcing `IForces` with universal quantifier in `imp` case -- `Semantics/Kripke.lean`
3. Define `IPLValidity φ = ∀ (W, R, v), ∀ w, IForces w φ` -- `Semantics/Kripke.lean`
4. Prove persistence (Proposition 2.1): `w ⊩ φ ∧ wRw' → w' ⊩ φ` -- `Semantics/Kripke.lean`
5. Prove each Int axiom (K, S, EFQ) is IPL-valid -- `Metalogic/IntSoundness.lean`
6. Prove Peirce is NOT IPL-valid (countermodel with 2-world frame) -- optional theorem
7. Prove int_soundness by induction on DerivationTree for IntPropAxiom -- `Metalogic/IntSoundness.lean`
8. Define IntSaturatedConsistent / IPLWorld for canonical model -- `Metalogic/IntSaturated.lean`
9. Prove condition (HS/2): existence of successor world -- `Metalogic/IntSaturated.lean`
10. Define canonical IPL model (IPLCanonicalModel) -- `Metalogic/IntCompleteness.lean`
11. Prove IPL Truth Lemma: `IForces w φ ↔ φ ∈ w` -- `Metalogic/IntCompleteness.lean`
12. Prove int_completeness: IPLValidity φ → Derivable IntPropAxiom φ -- `Metalogic/IntCompleteness.lean`

#### Dependencies
- Step 4 depends on Steps 1-3 (forcing defined)
- Steps 5-7 depend on Steps 1-4
- Step 9 depends on the deduction theorem for Int (inherits from existing `prop_has_deduction_theorem` using only K+S axioms — compatible!)
- Step 11 depends on Steps 8-10 and the Truth Lemma for Int-MCS properties
- Step 12 depends on Step 11 and Steps 5-7

#### Potential Formalization Challenges
- Step 4 (`imp` case of persistence): Subtle — requires transitivity of R to push the universal quantifier in `IForces` forward
- Step 9 (HS/2): Need to show `(Γ(w)∪{φ}, {ψ})` is Int-consistent; requires the deduction theorem
- Step 11 (`imp` case): The hardest step. Forward direction requires constructing a successor world using Step 9. Backward direction uses persistence (Step 4) and implication property of the Int-MCS.
- Step 12: The canonical model refutes `¬φ` at the "empty set" world (or root world); requires that `∅` is an Int-consistent set and can be extended to an IPLWorld

### Note on Minimal Logic

Minimal logic (HilbertMin, axioms K and S only) uses the same Kripke semantics as intuitionistic but with:
- `bot` case: `IForces_Min w ⊥ := ⊥ ∈ w` (treated as an atomic proposition, not forced false)
- All infrastructure from the intuitionistic case reuses directly
- Soundness: EFQ case removed from axiom soundness check
- Completeness: Identical construction, simpler bot handling

The minimal canonical model construction is technically simpler because we don't need `prop_mcs_bot_not_mem` (which requires EFQ).
