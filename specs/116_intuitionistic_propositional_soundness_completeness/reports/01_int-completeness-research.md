# Research Report: Intuitionistic Propositional Soundness and Completeness

**Task**: 116
**Status**: Research complete
**Date**: 2026-06-11

## Literature Proof Structure

**Source**: Chagrov & Zakharyaschev, "Modal Logic" (CZ), Sections 2.2, 2.6, 5.1
**Strategy**: Henkin-style canonical model construction adapted for intuitionistic logic

### Step Map

1. **Soundness** (CZ Theorem 2.43, => direction) -- Verify each IntPropAxiom is valid in all intuitionistic Kripke frames
2. **Deduction Theorem** (CZ Theorem 2.42) -- Already completed in task 113 (`deductionTheorem`, `prop_has_deduction_theorem`)
3. **Prime Theory Definition** -- Define "prime deductively-closed consistent theory" (CZ's maximal L-consistent tableaux for Int)
4. **Lindenbaum for Prime Theories** (CZ Lemma 5.1 / Theorem 2.43 completeness direction) -- Every consistent set extends to a prime theory
5. **Canonical Kripke Model** (CZ Section 5.1) -- Worlds = prime theories, accessibility = set inclusion, valuation = atom membership
6. **Truth Lemma** (CZ Theorem 5.4 / Theorem 2.43) -- `IForces v bot_forces w phi <-> phi in w` for canonical model
7. **Completeness** (CZ Theorem 2.43, <= direction) -- If `IValid phi` then `Derivable IntPropAxiom phi`

### Dependencies

- Step 2 is already done (task 113)
- Step 4 depends on Step 3
- Step 5 depends on Step 3
- Step 6 depends on Steps 4 and 5
- Step 7 depends on Steps 1 and 6

### Potential Formalization Challenges

- **Step 3**: Encoding the prime/disjunction property in the imp/bot language (no primitive disjunction)
- **Step 4**: The Lindenbaum lemma for prime theories uses the same Zorn pattern but requires proving a stronger condition than plain MCS
- **Step 6 (imp case)**: The forward direction `IForces ... w (phi.imp psi) -> (phi.imp psi) in w` is harder than classical because we cannot use Peirce's law; we must work purely intuitionistically

---

## Research Question 1: What is a "Prime Theory" in the imp/bot Language?

### CZ's Approach (Tableaux)

In CZ, a "maximal L-consistent tableau" for `L in ExtInt` is a pair `(Gamma, Delta)` where:
- `Gamma ∪ Delta` = all formulas
- `Gamma` does not derive any disjunction of formulas in `Delta`

The key property (CZ's Hintikka system condition HS/2) is:
> If `psi -> chi in Delta`, then there exists a successor tableau `t'` with `Gamma ⊆ Gamma'`, `psi in Gamma'`, and `chi in Delta'`.

### Translation to Set-Based Approach

In our formalization, we work with sets of formulas (not tableau pairs). The CZ tableau `t = (Gamma, Delta)` corresponds to a set `Gamma` where `Delta = Gamma^c` (complement). The relevant properties for `Gamma` are:

1. **Deductively closed**: If `L ⊆ Gamma` and `L ⊢_Int phi`, then `phi in Gamma`
2. **Consistent**: `bot ∉ Gamma` (equivalently, `Gamma ⊬_Int bot`)
3. **Prime** (disjunction property): For all `phi, psi`: if `(phi → psi) ∉ Gamma`, then there exists a prime theory `Gamma' ⊇ Gamma` with `phi ∈ Gamma'` and `psi ∉ Gamma'`

Property 3 is what distinguishes prime theories from MCS. In classical logic, MCS gives you `phi in S ∨ neg phi in S` for all formulas, which is equivalent to primeness + decidability of membership. But in intuitionistic logic, we need the weaker but more structural condition.

### Recommended Lean Definition

```lean
/-- A prime intuitionistic theory is a set that is:
(1) deductively closed w.r.t. IntPropAxiom,
(2) consistent (does not derive bot), and
(3) prime: if `phi.imp psi ∉ S`, then there exists a prime theory
    `T ⊇ S` with `phi ∈ T` and `psi ∉ T`.

This corresponds to CZ's "maximal Int-consistent tableaux" in set form. -/
structure IntPrimeTheory (Atom : Type*) where
  carrier : Set (PL.Proposition Atom)
  consistent : PropSetConsistent IntPropAxiom carrier
  closed : ∀ (L : List (PL.Proposition Atom)),
    (∀ x ∈ L, x ∈ carrier) →
    ∀ φ, (propDerivationSystem IntPropAxiom).Deriv L φ → φ ∈ carrier
  prime : ∀ (φ ψ : PL.Proposition Atom),
    Proposition.imp φ ψ ∉ carrier →
    ∃ T : IntPrimeTheory Atom,
      carrier ⊆ T.carrier ∧ φ ∈ T.carrier ∧ ψ ∉ T.carrier
```

**HOWEVER**, this definition is circular (IntPrimeTheory references itself in the `prime` field). We need a non-circular alternative.

### Alternative 1: MCS-based approach (RECOMMENDED)

The key insight is that **MCS for IntPropAxiom already gives us everything we need for the intuitionistic truth lemma**, but the imp case of the truth lemma works differently than in the classical case. The intuitionistic MCS has:

- `phi in S ∨ (phi → bot) in S` for every `phi` (negation completeness from generic MCS)
- `phi → psi in S ∧ phi in S → psi in S` (implication property)
- Deductive closure

The critical difference from classical completeness is **not** in the definition of worlds, but in **how the truth lemma's forward direction for imp works**. In the classical truth lemma for `phi → psi`, when `neg(phi → psi) in S`, we derive `phi in S` using Peirce's law. Without Peirce's law, we need a different argument.

**The solution**: MCS for IntPropAxiom (without Peirce) still gives negation completeness: `phi in S` or `phi → bot in S`. The imp case of the truth lemma works by:
- Backward: `(phi → psi) in S → IForces ... S phi → IForces ... S psi` -- works by going to any successor `T ⊇ S`, using that `(phi → psi) in T` (by deductive closure from `(phi → psi) in S`) and applying MP.
- Forward: `IForces ... S (phi.imp psi) → (phi.imp psi) in S` -- by contrapositive: assume `(phi → psi) ∉ S`. Then we find an MCS `T ⊇ S ∪ {phi}` with `psi ∉ T`. This gives `IForces ... T phi` and `¬IForces ... T psi`, contradicting the assumption.

**Wait** -- finding `T ⊇ S ∪ {phi}` with `psi ∉ T` requires showing `S ∪ {phi} ∪ {neg psi}` is consistent, which requires the **implication witness** argument. This is where the intuitionistic case differs fundamentally: without Peirce, we cannot derive `phi` from `neg(phi → psi)` alone.

### Alternative 2: CZ's Actual Approach (Saturated Tableaux as Worlds)

Re-reading CZ more carefully, the completeness proof for Int (Theorem 2.43) uses:

1. Worlds = **all** saturated consistent tableaux `(Gamma, Delta)` with `Gamma ∪ Delta = Sub(phi)` (for a specific formula phi being refuted)
2. Accessibility = `Gamma ⊆ Gamma'`
3. The implication witness (HS/2): if `psi → chi in Delta`, extend `(Gamma ∪ {psi}, {chi})` to a new saturated tableau

For **strong completeness** (Section 5.1), worlds = all maximal L-consistent tableaux (infinite sets), with the same accessibility.

### Alternative 3: Deductively Closed + Consistent + Imp-Prime (RECOMMENDED)

The cleanest approach that avoids circularity is to define "prime theory" as a **property** (not a structure), similar to how MCS is defined:

```lean
/-- A set S is Int-deductively-closed if whenever all assumptions
are in S and the derivation uses IntPropAxiom, the conclusion is in S. -/
def IntDeductivelyClosed (S : Set (PL.Proposition Atom)) : Prop :=
  ∀ (L : List (PL.Proposition Atom)) (φ : PL.Proposition Atom),
    (∀ x ∈ L, x ∈ S) →
    (propDerivationSystem IntPropAxiom).Deriv L φ → φ ∈ S

/-- A set S is Int-prime if it is consistent, deductively closed, and
has the implication witness property: if `phi → psi ∉ S`, then there
exists a consistent deductively-closed set T ⊇ S with phi ∈ T and
psi ∉ T. -/
def IntPrimeTheory (S : Set (PL.Proposition Atom)) : Prop :=
  PropSetConsistent IntPropAxiom S ∧
  IntDeductivelyClosed S ∧
  ∀ (φ ψ : PL.Proposition Atom),
    Proposition.imp φ ψ ∉ S →
    ∃ T : Set (PL.Proposition Atom),
      S ⊆ T ∧ IntPrimeTheory T ∧ φ ∈ T ∧ ψ ∉ T
```

This is STILL circular. The fundamental issue is that primeness for intuitionistic logic refers to itself.

### RESOLUTION: Use MCS and Prove the Implication Witness Directly

After careful analysis, the correct approach is:

**Worlds = MCS of IntPropAxiom** (exactly as in the classical case). The MCS framework already gives deductive closure and consistency. The key theorem to prove is:

**Implication Witness Lemma**: If `S` is MCS for IntPropAxiom and `phi → psi ∉ S`, then there exists an MCS `T` for IntPropAxiom such that `S ⊆ T`, `phi ∈ T`, and `psi ∉ T`.

This is provable without Peirce's law. Here's why:

1. `phi → psi ∉ S`, so by maximality, `S ∪ {phi → psi}` is inconsistent.
2. By deductive closure argument: from `S` being MCS, either `phi → psi in S` or `neg(phi → psi) in S`.
3. Since `phi → psi ∉ S`, we have `neg(phi → psi) in S`, i.e., `(phi → psi) → bot in S`.
4. Consider `W = S ∪ {phi} ∪ {neg psi}`. Claim: `W` is consistent.
   - Proof: Suppose `W` is inconsistent. Then some finite `L ⊆ W` derives `bot`.
   - Weaken to `[phi, psi → bot] ++ L_S ⊢ bot` where `L_S ⊆ S`.
   - By deduction theorem twice: `L_S ⊢ phi → ((psi → bot) → bot)`.
   - But `(psi → bot) → bot` in intuitionistic logic does NOT give `psi` (that requires Peirce/DNE).
   
**This argument fails!** We cannot derive `phi → psi` from `phi → ((psi → bot) → bot)` in intuitionistic logic.

### CORRECT APPROACH: Separate the Two Assumptions

The correct implication witness argument for intuitionistic logic is:

1. `phi → psi ∉ S` (given).
2. Claim: `S ∪ {phi, neg psi}` is consistent.
3. **Proof of claim**: Suppose inconsistent. Then `L ⊢ bot` for some `L ⊆ S ∪ {phi, neg psi}`.
   - Case A: `neg psi ∉ L`. Then `L ⊆ S ∪ {phi}`, so by deduction theorem: `S ⊢ phi → bot`, i.e. `neg phi ∈ S`. But then `phi → psi` is derivable from `neg phi` (via `⊥ → psi` and composition), so `phi → psi ∈ S`, contradiction.
   - Wait, we need `efq` for this. IntPropAxiom has EFQ. From `neg phi ∈ S`:
     - `phi → bot ∈ S` (this is neg phi)
     - Need: `phi → psi ∈ S`
     - Derivation: from `phi → bot` and `bot → psi` (EFQ), derive `phi → psi` by composition (using implyS/implyK)
     - So `phi → psi ∈ S`, contradicting `phi → psi ∉ S`. Good.
   - Case B: `phi ∉ L` (but `neg psi ∈ L`). Then `L ⊆ S ∪ {neg psi}`, so by deduction theorem: `S ⊢ (psi → bot) → bot`, i.e., `neg neg psi ∈ S`. This does NOT give `psi ∈ S` in intuitionistic logic. However, we need `phi → psi`, not just `psi`. Hmm, this case needs more care.
   
   Actually, let me reconsider. We want: `S ∪ {phi, neg psi}` is consistent, assuming `phi → psi ∉ S`.

   Suppose `L ⊢_Int bot` for `L ⊆ S ∪ {phi, neg psi}`. Partition `L` into `L_S` (elements from S), plus possibly `phi` and `neg psi`. Weaken to `phi :: (neg psi) :: L_S ⊢ bot` where `L_S ⊆ S`.
   
   By deduction theorem on `neg psi`: `phi :: L_S ⊢ (psi → bot) → bot`.
   By deduction theorem on `phi`: `L_S ⊢ phi → ((psi → bot) → bot)`.
   
   Now we need to derive `phi → psi` from `phi → ((psi → bot) → bot)` in Int. We CANNOT do this because DNE is not available.

**So `S ∪ {phi, neg psi}` may NOT be consistent** in Int without Peirce. The implication witness needs a different construction.

### THE CORRECT CONSTRUCTION: Only Add phi

The correct intuitionistic implication witness is:

**Theorem**: If `S` is MCS for IntPropAxiom and `phi → psi ∉ S`, then `S ∪ {phi}` is consistent, and there exists an MCS `T ⊇ S ∪ {phi}` such that `psi ∉ T`.

**Proof of `S ∪ {phi}` consistent**: Suppose not. Then `L ⊢ bot` for some `L ⊆ S ∪ {phi}`. By deduction theorem: `L_S ⊢ phi → bot` where `L_S ⊆ S`. So `phi → bot ∈ S` (by closure). But from `phi → bot` we derive `phi → psi` (via EFQ composition: `phi → bot` and `bot → psi` give `phi → psi`). So `phi → psi ∈ S`, contradiction.

**Proof that `psi ∉ T` for some MCS `T ⊇ S ∪ {phi}`**: We need `S ∪ {phi} ∪ {neg psi}` consistent (or equivalently, `S ∪ {phi, psi → bot}` consistent).

Suppose `L ⊢ bot` for `L ⊆ S ∪ {phi, psi → bot}`. By deduction theorem twice: `L_S ⊢ phi → ((psi → bot) → bot)`.

So `phi → neg neg psi ∈ S`. We need to show this implies `phi → psi ∈ S`, which fails in Int.

**ALTERNATIVE**: We do NOT need `psi ∉ T` for the same MCS. We need a DIFFERENT kind of extension.

### THE ACTUAL CORRECT APPROACH: CZ's Method

Going back to CZ Theorem 2.43:

The worlds are NOT plain MCS. They are **saturated consistent tableaux** `(Gamma, Delta)` where:
- `Gamma ∪ Delta` = all formulas (or Sub(phi) in the finite case)
- Consistency: no derivation of `chi_1 ∨ ... ∨ chi_n` from `Gamma` for `chi_i ∈ Delta`

In the imp/bot language, `chi_1 ∨ chi_2 = (chi_1 → bot) → chi_2`. So "L-consistency of tableau `(Gamma, Delta)`" means:

For no `chi_1, ..., chi_n ∈ Delta` do we have `Gamma ⊢ chi_1 ∨ ... ∨ chi_n`.

This is **stronger** than just `Gamma ⊬ bot`. It's a form of multi-conclusion consistency.

However, this is quite complex to formalize. Let me look for a simpler characterization.

### SIMPLEST CORRECT APPROACH: Theories as Upward-Closed Filters

After extensive analysis, here is the simplest correct approach that matches the codebase patterns:

**Key Insight**: For strong completeness of Int, we can use **the same MCS framework** but with a modified truth lemma strategy.

**Worlds**: MCS for IntPropAxiom (same as classical, just with different axiom set).

**Accessibility**: `S ≤ T iff S ⊆ T` (set inclusion).

**Valuation**: `v S p = (Proposition.atom p ∈ S)`.

**Truth Lemma** (the hard part):

For the imp case forward direction (`IForces ... S (phi.imp psi) → phi.imp psi ∈ S`):

Assume `phi → psi ∉ S`. Need to find MCS `T ⊇ S` with `phi ∈ T` and `psi ∉ T`.

**Claim**: `insert phi S` is consistent (as a set w.r.t. IntPropAxiom).

*Proof*: If not, some `L ⊆ insert phi S` derives `bot`. Extract `phi :: L_S ⊢ bot` with `L_S ⊆ S`. By DT: `L_S ⊢ phi → bot`. By closure: `phi → bot ∈ S`. Then using EFQ composition: derive `phi → psi` from `phi → bot` and `bot → psi`. So `phi → psi ∈ S`, contradiction.

**Claim**: There exists MCS `T ⊇ insert phi S` with `psi ∉ T`.

This requires `insert psi (insert phi S)` being potentially inconsistent, or equivalently, showing that `neg psi` must be in some extension. The issue is: we need an MCS that extends `S ∪ {phi}` but excludes `psi`.

By maximality: for MCS `T`, either `psi ∈ T` or `neg psi ∈ T`. We need the latter.

**Strategy**: Show `S ∪ {phi, neg psi}` is consistent.

Suppose not: `L ⊢ bot` for `L ⊆ S ∪ {phi, neg psi}`. By DT: `L_S ⊢ phi → (neg psi → bot)`, i.e., `L_S ⊢ phi → neg neg psi`. So `phi → neg neg psi ∈ S`.

Now in Int, we CANNOT derive `phi → psi` from `phi → neg neg psi`. But we can derive:
- `(phi → neg neg psi) → ((phi → neg psi) → (phi → bot))` using implyS
- Actually: from `phi → ((psi → bot) → bot)` and `phi → (psi → bot)`, derive `phi → bot`:
  - By S-combinator logic: `(phi → ((psi → bot) → bot)) → ((phi → (psi → bot)) → (phi → bot))` is an instance of implyS with chi = bot.
  
So if `phi → neg neg psi ∈ S` AND `phi → neg psi ∈ S`, then `phi → bot ∈ S`, and then `phi → psi ∈ S` (by EFQ composition), contradicting our assumption.

But we DON'T know that `phi → neg psi ∈ S`. We only have `neg neg psi ∈ S` potentially (from closure), but that doesn't give us `phi → neg psi ∈ S`.

Wait, let me restart this argument more carefully.

Suppose `S ∪ {phi, neg psi}` is inconsistent. Then `L ⊢ bot` for some `L ⊆ S ∪ {phi, neg psi}`.

Case 1: `phi ∉ L` and `neg psi ∉ L`. Then `L ⊆ S` and `L ⊢ bot`, contradicting S consistent.

Case 2: `phi ∈ L` but `neg psi ∉ L`. Then `L ⊆ S ∪ {phi}`. By DT: `L' ⊢ phi → bot` where `L' ⊆ S`. So `neg phi ∈ S`. Then `phi → psi` is derivable from `neg phi` (via EFQ comp), so `phi → psi ∈ S`, contradiction.

Case 3: `phi ∉ L` but `neg psi ∈ L`. Then `L ⊆ S ∪ {neg psi}`. By DT: `L' ⊢ neg psi → bot` where `L' ⊆ S`. So `neg neg psi ∈ S`. **This does NOT give contradiction in Int** because we cannot derive `psi` from `neg neg psi`, nor can we derive `phi → psi` from `neg neg psi`.

Case 4: Both `phi ∈ L` and `neg psi ∈ L`. By DT twice: `L' ⊢ phi → (neg psi → bot)` where `L' ⊆ S`. So `phi → neg neg psi ∈ S`. Same problem as Case 3.

**CONCLUSION**: Cases 3 and 4 do NOT yield contradictions in Int. Therefore `S ∪ {phi, neg psi}` might be inconsistent even when `phi → psi ∉ S`. The MCS approach **does not directly work** for intuitionistic completeness with set inclusion as accessibility.

### FINAL CORRECT APPROACH

After this careful analysis, the correct approach requires one of:

**Option A: Use MCS but with the "tableau pair" view**

Define worlds as MCS but define accessibility differently: `S R T` iff `{phi | phi ∈ S and phi → psi ∈ S implies psi ∈ S for all psi in T}` -- this is too complex.

**Option B: Use CZ's tableau approach (RECOMMENDED)**

This is what CZ actually does. A "world" is characterized by TWO sets: what's IN and what's OUT. For strong completeness, the worlds are all maximal Int-consistent tableaux, where:

- A **tableau** is a pair `(Gamma, Delta)` of sets of formulas with `Gamma ∪ Delta = For_L` (all formulas)
- **Int-consistent**: for no `psi_1, ..., psi_n ∈ Delta` do we have `Gamma ⊢_Int psi_1 ∨ ... ∨ psi_n`
- **Saturated** (= maximal among Int-consistent tableaux with Gamma ∪ Delta = For_L): already maximal by definition

**BUT** in our imp/bot language, `psi_1 ∨ ... ∨ psi_n` is encodable but messy for arbitrary n.

**Option C: Deductively closed + prime sets (SIMPLEST CORRECT APPROACH)**

Define:

```lean
/-- Int-deductively-closed consistent prime set.
- consistent: does not derive bot
- deductively closed: closed under derivation from IntPropAxiom
- prime: for all phi, either phi ∈ S or phi → bot ∈ S
         (this is negation-completeness, same as MCS!) -/
```

Wait -- **MCS for IntPropAxiom already IS negation-complete** by the generic `negation_complete` theorem. The issue is not the definition of worlds but the truth lemma argument.

Let me reconsider the truth lemma more carefully.

**Truth Lemma for Int with MCS worlds and set-inclusion accessibility:**

Forward imp case: `(∀ T ⊇ S, T MCS, phi ∈ T → psi ∈ T) → phi → psi ∈ S`.

Contrapositive: `phi → psi ∉ S → ∃ T MCS, S ⊆ T, phi ∈ T, psi ∉ T`.

This is the **implication witness lemma**. Let me prove it:

Given `phi → psi ∉ S`:
1. By maximality: `S ∪ {phi → psi}` is inconsistent. So there exist `L ⊆ S` such that `[phi → psi] ++ L ⊢ bot`. By DT: `L ⊢ (phi → psi) → bot`. So `neg(phi → psi) ∈ S`.
2. Consider `W = {chi | chi ∈ S} ∪ {phi}`.
3. `W` is consistent: if not, `L' ∪ [phi] ⊢ bot` for `L' ⊆ S`, giving `L' ⊢ phi → bot`, i.e., `neg phi ∈ S`. But from `neg phi` we derive `phi → psi` (by `neg phi ⊢ phi → psi` via EFQ composition: `phi → bot` then `bot → psi`). So `phi → psi ∈ S`, contradiction.
4. Extend `W` to MCS `T`. So `S ⊆ T` and `phi ∈ T`.
5. Need: `psi ∉ T`.
   - We have `neg(phi → psi) ∈ S ⊆ T`, i.e., `(phi → psi) → bot ∈ T`.
   - We have `phi ∈ T`.
   - Suppose `psi ∈ T`. Then by implyK: `phi → psi ∈ T` (from `psi`, derive `phi → psi` via K axiom). Then MP with `(phi → psi) → bot` gives `bot ∈ T`, contradicting T consistent.
6. So `psi ∉ T`. Done!

**THIS WORKS!** The key insight is:

- Step 3 uses EFQ (which Int has) to show consistency of `S ∪ {phi}`
- Step 5 uses the fact that `neg(phi → psi) ∈ S ⊆ T` together with `phi ∈ T` to BLOCK `psi` from being in `T`

**The derivation `psi ∈ T → phi → psi ∈ T`** uses:
- `psi ⊢ phi → psi` (via implyK axiom)
- So `psi ∈ T` implies `phi → psi ∈ T` by deductive closure
- But `(phi → psi) → bot ∈ T` (from `S ⊆ T`)  
- MP gives `bot ∈ T`, contradiction

This is a clean argument that works with standard MCS for IntPropAxiom!

---

## Research Question 2: How Does Lindenbaum's Lemma for Int Work?

**Answer**: The STANDARD Lindenbaum lemma (`set_lindenbaum` from `Consistency.lean`) works perfectly. MCS for IntPropAxiom is defined exactly as for any other axiom set via the generic `SetMaximalConsistent` definition. No special prime theory extension is needed.

The existing infrastructure provides:
- `prop_lindenbaum`: Every PropSetConsistent set extends to PropSetMaximalConsistent
- `prop_closed_under_derivation`: MCS is deductively closed (requires DT)
- `prop_implication_property`: MP closure
- `prop_negation_complete`: Negation completeness
- `prop_mcs_bot_not_mem`: Bot exclusion

All of these are **already parameterized over `Axioms`**, so we can instantiate at `IntPropAxiom` directly, supplying `h_implyK := fun phi psi => .implyK phi psi` and `h_implyS := fun phi psi chi => .implyS phi psi chi`.

**No IntLindenbaum.lean file is needed!** The MCS.lean file already provides everything parameterized.

---

## Research Question 3: Canonical Kripke Model

```lean
/-- A canonical world for intuitionistic logic is an MCS of IntPropAxiom. -/
def IntCanonicalWorld :=
  { S : Set (PL.Proposition Atom) // PropSetMaximalConsistent IntPropAxiom S }

/-- The canonical Kripke model for intuitionistic logic.
    - World type: IntCanonicalWorld
    - Preorder: set inclusion (S.val ⊆ T.val)
    - Valuation: v w p = (Proposition.atom p ∈ w.val)
    - bot_forces: fun _ => False (intuitionistic semantics) -/
```

The accessibility relation is `S.val ⊆ T.val`. This is a preorder (reflexive + transitive). We need to prove:
1. The valuation is upward-closed: if `atom p ∈ S` and `S ⊆ T`, then `atom p ∈ T`. This is trivially true by set inclusion.
2. `bot_forces = fun _ => False` is trivially upward-closed.

The canonical model uses `IForces` from `Kripke.lean` with:
- `v := fun w p => Proposition.atom p ∈ w.val`
- `bot_forces := fun _ => False`

---

## Research Question 4: Truth Lemma for the Imp Case

### Backward Direction (Easy)

`phi → psi ∈ S → IForces v bf S (phi.imp psi)`

Unfold: need `∀ T ⊇ S, IForces v bf T phi → IForces v bf T psi`.

Given `T ⊇ S` and `IForces v bf T phi`:
- By IH backward: `phi ∈ T`
- `phi → psi ∈ S ⊆ T`, so `phi → psi ∈ T`
- By `prop_implication_property`: `psi ∈ T`
- By IH forward: `IForces v bf T psi`

### Forward Direction (Hard, Key Lemma)

`IForces v bf S (phi.imp psi) → phi → psi ∈ S`

Contrapositive: `phi → psi ∉ S → ∃ T ⊇ S (T MCS), IForces v bf T phi ∧ ¬IForces v bf T psi`.

By the implication witness lemma (proved above):
1. `phi → psi ∉ S` implies `neg(phi → psi) ∈ S` (negation completeness)
2. `S ∪ {phi}` is consistent (using EFQ composition argument)
3. Extend to MCS `T ⊇ S ∪ {phi}`, so `phi ∈ T` and `S ⊆ T`
4. `psi ∉ T` (because `neg(phi → psi) ∈ T` and `psi ∈ T` would give `phi → psi ∈ T` then `bot ∈ T`)
5. By IH: `IForces v bf T phi` and `¬IForces v bf T psi`

The key derivation in step 2 that `neg phi` implies `phi → psi`:
```
-- From neg phi (= phi → bot) and bot → psi (EFQ), derive phi → psi
-- Using implyS: (phi → (bot → psi)) → ((phi → bot) → (phi → psi))
-- step 1: bot → psi  (EFQ axiom)
-- step 2: phi → (bot → psi)  (implyK on step 1)
-- Actually: use implyK to get ⊢ (bot → psi) → (phi → (bot → psi))
-- Then MP with EFQ to get ⊢ phi → (bot → psi)
-- Then implyS to get ⊢ (phi → (bot → psi)) → ((phi → bot) → (phi → psi))
-- MP to get ⊢ (phi → bot) → (phi → psi)
-- MP with neg phi to get ⊢ phi → psi
```

The key derivation in step 4 that `psi ∈ T → phi → psi ∈ T`:
```
-- implyK: ⊢ psi → (phi → psi)
-- By MCS closure: psi ∈ T implies phi → psi ∈ T
-- Then (phi → psi) → bot ∈ T and phi → psi ∈ T give bot ∈ T
-- Contradiction with T consistent
```

---

## Research Question 5: MCS Infrastructure Reuse

**Everything from MCS.lean can be reused as-is**, since all definitions are parameterized over `Axioms`:

| MCS.lean Definition | Reuse | Notes |
|---------------------|-------|-------|
| `PropSetConsistent` | Direct | At `IntPropAxiom` |
| `PropSetMaximalConsistent` | Direct | At `IntPropAxiom` |
| `prop_lindenbaum` | Direct | At `IntPropAxiom` |
| `prop_closed_under_derivation` | Direct | Supply `h_implyK`, `h_implyS` from IntPropAxiom |
| `prop_implication_property` | Direct | Supply `h_implyK`, `h_implyS` from IntPropAxiom |
| `prop_negation_complete` | Direct | Supply `h_implyK`, `h_implyS` from IntPropAxiom |
| `prop_mcs_bot_not_mem` | Direct | At `IntPropAxiom` |
| `prop_mcs_neg_of_not_mem` | Direct | Supply `h_implyK`, `h_implyS` from IntPropAxiom |
| `prop_mcs_not_mem_of_neg` | Direct | Supply `h_implyK`, `h_implyS` from IntPropAxiom |
| `prop_mcs_mem_iff_neg_not_mem` | Direct | Supply `h_implyK`, `h_implyS` from IntPropAxiom |

**New infrastructure needed for IntCompleteness.lean**:
1. `int_imp_witness`: The implication witness lemma (the hard part)
2. `int_neg_phi_imp_psi`: Derivation that `neg phi ⊢ phi → psi` (via EFQ composition)
3. `int_neg_consistent_of_not_derivable`: If `phi` not derivable, `{neg phi}` consistent (same as classical, but WITHOUT Peirce -- needs different argument)

**CRITICAL**: The `neg_consistent_of_not_derivable` in the modal case uses Peirce's law. The intuitionistic version needs a DIFFERENT proof. Specifically:

In the classical case: if `{neg phi}` is inconsistent, derive `[neg phi] ⊢ bot`, then DT gives `⊢ neg phi → bot`, then use Peirce to get `⊢ phi`.

In the intuitionistic case: if `{neg phi}` is inconsistent, derive `[neg phi] ⊢ bot`, then DT gives `⊢ neg phi → bot`, i.e., `⊢ neg neg phi`. But we cannot derive `phi` from `neg neg phi` in Int!

**HOWEVER**, for the completeness proof, we don't actually need `{neg phi}` consistent. We need the **EMPTY SET** to be consistent when `phi` is not derivable. The argument is:

- Assume `IValid phi` (valid in all Kripke models).
- Assume `phi` is not derivable from IntPropAxiom.
- Need to find a countermodel.
- The empty set `{}` is consistent (since `phi` is not derivable, and `{} ⊢ bot` implies `{} ⊢ phi` via EFQ, contradiction).

Wait, `{} ⊢ bot` directly contradicts consistency because EFQ gives `⊢ phi` for any phi. Actually, the empty set is always consistent as long as the axiom system is consistent (doesn't derive bot). And IntPropAxiom is consistent (it has a model: any single-world Kripke model).

The actual completeness argument: assume `phi` is not derivable. Then `{phi → bot}` (= `{neg phi}`) might or might not be consistent. We need a different starting point.

**Correct argument for intuitionistic completeness**:

Assume `¬ Derivable IntPropAxiom phi`. Want to find a Kripke model refuting `phi`.

1. Consider the canonical model (all MCS of IntPropAxiom).
2. We need an MCS `S` with `phi ∉ S`.
3. Show `{neg phi}` is consistent: if `L ⊢ bot` with `L ⊆ {neg phi}`, then `[neg phi] ⊢ bot` or `[] ⊢ bot`.
   - If `[] ⊢ bot`, then `[] ⊢ phi` by EFQ, contradicting non-derivability.
   - If `[neg phi] ⊢ bot`, then by DT: `[] ⊢ neg phi → bot`, i.e., `⊢ (phi → bot) → bot`. This is `⊢ neg neg phi`. But we need `⊢ phi`, which we can't get in Int.
   
   **So `{neg phi}` might be inconsistent even though `phi` is not Int-derivable!** This happens when `neg neg phi` is Int-derivable but `phi` is not (e.g., take phi = any formula where DNE fails).

4. **Alternative starting set**: Instead of `{neg phi}`, consider just that `{phi}` together with `S` for some base. Actually, the right approach:

   Since `phi` is not derivable, `[] ⊬ phi`. By maximality, there exists MCS `S` such that `phi ∉ S`.
   
   Wait, we need to construct an MCS not containing `phi`. The standard approach: the set `{neg phi}` might not be consistent. But we can use a WEAKER starting point.

   **Key**: `{}` is consistent (the empty set -- because if `[] ⊢ bot` then by EFQ `[] ⊢ phi` for any phi, so every formula is derivable, but Int is consistent). Extend `{}` to MCS `S` by Lindenbaum. Then either `phi ∈ S` or `neg phi ∈ S`. If `phi ∉ S`, we're done. If `phi ∈ S` for EVERY MCS, then `phi` is derivable (by the "second direction" of Lindenbaum/MCS theory: a formula in every MCS is derivable).

   Actually, the contrapositive of derivability: `phi` is derivable iff `phi ∈ S` for every MCS `S`. This is exactly `Metalogic.SetMaximalConsistent.closed_under_derivation` applied globally.

   So if `phi` is NOT derivable, there exists MCS `S` with `phi ∉ S`. Proof: by contrapositive of the fact that derivable implies in every MCS. More precisely:

   Suppose `phi ∈ S` for every MCS. Then `neg phi = (phi → bot) ∉ S` for every MCS (by `prop_mcs_not_mem_of_neg`... wait, that goes the wrong way). Let me think again.

   Actually the direct argument: if `phi ∉ S` for some MCS `S`, then by truth lemma (backward for atoms/bot, forward/backward for imp), `¬IForces v bf S phi` in the canonical model, giving a countermodel.

   But we need `phi ∉ S` for some MCS. Proof: if `phi` is not derivable, then `[] ⊬ phi`. By maximality of `S`: `phi ∉ S` implies `insert phi S` is inconsistent, while `phi ∈ S` is the only other option. We need to show NOT every MCS contains `phi`.

   Suppose every MCS contains `phi`. Then for the empty set (which is consistent), extend to MCS `M`. We have `phi ∈ M`. Is this always the case? The answer is: `phi ∈ M` for every MCS `M` iff `[] ⊢ phi`. This follows from:
   - Forward: if `[] ⊢ phi`, then by `closed_under_derivation` (with empty L), `phi ∈ M`.
   - Backward: if `phi ∈ M` for every MCS, then `phi ∉ M` is impossible for any MCS, so `insert (neg phi) M` is inconsistent... hmm, this gets circular.

   The standard proof: assume `[] ⊬ phi`. Then `{neg phi}` ... but we showed this might not be consistent in Int.

   **RESOLUTION**: The correct argument uses the fact that `phi ∉ M` for some MCS iff `¬[] ⊢ phi`. The proof:

   If `[] ⊬ phi`, then `[] ⊬ phi` means there's no derivation tree. By maximality of MCS: for any MCS `M`, either `phi ∈ M` or `phi ∉ M`. We need `phi ∉ M` for some `M`.

   The clean proof: Consider any MCS `M`. We claim NOT every MCS contains `phi`. Suppose for contradiction that every MCS contains `phi`. Consider any list `L ⊆ S` for any consistent set `S`. Extend `S` to MCS `M`. Then `phi ∈ M`. Since `S ⊆ M`...

   Actually, this is proved by the standard result: **`phi` derivable iff `phi ∈ M` for every MCS `M`** (CZ Lemma 5.2). The forward direction uses `closed_under_derivation`. The backward direction: if `phi` is not derivable, then `{phi → bot}` extended... no, the backward direction is the hard part for Int.

   **CZ Lemma 5.2 backward direction**: Suppose `A ⊬_L phi`. Then `(A, {phi})` is L-consistent (as a tableau). By Lindenbaum, extend to maximal tableau `(Gamma, Delta)`. Then `A ⊆ Gamma` and `phi ∈ Delta`, so `phi ∉ Gamma`.

   In CZ's tableau framework, `(A, {phi})` being L-consistent means: `A` does not derive `phi` (since `{phi}` is a singleton, the disjunction is just `phi`). This is exactly `A ⊬ phi`, which is given.

   **Translating to our framework**: We need `(A, {phi})` consistent in the tableau sense, which means `A ⊬ phi`. In our set-based framework, this translates to: the set `A` together with the requirement that `phi` is excluded should be consistent.

   For the completeness proof with `A = {}`: `[] ⊬ phi` (given). We need to find MCS `M` with `phi ∉ M`.

   **Direct proof**: By `prop_negation_complete` for MCS `M`: either `phi ∈ M` or `neg phi ∈ M`. We can't rule out `phi ∈ M` for all `M`. However:
   
   Since `[] ⊬ phi`, the derivation system is non-trivial. Consider the single-world Kripke model where valuation assigns False to all atoms. Then `IForces v (fun _ => False) w phi` may or may not hold. If it doesn't hold for some valuation/model, we already have a countermodel from soundness considerations.

   Wait, the completeness proof should NOT require constructing the countermodel from scratch. It should use the canonical model. Let me reconsider.

   **THE CORRECT AND SIMPLE ARGUMENT**:

   By contrapositive. Assume `phi` is not derivable. Then `[] ⊬ phi`. 
   
   Claim: there exists MCS `S` with `phi ∉ S`.
   
   Proof: Suppose every MCS contains `phi`. Consider the consistent set `{}`. Extend to MCS `M` (by Lindenbaum). Then `phi ∈ M` by assumption. Now for any list `L ⊆ M`, if `L ⊢ bot`, then `M` is inconsistent, contradiction. So this doesn't help directly.
   
   Instead: since `[] ⊬ phi`, by DT arguments there's no derivation of `phi` from the empty context. Now the set `{phi → bot}` may or may not be consistent.
   
   If `{phi → bot}` IS consistent: extend to MCS `M`. Then `phi → bot ∈ M`, so `phi ∉ M` (by `prop_mcs_not_mem_of_neg`). Done.
   
   If `{phi → bot}` is NOT consistent: then `[phi → bot] ⊢ bot`, so `⊢ (phi → bot) → bot`, i.e., `⊢ neg neg phi`. But `⊬ phi`. This is possible in Int (e.g., `phi = p ∨ neg p`). In this case... we still need to find MCS with `phi ∉ M`.
   
   Since `⊬ phi`: the set of formulas derivable from `[]` does not include `phi`. Consider the set `Th = {psi | [] ⊢ psi}` (the Int-theory). This is consistent (if `[] ⊢ bot` then by EFQ everything is derivable including `phi`, contradiction). Extend `Th` to MCS `M`. Then `phi ∈ M` iff `phi ∈ Th` iff `[] ⊢ phi`, which is false. So `phi ∉ M`. Done!

   Wait, is `Th ⊆ M`? Yes, by construction (Lindenbaum extends consistent sets). And `phi ∉ Th` since `⊬ phi`. But does `phi ∉ Th` imply `phi ∉ M`? Not necessarily -- Lindenbaum might add `phi` to the extension!

   Hmm. Let me think again. The issue is that Lindenbaum extends by adding formulas, so `phi` might get added even though `phi ∉ Th`.

   **THE REAL ARGUMENT** (finally correct):

   `⊬ phi` means `[] ⊬ phi`. This means the set `{}` does not derive `phi`. By the backward direction of Lemma 5.2 in CZ:

   `A ⊬ phi` iff there exists a maximal L-consistent tableau `(Gamma, Delta)` with `A ⊆ Gamma` and `phi ∈ Delta`.

   In our framework: `A ⊬ phi` iff there exists MCS `M ⊇ A` with `phi ∉ M`.

   Proof: If `phi ∈ M` for every MCS `M ⊇ A`, then by `closed_under_derivation`: `phi` is derivable from any list `L ⊆ A`... no, `closed_under_derivation` says: if `L ⊢ phi` and `L ⊆ M` then `phi ∈ M`. The converse is what we need.

   The converse uses maximality: if `phi ∉ M$, then `insert phi M` is inconsistent, so there exist `L ⊆ insert phi M` with `L ⊢ bot`. Extract `phi :: L_S ⊢ bot` with `L_S ⊆ M`. By DT: `L_S ⊢ phi → bot`. So `neg phi ∈ M$ by closure.

   OK so the standard fact IS: `phi ∈ M` for EVERY MCS `M` iff `⊢ phi`.

   Forward: `⊢ phi` implies `phi ∈ M$ by closure (derivation from empty context, then weakening).

   Backward: Suppose `⊬ phi`. We want MCS with `phi ∉ M`. 
   
   **Key construction**: Consider any MCS `M`. By `prop_negation_complete`: either `phi ∈ M` or `neg phi ∈ M`. If `neg phi ∈ M`, then `phi ∉ M` (by `prop_mcs_not_mem_of_neg`). So if there's ANY MCS with `neg phi ∈ M`, we're done.
   
   Suppose for contradiction that no MCS contains `neg phi`. Then `neg phi ∉ M` for all MCS `M`, so `phi ∈ M$ for all MCS `M`. We need to show `⊢ phi`.
   
   Since `neg phi ∉ M$ for all MCS, by maximality: for each MCS `M`, `insert (neg phi) M` is inconsistent. So... this is getting complex.

   **SIMPLEST CORRECT PROOF**: Since `⊬ phi`, the set `{phi → bot}` may or may not be consistent:
   
   If consistent: extend to MCS with `neg phi ∈ M$, giving `phi ∉ M`. Done.
   
   If inconsistent: `⊢ neg neg phi`. But `⊬ phi`. So `neg neg phi` is derivable but `phi` is not. This is possible in Int. In this case, we STILL need a countermodel.
   
   Construct one directly: consider the two-world Kripke model `{w0, w1}` with `w0 ≤ w1`, `w0 ≤ w0`, `w1 ≤ w1`, and choose the valuation so that `phi` fails at `w0`. This is ad-hoc and depends on the structure of `phi`.
   
   **Actually, the canonical model itself provides the countermodel!** The canonical model contains ALL MCS as worlds. If `phi ∈ M$ for every MCS, then by the truth lemma, `phi$ is forced at every world, so `phi$ is valid in the canonical model. But the canonical model validates exactly the Int-derivable formulas (by soundness + truth lemma). If `phi$ is valid in the canonical model and `⊬ phi$, we get a contradiction with soundness... wait, soundness says derivable implies valid, not the converse.
   
   Hmm. Let me go back to CZ's exact argument for completeness (Theorem 2.43, completeness direction via Theorem 5.5):
   
   CZ Theorem 5.5: "every L-consistent tableau is realized in the canonical model". In particular, `({}, {phi})$ is L-consistent (since `⊬ phi$), so it is realized: there exists world `t$ in the canonical model with `{} ⊆ Gamma_t$ and `phi ∈ Delta_t$, i.e., `phi ∉ Gamma_t$ (since `Gamma_t ∪ Delta_t = For_L$ and they are disjoint).
   
   The CZ proof of Theorem 5.5 goes through Lemma 5.1 (Lindenbaum) and Theorem 5.4 (truth lemma). Lindenbaum extends the consistent tableau `({}, {phi})$ to a maximal consistent tableau `(Gamma, Delta)$ with `phi ∈ Delta$.
   
   **In our framework**: CZ's maximal consistent tableau `(Gamma, Delta)$ corresponds to an MCS `Gamma` where `Delta = Gamma^c$. The condition "`phi ∈ Delta$" is "`phi ∉ Gamma$".
   
   But CZ's "L-consistent tableau `(A, {phi})$" means `A ⊬ phi$ (in Int). This is NOT the same as "the SET `A` is consistent" in our framework. The tableau consistency is: `A$ does not derive `phi$ (not: `A$ does not derive `bot$).
   
   **Translation**: CZ's Lindenbaum (Lemma 5.1) for tableaux says: any L-consistent tableau extends to a maximal one. This means: if `A ⊬ phi$, then there exists maximal tableau `(Gamma, Delta)$ with `A ⊆ Gamma$ and `phi ∈ Delta$.
   
   In our set-based framework: if `A ⊬ phi$, we need MCS `M ⊇ A$ with `phi ∉ M$.
   
   **Proof**: If `A ⊬ phi$, then `insert (phi → bot) A$ is a SET that might or might not be consistent...
   
   OK, I think the cleanest proof for this specific step is:
   
   **Lemma (int_not_derivable_implies_not_in_some_mcs)**: If `⊬ phi$, then there exists MCS `M$ with `phi ∉ M$.
   
   **Proof**: Consider `S = {phi → bot}$. We show `S$ is set-consistent for IntPropAxiom.
   
   Suppose not: `L ⊢ bot$ for `L ⊆ S$. Then either `L = []$ or `L = [phi → bot]$ (or repetitions).
   - If `L = []$: `⊢ bot$, hence by EFQ `⊢ phi$, contradicting `⊬ phi$.
   - If `phi → bot ∈ L$: weaken to `[phi → bot] ⊢ bot$. By DT: `⊢ (phi → bot) → bot$, i.e., `⊢ neg neg phi$.
     Now, `⊢ neg neg phi$ does NOT imply `⊢ phi$ in Int. So this does NOT give a contradiction!
   
   **So `{neg phi}$ might indeed be inconsistent for IntPropAxiom**, meaning there exist formulas `phi$ such that `neg neg phi$ is Int-derivable but `phi$ is not (e.g., `phi = p ∨ ¬p = (p → bot) → p → bot... wait, `¬¬(p ∨ ¬p)$ IS derivable in Int but `p ∨ ¬p$ is not).
   
   In this case, `{neg phi}$ is inconsistent, and we CANNOT use it as our starting consistent set.
   
   **Alternative starting set**: Use `{neg phi} ∪ Th_Int$ where `Th_Int$ is the set of Int-derivable formulas? No, that's not simpler.
   
   **The correct approach**: We don't start from `{neg phi}$. Instead:
   
   Since `⊬ phi$, consider the set `T_0 = {psi | [] ⊢_Int psi}$ (the Int-theorems). This is consistent. By negation completeness for any MCS `M ⊇ T_0$: either `phi ∈ M$ or `neg phi ∈ M$.
   
   If there exists such `M$ with `phi ∉ M$, done.
   
   If `phi ∈ M$ for every MCS extending `T_0$, then `phi$ is in the intersection of all MCS. By a standard result, the intersection of all MCS is exactly the set of derivable formulas. Therefore `phi$ is derivable, contradiction.
   
   **Proving "intersection of all MCS = derivable formulas"**:
   - Forward: derivable implies in every MCS (by closed_under_derivation).  
   - Backward: if `phi$ in every MCS, suppose `⊬ phi$. Then... we need to show not every MCS contains `phi$. This is circular!
   
   **THE NON-CIRCULAR PROOF** uses a DIRECT construction:
   
   We bypass the issue entirely. The completeness proof proceeds as:
   
   Assume `IValid phi$ (forced in every intuitionistic Kripke model at every world).
   Assume `⊬ phi$.
   
   We build a SPECIFIC model refuting `phi$:
   
   1. Build the canonical model (all Int-MCS with set inclusion).
   2. By soundness (which we prove first), every Int-derivable formula is valid in all Kripke models, hence in the canonical model.
   3. By the truth lemma: for each MCS `S$ and formula `psi$: `IForces v bf S psi ↔ psi ∈ S$.
   4. If `phi$ were in every MCS, then by truth lemma backward: `IForces v bf S phi$ for every world `S$, so `phi$ is valid in the canonical model.
   5. But `IValid phi$ means `phi$ is valid in EVERY model including the canonical model... wait, this goes in the WRONG direction for a contradiction.
   
   **Let me restart the completeness proof structure**:
   
   We prove: `IValid phi → Derivable IntPropAxiom phi$.
   
   Contrapositive: `¬Derivable IntPropAxiom phi → ¬IValid phi$.
   
   Assume `⊬ phi$. Want `¬IValid phi$, i.e., some model and world where `phi$ is not forced.
   
   Construct the canonical model. By truth lemma: `IForces ... S phi ↔ phi ∈ S$ for every canonical world `S$.
   
   If there exists canonical world `S$ with `phi ∉ S$, then `¬IForces ... S phi$, giving the countermodel.
   
   If `phi ∈ S$ for every canonical world... then we need another argument.
   
   **But there IS a canonical world with `phi ∉ S$!**
   
   Here's why: `⊬ phi$ means `Deriv IntPropAxiom [] phi$ is false. Consider `Deriv IntPropAxiom$ as the derivation system. The empty set is consistent (if `[] ⊢ bot$, then by EFQ `[] ⊢ phi$, contradiction). Extend `{}$ to MCS `M$ by Lindenbaum.
   
   Now: is `phi ∈ M$? `phi ∈ M$ iff... by deductive closure, `phi ∈ M$ if `L ⊆ M, L ⊢ phi$ for some `L$. Since `[] ⊢ phi$ is false, the empty list doesn't work. But Lindenbaum might add `phi$ to `M$ during the extension process!
   
   The extension process (Zorn/enumeration): at each step, if adding `psi$ keeps consistency, add it; otherwise don't. Whether `phi$ gets added depends on whether `{phi} ∪ (current set)$ is consistent.
   
   If `phi$ gets added (i.e., adding `phi$ to the current set is consistent), then `phi ∈ M$. If not, `phi ∉ M$. The enumeration order matters!
   
   **Key**: We can control this. Instead of extending `{}$, extend `{neg phi}$ if it's consistent, or use a different strategy.
   
   **ACTUAL SOLUTION**: We don't need `{neg phi}$ to be consistent. We use a more subtle argument:
   
   **Lemma**: If `⊬ phi$ (i.e., `[] ⊬ phi$ in IntPropAxiom), then there exists IntPropAxiom-MCS `M$ with `phi ∉ M$.
   
   **Proof**: Since `[] ⊬ phi$, the formula `phi$ is not derivable from the empty context. 
   
   Consider the set `T = {phi → bot}$. If `T$ is consistent, extend to MCS with `neg phi ∈ M$, giving `phi ∉ M$ by `prop_mcs_not_mem_of_neg$. Done.
   
   If `T$ is inconsistent: `[phi → bot] ⊢ bot$, so by DT: `⊢ neg neg phi$. 
   
   In this case, `neg neg phi$ is derivable but `phi$ is not. Since `neg neg phi$ is derivable, it's in every MCS. In particular, for any MCS `M$: `neg neg phi = (phi → bot) → bot ∈ M$.
   
   By negation completeness: either `phi ∈ M$ or `neg phi ∈ M$.
   
   If `neg phi ∈ M$ for some M: then `neg neg phi ∈ M$ AND `neg phi ∈ M$, giving `bot ∈ M$ by MP, contradicting consistency. So `neg phi ∉ M$ for every MCS.
   
   Therefore `phi ∈ M$ for every MCS (by negation completeness, since `neg phi ∉ M$ forces `phi ∈ M$... wait, negation completeness says `phi ∈ M$ OR `neg phi ∈ M$, and we just showed `neg phi ∉ M$, so `phi ∈ M$).
   
   But then `phi$ is in every MCS. By the truth lemma, `phi$ is forced at every world of the canonical model. So the canonical model validates `phi$. But we assumed `⊬ phi$...
   
   **This means**: if `⊬ phi$ and `⊢ neg neg phi$, then the canonical model DOES validate `phi$ (since `phi ∈ M$ for every MCS). This gives `IValid phi$ in the canonical model. But `IValid$ quantifies over ALL models, not just canonical. So there might be another model refuting `phi$.
   
   However, our completeness proof must produce a SPECIFIC countermodel from `⊬ phi$. The canonical model doesn't work in this case!

   **FUNDAMENTAL ISSUE**: The canonical model approach for Int completeness using MCS and set inclusion DOES NOT WORK DIRECTLY when `neg neg phi$ is derivable but `phi$ is not, because all MCS contain `phi$ in that case.

   This confirms that **MCS alone is insufficient for intuitionistic completeness**. We need the CZ tableau approach or an equivalent.

---

## Research Question 6: The Correct Architecture

After the deep analysis above, the correct approach for intuitionistic completeness requires one of:

### Approach A: CZ Tableau Pairs (Complete but Complex)

Define worlds as tableau pairs `(Gamma, Delta)$. This is CZ's actual approach. It handles all cases correctly but requires significant new infrastructure.

### Approach B: Theories with Disjunction Property (Standard in Modern Treatments)

In modern treatments (e.g., Troelstra & van Dalen, van Dalen "Logic and Structure"), the worlds in the canonical model for Int are **prime theories** (also called **prime filters**):

A set `S$ is a **prime theory** for Int if:
1. `S$ is a **theory** (= deductively closed: if `L ⊆ S$ and `L ⊢ phi$ then `phi ∈ S$)
2. `S$ is **consistent** (`bot ∉ S$)
3. `S$ has the **disjunction property**: if `phi ∨ psi ∈ S$ then `phi ∈ S$ or `psi ∈ S$

In our imp/bot language, `phi ∨ psi = (phi → bot) → psi$, so condition 3 becomes:
> If `(phi → bot) → psi ∈ S$, then `phi → bot ∈ S$ or `psi ∈ S$

Equivalently (using derived connectives): prime means for all `phi, psi$:
> `(neg phi) → psi ∈ S$ implies `neg phi ∈ S$ or `psi ∈ S$

**But this is EXACTLY what negation completeness for MCS gives us!** For MCS `M$:
- Either `neg phi ∈ M$ or `neg neg phi ∈ M$ (by negation completeness applied to `neg phi$)
- If `neg neg phi ∈ M$ and `(neg phi) → psi ∈ M$, then... hmm, we need `psi ∈ M$.

Actually, the disjunction property for MCS in the imp/bot language:
- `(phi → bot) → psi ∈ M$
- By negation completeness on `phi$: `phi ∈ M$ or `phi → bot ∈ M$
- If `phi → bot ∈ M$: by MP, `psi ∈ M$. Done.
- If `phi ∈ M$ but `phi → bot ∉ M$: then `phi ∈ M$ and `(phi → bot) → psi ∈ M$. We can't conclude `psi ∈ M$ from these (we'd need `phi → bot ∈ M$).

Wait, let me reconsider. We need: `phi → bot ∈ M$ OR `psi ∈ M$. We have:
- Case 1: `phi → bot ∈ M$. Then `phi → bot ∈ M$, first disjunct holds.
- Case 2: `phi → bot ∉ M$ (so `phi ∈ M$ by some argument... actually `phi ∉ M → phi → bot ∈ M$ by negation completeness, contrapositive: `phi → bot ∉ M → phi ∈ M$... no, negation completeness says `phi ∈ M$ OR `phi → bot ∈ M$, so if `phi → bot ∉ M$ then `phi ∈ M$).

In Case 2: `phi ∈ M$ and `phi → bot ∉ M$. We have `(phi → bot) → psi ∈ M$. We need `psi ∈ M$.

From `phi → bot ∉ M$: by negation completeness on `phi → bot$: `(phi → bot) ∈ M$ or `((phi → bot) → bot) ∈ M$. Since `phi → bot ∉ M$, we get `(phi → bot) → bot ∈ M$, i.e., `neg neg phi ∈ M$.

But we need `psi ∈ M$, not `neg neg phi ∈ M$. We have `(phi → bot) → psi ∈ M$ and `phi → bot ∉ M$. Without `phi → bot ∈ M$, we cannot apply MP. And we have no way to derive `psi$ from `(phi → bot) → psi$ and `neg neg phi$ alone.

**So MCS does NOT have the disjunction property in general!** This confirms that MCS ≠ prime theory for Int.

### Approach C: The Actual Working Approach (RECOMMENDED)

After all this analysis, here is the architecture that actually works:

**Key realization**: The problem with MCS + set inclusion is that MCS for Int has STRONGER properties than needed (negation completeness) but LACKS the disjunction property, and the truth lemma for imp fails because we can't find the right witness.

BUT WAIT -- in our earlier analysis (Research Question 4), we DID prove the implication witness lemma! Let me revisit:

**Implication Witness Lemma** (re-stated):
If `S$ is MCS for IntPropAxiom and `phi → psi ∉ S$, then there exists MCS `T$ for IntPropAxiom with `S ⊆ T$, `phi ∈ T$, and `psi ∉ T$.

**Proof** (from our earlier analysis):
1. `phi → psi ∉ S$, so `neg(phi → psi) = (phi → psi) → bot ∈ S$ (by negation completeness).
2. `S ∪ {phi}$ is consistent. Proof: if not, by DT `S ⊢ phi → bot$, so `neg phi ∈ S$. From `neg phi$ derive `phi → psi$ (via EFQ composition), contradicting `phi → psi ∉ S$.
3. Extend `S ∪ {phi}$ to MCS `T$. So `S ⊆ T$ and `phi ∈ T$.
4. `psi ∉ T$: if `psi ∈ T$, then by implyK closure `phi → psi ∈ T$. But `(phi → psi) → bot ∈ S ⊆ T$. MP gives `bot ∈ T$, contradiction.

**This proof is correct and uses only Int axioms (K, S, EFQ).** No Peirce needed.

Now the **truth lemma forward direction for imp**:

`IForces v bf S (phi.imp psi) → phi → psi ∈ S$

Proof by contrapositive: assume `phi → psi ∉ S$. By implication witness: exists MCS `T ⊇ S$ with `phi ∈ T$ and `psi ∉ T$. By IH (backward): `IForces v bf T phi$. By IH (backward from `psi ∉ T$): well, we need `¬IForces v bf T psi$. By IH forward direction on `psi$: `IForces v bf T psi ↔ psi ∈ T$. Since `psi ∉ T$, `¬IForces v bf T psi$.

So `T$ is a witness: `S ⊆ T$, `IForces v bf T phi$, and `¬IForces v bf T psi$. Therefore `¬IForces v bf S (phi.imp psi)$.

**This works!** The truth lemma is correct with MCS worlds and set inclusion.

Now the **completeness argument**:

Assume `⊬ phi$. Need countermodel.

**Claim**: there exists MCS `S$ with `phi ∉ S$.

We showed above that this might fail if `neg neg phi$ is derivable but `phi$ is not (e.g., `phi = p ∨ ¬p$ in the imp/bot encoding). In that case, every MCS contains `phi$.

**BUT WAIT**: let's check if this is actually true. Does every MCS for IntPropAxiom contain `p ∨ ¬p$?

`p ∨ ¬p = (p → bot) → p$ (in the imp/bot encoding, since `A ∨ B = (A → ⊥) → B$, and `¬p = p → bot$, so `p ∨ ¬p = (p → bot) → p$).

Wait: `p ∨ ¬p = ¬p → ¬p... no. `p ∨ ¬p = (¬p) → (¬p)$? No: `A ∨ B = (A → ⊥) → B$. So `p ∨ (¬p) = (p → ⊥) → (p → ⊥) = (p → ⊥) → (p → ⊥)$. But that's `¬p → ¬p$, which IS derivable in Int (it's an instance of `A → A$). So `p ∨ ¬p$ is actually DERIVABLE in our encoding!

Wait, that can't be right. Let me re-check:

`Proposition.or A B = .imp (.imp A .bot) B` (from Defs.lean line 64)

So `p ∨ ¬p = or (atom p) (neg (atom p)) = .imp (.imp (atom p) .bot) (neg (atom p)) = .imp (.imp (atom p) .bot) (.imp (atom p) .bot)$

This is `(p → ⊥) → (p → ⊥)$, which is `¬p → ¬p$, which IS a theorem of Int (instance of `A → A$).

So **our encoding of `p ∨ ¬p$ IS intuitionistically valid**! This is because disjunction in the imp/bot encoding doesn't correspond to the "true" intuitionistic disjunction. In the full intuitionistic language with primitive `∨$, `p ∨ ¬p$ is NOT derivable. But in our imp/bot encoding, the "disjunction" `(¬A) → B$ is weaker than true disjunction.

**This is a crucial observation**: In the imp/bot fragment, intuitionistic and classical logic are actually NOT as different as in the full language. Specifically:

**Glivenko's theorem**: For the implication-negation fragment (which is our imp/bot language), `⊢_Cl phi$ iff `⊢_Int neg neg phi$. Moreover, for the imp/bot fragment, Int and Cl prove the same formulas (Harrop's result, or see CZ).

Actually, CZ Theorem 2.47: "The following conditions are equivalent for any formula `phi$ in the language `{→, ⊥}$: (i) `⊢_Cl phi$; (ii) `⊢_Int phi$."

**WAIT** -- this means that for the `{→, ⊥}$ fragment, Int = Cl! So the "intuitionistic completeness" in this fragment is IDENTICAL to classical completeness!

Let me verify this claim from CZ:

CZ Section 2.7 discusses embeddings of Cl into Int. Theorem 2.47 should be around there.

<br>

**CRITICAL FINDING**: If CZ Theorem 2.47 is correct (Int = Cl for the `{→, ⊥}$ fragment), then:
1. IntPropAxiom proves exactly the same formulas as PropositionalAxiom in the imp/bot language
2. The completeness proof for Int can follow the SAME structure as the classical completeness proof
3. The canonical model construction with MCS works perfectly

However, this would make the task somewhat trivial (just copy the classical proof with different axiom names). The task description specifically asks for Kripke semantics, prime theories, etc. So either:
(a) CZ Theorem 2.47 makes the task simpler than expected, OR
(b) The task is specifically about Kripke completeness (not bivalent completeness), which requires different infrastructure even if the derivable formulas are the same

Let me re-read the task description: "Prove soundness and completeness of HilbertInt with respect to intuitionistic Kripke semantics."

So the task IS specifically about Kripke semantics (`IValid`, `IForces`), not about bivalent truth-value semantics. Even if the same formulas are derivable, the semantics are different and the completeness proof structure is different.

**This means the completeness proof must show: `IValid phi ↔ Derivable IntPropAxiom phi`**

where `IValid$ is defined in Kripke.lean as:
```lean
def IValid (φ : PL.Proposition Atom) : Prop :=
  ∀ (World : Type v) [Preorder World] (val : World → Atom → Prop),
    (∀ {w w' : World} (p : Atom), w ≤ w' → val w p → val w' p) →
    ∀ w, IForces val (fun _ => False) w φ
```

This quantifies over ALL Kripke models (all preordered types, all upward-closed valuations).

So we need:
1. **Soundness**: `Derivable IntPropAxiom phi → IValid phi`
2. **Completeness**: `IValid phi → Derivable IntPropAxiom phi`

For completeness, the contrapositive: `¬Derivable → ¬IValid`, i.e., find a Kripke countermodel.

**Given that Int = Cl for imp/bot**: `¬Derivable IntPropAxiom phi$ iff `¬Derivable PropositionalAxiom phi$ (by CZ 2.47). And `¬Derivable PropositionalAxiom phi$ means there's a bivalent valuation falsifying `phi$. A single-world Kripke model with that valuation is also a Kripke countermodel.

So we could prove completeness by:
1. Use classical completeness (already proved)
2. Build a single-world Kripke model from the classical countermodel

But this misses the point of the task, which wants the CANONICAL Kripke model construction.

**FINAL ARCHITECTURE DECISION**: Use MCS with set inclusion as the canonical model. The completeness proof works because (as shown in our implication witness analysis) the truth lemma IS provable with MCS, and the completeness argument (finding MCS with `phi ∉ M$) works because in the imp/bot fragment, `⊬ phi$ implies `{neg phi}$ is consistent (since `⊢ neg neg phi$ implies `⊢ phi$ in the imp/bot fragment by CZ 2.47).

Wait, does CZ 2.47 actually hold? Let me verify quickly.

CZ 2.47 says: for `phi$ in `{→, ⊥}$: `⊢_Cl phi$ iff `⊢_Int phi$. 

Proof sketch (Int → Cl is trivial). For Cl → Int: Use Glivenko's theorem (`⊢_Cl phi$ iff `⊢_Int ¬¬phi$) and the fact that for `{→, ⊥}$-formulas, `¬¬phi ⊢_Int phi$ (provable by induction on phi in the `{→, ⊥}$ fragment).

Actually, this follows from: in the `{→, ⊥}$ fragment, Peirce's law is derivable in Int. Specifically, `((phi → psi) → phi) → phi$ is Int-derivable when `phi, psi$ are in `{→, ⊥}$? I'm not sure about this claim. Let me check:

For `phi = bot$: `((⊥ → psi) → ⊥) → ⊥ = neg neg (⊥ → psi)$. By EFQ, `⊥ → psi$ is derivable, so `neg neg (⊥ → psi)$ is derivable (double negation introduction). And actually `((⊥ → psi) → ⊥) → ⊥$ has a simpler proof: assume `(⊥ → psi) → ⊥$; we have `⊥ → psi$ (EFQ); MP gives `⊥$. So this is derivable in Int.

The general claim CZ 2.47 is a well-known result. Let me accept it and move forward.

**Consequence**: `¬Derivable IntPropAxiom phi$ implies `¬Derivable PropositionalAxiom phi$ implies (by classical completeness) there exists bivalent valuation falsifying `phi$. A single-world Kripke model using this valuation also falsifies `phi$. So the EXISTENCE of a countermodel is guaranteed.

But for the canonical model construction: if `⊬_Int phi$, then `⊬_Cl phi$ (since they're the same), so `{neg phi}$ is Cl-inconsistent iff `⊢_Cl neg neg phi$ iff `⊢_Int neg neg phi$ (by CZ 2.47 again). But `⊢_Int neg neg phi$ and `⊢_Int phi$ are equivalent (by CZ 2.47 since both are in `{→, ⊥}$). So `⊢_Int neg neg phi$ implies `⊢_Int phi$, contradicting `⊬_Int phi$. Therefore `{neg phi}$ IS consistent for IntPropAxiom!

**FINAL CONCLUSION**: `{neg phi}$ IS always consistent for IntPropAxiom when `⊬ phi$. The argument: if `{neg phi}$ inconsistent, then `⊢ neg neg phi$, and by CZ 2.47, `⊢ phi$, contradicting `⊬ phi$.

This means the completeness proof for Int with Kripke semantics can follow the EXACT same pattern as the classical completeness proof:

1. Assume `⊬ phi$
2. `{neg phi}$ is consistent (by the argument above, using CZ 2.47 or equivalently proving DNE for the imp/bot fragment)
3. Extend to MCS `M$, with `neg phi ∈ M$ hence `phi ∉ M$
4. By truth lemma: `phi$ not forced at `M$ in the canonical model
5. Canonical model is a Kripke model, so `¬IValid phi$

**However, we should NOT rely on CZ 2.47 as an axiom.** We should either prove it or find a self-contained argument. The self-contained argument for step 2 is:

**Lemma (int_neg_neg_elim_imp_bot)**: For any formula `phi$ in the `{→, ⊥}$ language (which is ALL our formulas since `PL.Proposition$ only has `atom, bot, imp$): `⊢_Int neg neg phi → phi$.

This can be proved by structural induction on `phi$:
- `phi = atom p$: `neg neg p → p$ requires Peirce/DNE, which is NOT derivable for atoms.

**WAIT** -- this contradicts CZ 2.47! `neg neg p → p$ is NOT derivable in Int for an atom `p$. So CZ 2.47 cannot be correct... unless I'm misreading it.

Let me re-read CZ 2.47 more carefully.

Actually, I realize I haven't actually read CZ 2.47. I was inferring it. The claim "Int = Cl for the `{→, ⊥}$ fragment" might refer to the `{→}$ fragment (without `⊥$), which is the purely implicational fragment. For the purely implicational fragment `{→}$, it IS known that classical and intuitionistic logics coincide.

But our formulas include `⊥$. With `⊥$, we can express negation (`¬p = p → ⊥$), and `¬¬p → p$ is NOT Int-derivable. So CZ 2.47, if it exists, does NOT apply to our full `{→, ⊥}$ language.

**CORRECTION**: The `{→, ⊥}$ fragment of Int is STRICTLY WEAKER than Cl. For example, `¬¬p → p$ (= `((p → ⊥) → ⊥) → p$) is Cl-derivable but not Int-derivable.

This means the earlier concern IS valid: `{neg phi}$ might be inconsistent for IntPropAxiom even when `⊬ phi$. Specifically, `phi = p$ (an atom): `¬¬p → p$ is not Int-derivable, but `{¬(¬¬p → p)}$ might be consistent or inconsistent.

Actually: `neg(neg neg p → p) = (((p → ⊥) → ⊥) → p) → ⊥$. Is `{(((p → ⊥) → ⊥) → p) → ⊥}$ consistent for Int?

If it were inconsistent: `[(((p → ⊥) → ⊥) → p) → ⊥] ⊢ ⊥$. By DT: `⊢ ((((p → ⊥) → ⊥) → p) → ⊥) → ⊥$, i.e., `⊢ ¬¬(¬¬p → p)$. This IS derivable in Int (by the general fact that `¬¬(¬¬A → A)$ is Int-derivable for any `A$).

So `{neg(neg neg p → p)}$ IS inconsistent for IntPropAxiom, but `neg neg p → p$ is NOT Int-derivable. This confirms the problem.

**SO THE PEIRCE-BASED `neg_consistent_of_not_derivable` DOES NOT WORK FOR Int.**

### THE ACTUAL CORRECT COMPLETENESS ARGUMENT FOR INT

We need a different way to find MCS with `phi ∉ M$ when `⊬ phi$.

**Method 1**: Direct model construction (bypass canonical model)

Since `⊬_Int phi$, there exists a BIVALENT valuation `v$ falsifying `phi$ (by classical completeness, which is already proved). The single-world Kripke model using `v$ is an intuitionistic model refuting `phi$, giving `¬IValid phi$.

This is clean and correct but "cheats" by using classical completeness.

**Method 2**: Use the canonical model but with a DIFFERENT starting point

Instead of `{neg phi}$, start from a set that is guaranteed consistent and excludes `phi$.

**Method 3**: Prove the "weak completeness" via the truth lemma + existence of non-containing MCS

We need a DIRECT proof that `⊬ phi$ implies some MCS doesn't contain `phi$.

**Lemma (not_derivable_iff_not_in_all_mcs)**: For IntPropAxiom: `⊬ phi$ iff exists MCS `M$ with `phi ∉ M$.

Forward direction: if some MCS doesn't contain `phi$, and `⊢ phi$, then by closed_under_derivation, `phi ∈ M$, contradiction.

Backward direction: if `⊬ phi$, we need MCS with `phi ∉ M$. 

**Proof of backward direction**: We prove the contrapositive: if every MCS contains `phi$, then `⊢ phi$.

Suppose `phi ∈ M$ for every IntPropAxiom-MCS `M$. Then `phi → ⊥ ∉ M$ for every MCS (by `prop_mcs_not_mem_of_neg$). By maximality, for every MCS, `insert (phi → ⊥) M$ is inconsistent. So for every MCS `M$, there exist `L ⊆ insert (phi → ⊥) M$ with `L ⊢ bot$...

This is getting complex. Let me try a cleaner approach.

**Approach via Gen-consistency**: Define "Gen-consistent" for IntPropAxiom as: a set `S$ is Gen-consistent if for every `psi$, `S ⊢ psi$ implies `psi ∈ S$.

Actually no. Let's use CZ's approach translated.

**CZ's approach (Theorem 2.43, completeness direction)**:

CZ uses tableaux `(Gamma, Delta)$. The completeness proof for a single formula `phi$ works with the set of subformulas `Sub(phi)$, which is finite. This gives the finite model property.

For STRONG completeness (Theorem 2.45 = our desired result), CZ uses the canonical model from Section 5.1 with ALL formulas.

The key is CZ Lemma 5.2: "`A ⊢_L phi$ iff for every maximal L-consistent tableau `(Gamma, Delta)$, `A ⊆ Gamma$ implies `phi ∈ Gamma$."

Backward: if `A ⊬_L phi$, the tableau `(A, {phi})$ is L-consistent. By Lindenbaum, extend to maximal `(Gamma, Delta)$ with `A ⊆ Gamma$ and `phi ∈ Delta$ (i.e., `phi ∉ Gamma$).

The tableau `(A, {phi})$ is L-consistent iff `A ⊬_L phi$. In our framework:
- "A ⊬ phi" means `Deriv IntPropAxiom A phi$ is false
- The "tableau `(A, {phi})$" corresponds to: extending `A$ to a set that excludes `phi$

The Lindenbaum lemma for TABLEAUX (not sets) extends a consistent tableau to a maximal consistent tableau. In CZ's setting, this uses enumeration of all formulas and at each step assigns a formula to either Gamma or Delta.

**In our set-based framework**, the equivalent of CZ's maximal consistent tableau `(Gamma, Delta)$ is: a set `Gamma$ such that:
- `Gamma$ is deductively closed (= theory)
- `Gamma$ is consistent
- For every formula `psi$: either `psi ∈ Gamma$ or... `psi ∉ Gamma$ (with specific properties)

But deductively-closed + consistent is NOT the same as MCS. MCS additionally requires that `insert phi S$ is inconsistent for every `phi ∉ S$. Deductively-closed + consistent is weaker.

**The key insight**: CZ's maximal consistent tableau IS equivalent to MCS in our framework, BUT CZ's CONSISTENCY is different from ours.

CZ's L-consistency of tableau `(Gamma, Delta)$: for no `psi_1, ..., psi_n ∈ Delta$ do we have `Gamma ⊢_L psi_1 ∨ ... ∨ psi_n$.

For a maximal tableau where `Gamma ∪ Delta$ = all formulas, this becomes: for no `psi_1, ..., psi_n ∉ Gamma$ do we have `Gamma ⊢_L psi_1 ∨ ... ∨ psi_n$.

In particular, `Gamma ⊬_L psi$ for any `psi ∉ Gamma$. This means `Gamma$ is deductively closed in the strong sense: if `Gamma ⊢ psi$ then `psi ∈ Gamma$.

And `Gamma ⊬_L bot$ (take `n=1, psi_1 = bot$ and note `bot ∈ Delta$ since `bot ∉ Gamma$ by this consistency).

Wait, is `bot ∈ Gamma$ or `bot ∈ Delta$? If `Gamma$ is consistent (doesn't derive `bot$), and `bot ∈ Gamma$, then `Gamma ⊢ bot$ (by assumption rule), contradicting consistency. So `bot ∈ Delta$ = `bot ∉ Gamma$.

So CZ's maximal consistent tableau gives a set `Gamma$ that is:
1. Deductively closed
2. Consistent (`bot ∉ Gamma$)
3. For every `psi$: `psi ∈ Gamma$ or `psi ∉ Gamma$ (tautology, no info here)
4. For `psi ∉ Gamma$: `Gamma ⊬ psi$ (this is stronger than MCS!)

Properties 1+2+4 together mean: `psi ∈ Gamma ↔ Gamma ⊢ psi$ (deductive closure gives `⊢ psi → ∈ Gamma$, property 4 gives `∉ Gamma → ⊬ psi$, i.e., `⊢ psi → ∈ Gamma$).

Now, our MCS has: `psi ∉ S → insert psi S$ inconsistent → there exist `L ⊆ insert psi S$ with `L ⊢ bot$ → by DT: `L' ⊢ psi → bot$ where `L' ⊆ S$ → `neg psi ∈ S$ (by closure).

This gives negation completeness but NOT deductive closure in general (for Int). MCS for Int is deductively closed by the general theorem `closed_under_derivation$ (which requires the deduction theorem, which Int has). So MCS for Int IS deductively closed.

And MCS has property 4? If `psi ∉ S$, can `S ⊢ psi$? If `S ⊢ psi$ and `S$ is deductively closed, then `psi ∈ S$, contradiction. So yes, `psi ∉ S → S ⊬ psi$ follows from deductive closure.

**So MCS for IntPropAxiom has all four properties**, matching CZ's maximal consistent tableau.

**Therefore, the Lindenbaum lemma in CZ (Lemma 5.1) corresponds EXACTLY to our `prop_lindenbaum$, and the canonical model construction works.**

**The remaining issue**: given `⊬ phi$, find MCS with `phi ∉ M$.

CZ Lemma 5.2 backward direction: if `⊬ phi$, the tableau `(∅, {phi})$ is consistent. Extending: we get maximal `(Gamma, Delta)$ with `phi ∈ Delta$, i.e., `phi ∉ Gamma$.

The tableau `(∅, {phi})$ being consistent means: `∅ ⊬ phi$, which is our assumption. In our framework, we need to show that `∅$ can be extended to MCS `M$ with `phi ∉ M$.

CZ's Lindenbaum extends the tableau `(∅, {phi})$. At each enumeration step for formula `psi$:
- If adding `psi$ to `Gamma$ keeps the tableau consistent with `phi ∈ Delta$, add `psi$ to `Gamma$
- Otherwise, add `psi$ to `Delta$

The constraint is: at every step, `Gamma ⊬ chi_1 ∨ ... ∨ chi_n$ for `chi_i ∈ Delta$. Crucially, `phi$ stays in `Delta$ throughout.

**In our set-based framework**: we need a MODIFIED Lindenbaum that extends a consistent set while EXCLUDING a specific formula.

**Lemma (lindenbaum_excluding)**: If `S$ is set-consistent for IntPropAxiom and `S ⊬ phi$ (meaning there's no derivation of `phi$ from any `L ⊆ S$), then there exists MCS `M ⊇ S$ with `phi ∉ M$.

**Proof**: Consider the collection of consistent supersets of `S$ that do not derive `phi$:
```
C = { T | S ⊆ T ∧ SetConsistent IntPropAxiom T ∧ ∀ L, (∀ x ∈ L, x ∈ T) → ¬Deriv IntPropAxiom L phi }
```

Apply Zorn's lemma to `C$ (ordered by inclusion). Chain unions preserve the non-derivability of `phi$ (same compactness argument as for consistency). So we get a maximal element `M$ of `C$.

Claim: `M$ is MCS. If `psi ∉ M$, then `insert psi M ∉ C$. So either `insert psi M$ is inconsistent (meaning `psi ∉ M$ triggers inconsistency, as in standard MCS) or `insert psi M$ derives `phi$. In the latter case, by DT: `M ⊢ psi → phi$.

Hmm, this doesn't immediately give MCS. The maximal elements of `C$ satisfy a weaker condition than MCS.

**Actually, a simpler approach**: 

**Theorem (mcs_excluding_nonderivable)**: If `S ⊬ phi$ (S does not derive `phi$ from IntPropAxiom), then there exists an IntPropAxiom-MCS `M ⊇ S$ with `phi ∉ M$.

**Proof**: The set `S ∪ {phi → bot}$ is consistent.

If not: `L ⊢ bot$ for `L ⊆ S ∪ {phi → bot}$. By DT: `L' ⊢ (phi → bot) → bot$ for `L' ⊆ S$. So `S ⊢ neg neg phi$.

We also need `S ⊬ phi$. Is it possible that `S ⊢ neg neg phi$ but `S ⊬ phi$? Yes, this can happen for Int (but not for Cl).

So `S ∪ {neg phi}$ might be inconsistent. Let's try yet another approach.

**Direct approach**: use the general fact that deductively closed consistent sets for Int are exactly CZ's Gamma-components of maximal consistent tableaux.

If `S$ is MCS and `phi ∈ S$, that's because Lindenbaum's enumeration-based construction added `phi$ at some step. If we use a DIFFERENT enumeration order (putting `phi$ LAST or ensuring it's tried for Delta first), we might get `phi ∉ M$.

But our Zorn-based Lindenbaum gives no control over which elements are added.

**THE ACTUALLY CORRECT AND SIMPLE APPROACH**:

Use the fact that for MCS `M$, `phi ∈ M ↔ S ⊢ phi$ for any set `S$ with `M$ being the MCS extending `S$... no, this is also not right.

OK, let me try to prove `mcs_excluding_nonderivable$ differently.

**Theorem**: For IntPropAxiom, if `⊬ phi$, there exists MCS `M$ with `phi ∉ M$.

**Proof by contradiction**: Suppose every MCS `M$ has `phi ∈ M$. 

Consider the set `S_0 = {psi | ⊢_Int psi}$ (all Int-theorems). This is consistent and deductively closed. Extend to MCS `M_0$. By assumption, `phi ∈ M_0$. 

For ANY consistent set `T$, extend to MCS `M_T$. By assumption, `phi ∈ M_T$.

Now, `phi ∉ S_0$ (since `⊬ phi$). So `S_0 ⊊ M_0$. 

Since `phi ∈ M_0$ and `phi ∉ S_0$, Lindenbaum added `phi$ during extension. At the point of adding, `S_i ∪ {phi}$ was consistent (where `S_i$ is the set at step i).

But we used Zorn, not enumeration. With Zorn, ALL maximal consistent supersets of `S_0$ are MCS. If `phi ∈ M$ for every such maximal `M$, then... 

Actually, `phi ∈ M$ for every MCS `M$ implies `phi$ is derivable. This is a standard result:

**Lemma**: `phi ∈ M$ for every IntPropAxiom-MCS iff `⊢_Int phi$.

Forward: clear (closed_under_derivation from empty context).

Backward: Suppose `⊬ phi$. Consider `T = {neg phi}$. If `T$ is consistent, extend to MCS `M$ with `neg phi ∈ M$, giving `phi ∉ M$.

If `T$ is inconsistent: `⊢ neg neg phi$. Now we need to derive `phi$ from `neg neg phi$ in Int. For the imp/bot fragment, this is NOT generally possible.

**KEY PROOF**: We can show that `⊢_Int neg neg phi → phi$ for CERTAIN shapes of `phi$ in the imp/bot language:

- If `phi = bot$: `neg neg bot → bot$ = `((bot → bot) → bot) → bot$ = `(top → bot) → bot$ = `neg top → bot$. Derivable by: assume `neg top$; we have `top$ (derivable); MP gives `bot$.

- If `phi = psi → chi$: `neg neg (psi → chi) → (psi → chi)$. Assume `neg neg (psi → chi)$ and `psi$. Need `chi$. 
  We have `neg neg (psi → chi)$, i.e., `((psi → chi) → bot) → bot$. 
  Also have `psi$. 
  If we could derive `neg neg chi$, then by IH, `chi$. 
  Assume `neg chi$ (= `chi → bot$). Then from `psi$ and `neg chi$, derive `psi → chi$? We need: given `psi → chi$ is derivable from `psi$ and `neg chi$... no, `psi → chi$ is not derivable from these.
  
  Instead: assume `(psi → chi) → bot$ (negation of conclusion). We have `psi$. We need `bot$. 
  We need `psi → chi$. Assume `psi$: need `chi$. We don't have `chi$.
  
  Actually, assume `chi → bot$. Build `psi → chi → bot$ (by composition or K). Then from `psi → chi → bot$ and `psi$ get `chi → bot$... this is circular.

  Better approach: 
  - Given: `((psi → chi) → bot) → bot$ and `psi$.
  - Want: `chi$.
  - Assume `chi → bot$ (toward deriving `bot$, which gives `chi$ by EFQ of `neg neg chi → chi$ if it works).
  - From `psi$ and `chi → bot$: build `psi → chi$ as follows? No, we can't.
  - From `chi → bot$ and `psi`: build `(psi → chi) → bot$? If we had `psi → chi → bot$... 
  - We have `chi → bot$. From `chi → bot$ derive `(psi → chi) → (psi → bot)$ (by implyS-like). Actually: `(psi → chi) → bot$ is not the same as `(psi → chi) → (psi → bot)$.
  
  Hmm, let me try: Given `chi → bot$, derive `(psi → chi) → bot$:
  - Assume `psi → chi$. We have `psi$ (outer assumption). By MP: `chi$. By MP with `chi → bot$: `bot$.
  - So from `chi → bot$ and `psi$, we derive `(psi → chi) → bot$.
  - Now MP with `((psi → chi) → bot) → bot$: `bot$.
  - So from `chi → bot$, `psi$, and `((psi → chi) → bot) → bot$: derive `bot$.
  - By DT on `chi → bot$: from `psi$ and `((psi → chi) → bot) → bot$: derive `(chi → bot) → bot$ = `neg neg chi$.
  - By IH for chi: `neg neg chi → chi$. So `chi$.

This induction works! Let me formalize:

**Theorem (int_dne_imp_bot)**: For every formula `phi$ in the `{imp, bot}$ language, `⊢_Int neg neg phi → phi$.

Proof by structural induction on `phi$:

- `phi = atom p$: Need `⊢ ((p → ⊥) → ⊥) → p$. This is NOT derivable in Int!

**FAILURE**: The induction fails at atoms. `neg neg p → p$ is not Int-derivable.

So my earlier claim that CZ 2.47 says Int = Cl for `{→, ⊥}$ is WRONG. The atom case breaks it.

**This means**: there exist formulas `phi$ in our language such that `⊬_Int phi$ but `⊢_Int neg neg phi$. For such `phi$, `{neg phi}$ is inconsistent, and we cannot use it to find an MCS excluding `phi$.

For example: `phi = ((p → ⊥) → ⊥) → p$ (which is `neg neg p → p$). We have `⊢_Int neg neg (neg neg p → p)$ but `⊬_Int neg neg p → p$.

**So how do we find MCS `M$ with `phi ∉ M$?**

### THE DEFINITIVE SOLUTION

After all this analysis, the issue is clear: for intuitionistic logic in the imp/bot fragment, MCS with set-inclusion accessibility gives a correct truth lemma (via the implication witness lemma), but the completeness argument fails at the final step (finding MCS excluding non-derivable formulas).

**The solution is to use PRIME THEORIES, not MCS.**

A **prime theory** for Int is a set `S$ satisfying:
1. **Theory**: deductively closed w.r.t. IntPropAxiom (if `L ⊆ S$ and `L ⊢ phi$ then `phi ∈ S$)
2. **Consistent**: `bot ∉ S$
3. **Prime/Disjunctive**: For all `phi, psi$: if `phi → psi ∈ S$ then `phi ∈ S$ or `psi ∈ S$... 
   no wait, that's not the disjunction property. The disjunction property for `∨$ is: if `phi ∨ psi ∈ S$ then `phi ∈ S$ or `psi ∈ S$. In imp/bot encoding: if `(phi → bot) → psi ∈ S$ then `phi → bot ∈ S$ (i.e., `phi ∉ S$ "morally") or `psi ∈ S$.

Actually, for the imp case of the truth lemma, what we need from the world is exactly the **implication witness property**:

> If `phi → psi ∉ S$, then there exists a world `T ≥ S$ with `phi ∈ T$ and `psi ∉ T$.

This is what we proved earlier for MCS. And this is what CZ's Hintikka condition HS/2 says.

So the truth lemma works with MCS. The issue is only the final step of completeness.

**The final step fix**: Instead of trying to find an MCS excluding `phi$, we observe that:

1. `⊬ phi$ means there is no `DerivationTree IntPropAxiom [] phi$.
2. Consider the empty set `∅$. It is consistent.
3. Extend `∅$ to MCS `M$.
4. Need `phi ∉ M$. 

If `phi ∈ M$: by deductive closure, there exists `L ⊆ M$ with `L ⊢ phi$. But this doesn't mean `⊢ phi$ (the list `L$ might be nonempty).

**So `phi ∈ M$ does NOT imply `⊢ phi$.** The formula `phi$ might be in `M$ because it's derivable from OTHER formulas in `M$, not from the empty context.

**This means**: we cannot conclude `⊢ phi$ from `phi ∈ M$ for a specific MCS `M$. We can only conclude `⊢ phi$ from `phi ∈ M$ for ALL MCS `M$.

So: `⊬ phi$ does NOT guarantee that there's an MCS excluding `phi$. The formula `phi$ might be in SOME MCS but not derivable from `∅$.

Wait... actually, `phi ∈ M$ for every MCS extending `∅$ IS possible even when `⊬ phi$? Let me think of an example.

`phi = neg neg p → p$ where `p$ is an atom. `⊬_Int phi$. Is `phi$ in every MCS extending `∅$?

An MCS `M$ satisfies negation completeness: `phi ∈ M$ or `neg phi ∈ M$. If `neg phi ∈ M$, then `phi ∉ M$ and we're done. If `phi ∈ M$ for all MCS... then `neg phi ∉ M$ for all MCS (by `prop_mcs_not_mem_of_neg$). But then `neg phi$ is not in any MCS, meaning `neg neg phi$ is in every MCS (by negation completeness). And `⊢ neg neg phi$? 

Actually, `neg neg (neg neg p → p)$ = `((neg neg p → p) → bot) → bot$. Is this Int-derivable?

Assume `(neg neg p → p) → bot$. Need `bot$. We need `neg neg p → p$. Assume `neg neg p$. Need `p$. We have `neg neg p$ and `(neg neg p → p) → bot$. From `neg neg p → p$ and the outer assumption, we'd get `bot$. But we need `p$ first, which we can't get from `neg neg p$ alone.

So `neg neg (neg neg p → p)$ is probably not Int-derivable (I'm not 100% sure without a formal check). If it's not, then `{neg(neg neg p → p)}$ is consistent, and we can extend it to MCS `M$ with `neg neg p → p ∉ M$.

If it IS derivable, then we're back to the problem.

Actually, I believe `neg neg (neg neg p → p)$ IS Int-derivable. Here's a sketch:

Assume `(neg neg p → p) → bot$ (toward deriving `bot$).
We need `neg neg p → p$ to get the contradiction.
Assume `neg neg p$ (toward deriving `p$).
Assume `p → bot$ (toward deriving `bot$ to get `p$ via... wait, we need EFQ).

OK let me try differently:
Assume `(neg neg p → p) → bot$.
Assume `neg neg p$.
We need `p$. But we can't get `p$ from `neg neg p$ in Int.
Instead, assume `neg p$ (= `p → bot$):
  From `neg p$ derive `neg neg p → p$: assume `neg neg p$; from `neg neg p$ and `neg p$: `neg neg p ⊢ (p → bot) → bot$ and `neg p = p → bot$, so MP gives `bot$; EFQ gives `p$. So `[neg p] ⊢ neg neg p → p$.
  From `neg p$ and `(neg neg p → p) → bot$: MP gives `bot$. Contradiction.
  
Wait, that's wrong. From `neg p$ we derived `neg neg p → p$, and from `(neg neg p → p) → bot$ and `neg neg p → p$, we get `bot$. So from `neg p$ and `(neg neg p → p) → bot$: `bot$.

By DT on `neg p$: `(neg neg p → p) → bot ⊢ neg p → bot$ = `neg neg p$.

So from `(neg neg p → p) → bot$ we derive `neg neg p$.

But we also derived: from `neg p$ and `(neg neg p → p) → bot$: `bot$.
And from `(neg neg p → p) → bot$ derive `neg neg p = (p → bot) → bot$.

From `(p → bot) → bot$ and `p → bot$: `bot$. But we don't have `p → bot$ (we derived `neg neg p$, not `neg p$).

Hmm. Let me redo:

From `(neg neg p → p) → bot$:
1. Assume `p → bot$ (= neg p).
2. From neg p, derive `neg neg p → p$: assume `neg neg p = (p → bot) → bot$; from `neg neg p$ and `neg p$: MP gives `bot$; EFQ gives `p$. So `[neg p] ⊢ neg neg p → p$.
3. From `neg neg p → p$ and `(neg neg p → p) → bot$: MP gives `bot$.
4. So `[(neg neg p → p) → bot, neg p] ⊢ bot$.
5. By DT: `[(neg neg p → p) → bot] ⊢ neg p → bot$ = `neg neg p$.
6. Now we have `[(neg neg p → p) → bot] ⊢ neg neg p$.
7. We also need `[(neg neg p → p) → bot] ⊢ neg neg p → p$ to get `bot$ via the outer assumption.
8. From step 6: `neg neg p$. We need `p$. We can't derive `p$ from `neg neg p$ in Int.

**STUCK**. So `neg neg (neg neg p → p)$ is NOT obviously Int-derivable.

But actually, let me reconsider. In step 6 we have `neg neg p$. We want to derive `neg neg p → p$ (to feed into the outer `(neg neg p → p) → bot$):

Assume `neg neg p$ (inner assumption). Need `p$.
- We have outer assumption `(neg neg p → p) → bot$.
- We have inner `neg neg p$.
- We can't get `p$ directly.

But: assume `p → bot$. Then by step 2-3 above: `bot$. So `[neg neg p, (neg neg p → p) → bot] ⊢ (p → bot) → bot$ = `neg neg p$. But we already have `neg neg p$!

We also have `[neg neg p, (neg neg p → p) → bot] ⊢ neg neg p$. And we have the assumption `neg neg p$ directly. So `(p → bot) → bot$ is derivable from these assumptions. But that doesn't give us `p$.

**Conclusion**: `neg neg (neg neg p → p)$ is NOT Int-derivable.

Wait, actually I think it IS. Let me try once more:

Goal: derive `((neg neg p → p) → bot) → bot$.
Assume `(neg neg p → p) → bot$. Need `bot$.
Need `neg neg p → p$. Assume `neg neg p$. Need `p$.

Alternative path: Don't try to derive `neg neg p → p$ directly. Instead:

From assumption `(neg neg p → p) → bot$:
- Derive `neg p$: assume `p$. Then `neg neg p → p$ is derivable (by K: `p → (neg neg p → p)$, MP). Then `(neg neg p → p) → bot$ and `neg neg p → p$ give `bot$. So `[p, (neg neg p → p) → bot] ⊢ bot$, giving `[(neg neg p → p) → bot] ⊢ p → bot$ = `neg p$.
- Derive `neg neg p$: from `neg p$ (proved above), `neg neg p → p$ is derivable (as in step 2 earlier: from `neg p$ and `neg neg p$, derive `bot$ then `p$ by EFQ). Then `(neg neg p → p) → bot$ gives `bot$. 

Wait, let me be more careful.

Step A: `[(neg neg p → p) → bot] ⊢ neg p$
  Proof: Assume `p$. 
    `p → (neg neg p → p)$ by implyK. MP: `neg neg p → p$.
    `(neg neg p → p) → bot$ and `neg neg p → p$: `bot$.
    So `[p, (neg neg p → p) → bot] ⊢ bot$.
    DT: `[(neg neg p → p) → bot] ⊢ p → bot$ = `neg p$. QED.

Step B: `[(neg neg p → p) → bot] ⊢ neg neg p$
  Proof: we have `neg p$ from step A. 
  Assume `neg neg p = (p → bot) → bot$. From `neg p$ and `neg neg p$: MP gives `bot$.
  Wait, that's the wrong direction. `neg neg p$ assumes `p → bot$ and gives `bot$. We HAVE `p → bot$ (= `neg p$ from step A).
  So `[(neg neg p → p) → bot] ⊢ neg p$ and we feed `neg p$ into `neg neg p$: but `neg neg p$ means `(p → bot) → bot$. We need `(p → bot) → bot$, i.e., assume `p → bot$ and derive `bot$. We have `neg p = p → bot$. So assuming `p → bot$ again just gives us what we already have.
  
  Actually, to derive `neg neg p$ from `neg p$: we need `(p → bot) → bot$. Assume `p → bot$. From `neg p$ and `p → bot$: these are the same thing! So... `neg neg p$ means `(p → bot) → bot$. To derive this from `neg p = p → bot$:
  
  Assume `p → bot$. Need `bot$. But `p → bot$ is just `neg p$, and we have no `p$ to apply it to. 
  
  So `neg neg p$ is NOT derivable from `neg p$! In fact, `neg p → neg neg p$ is NOT a theorem.
  
  Actually wait: `neg p → neg neg p$ would be `(p → bot) → ((p → bot) → bot) → bot$. Assume `p → bot$ and `(p → bot) → bot$. MP: `bot$. So `[(p → bot), (p → bot) → bot] ⊢ bot$. DT: `[p → bot] ⊢ ((p → bot) → bot) → bot$. DT: `⊢ (p → bot) → ((p → bot) → bot) → bot$. 

  YES! `neg p → neg neg p$ IS derivable (it's an instance of `A → (A → bot) → bot$, which is DNI and is Int-derivable).

  Wait, but I want `neg neg p$, not `neg p → neg neg p$. From step A I have `neg p$. So by MP with `neg p → neg neg p$ (which is derivable): `neg neg p$.

Step B corrected: `[(neg neg p → p) → bot] ⊢ neg neg p$
  From step A: `neg p$ (under the assumption `(neg neg p → p) → bot$).
  DNI: `neg p → neg neg p$ is Int-derivable.
  MP: `neg neg p$. QED.

Step C: Now I have both `neg neg p$ and `(neg neg p → p) → bot$ in my context. 
  I want `bot$. 
  I need `neg neg p → p$ to feed into `(neg neg p → p) → bot$.
  From `neg neg p$ I can't derive `p$ (no DNE in Int).
  So I can't derive `neg neg p → p$.

**STUCK AGAIN**.

Hmm, but wait. I have `neg neg p$ and `(neg neg p → p) → bot$. What if I use these differently?

From `neg neg p$: `(p → bot) → bot$.
From step A: `neg p = p → bot$.
These two together: `((p → bot) → bot)$ and `(p → bot)$: MP gives `bot$!

YES! `neg neg p$ and `neg p$ give `bot$!

Step C: `[(neg neg p → p) → bot] ⊢ bot$
  From step A: `neg p$ = `p → bot$.
  From step B: `neg neg p$ = `(p → bot) → bot$.
  MP: `bot$. QED!

So `⊢ ((neg neg p → p) → bot) → bot$, i.e., `⊢ neg neg (neg neg p → p)$.

**So `neg neg (neg neg p → p)$ IS Int-derivable!**

And `neg neg p → p$ is NOT Int-derivable. So `{neg(neg neg p → p)}$ is inconsistent but `neg neg p → p$ is not derivable. This confirms the problem scenario exists.

And the consequence: for `phi = neg neg p → p$, every IntPropAxiom-MCS contains `phi$ (as shown earlier: `neg neg phi$ derivable implies `neg phi$ can't be in any MCS, so `phi$ must be in every MCS by negation completeness). So the canonical model with MCS worlds validates `phi$, even though `phi$ is not Int-derivable. **The canonical model with MCS is NOT a model for Int!** It validates non-theorems!

**Wait** -- that can't be right. If the truth lemma holds (`IForces ... S phi ↔ phi ∈ S$) and `phi ∈ S$ for every MCS `S$, then `IForces ... S phi$ for every `S$, meaning `phi$ is valid in the canonical model. But `phi$ is NOT Int-derivable. So the canonical model is a Kripke model (preordered worlds, upward-closed valuation) that validates a non-theorem of Int. This is fine -- it just means the canonical model is not "universal" (it doesn't refute all non-theorems). The issue is that the COMPLETENESS proof requires finding a countermodel in the canonical model.

**THE DEFINITIVE ANSWER**: The canonical model with MCS worlds and set inclusion is a valid Kripke model that validates all Int-theorems (by soundness + truth lemma), but it may also validate non-theorems. So it cannot serve as the basis for a completeness proof BY ITSELF.

For completeness, we need EITHER:
1. A different class of worlds (prime theories / CZ tableaux)
2. A different construction for finding countermodels

Since the task description explicitly asks for prime theories, let's go with option 1.

---

## Definitive Architecture

### File 1: `IntSoundness.lean` (Straightforward)

**Imports**: `Kripke.lean`, `Derivation.lean`

**Main results**:
- `int_axiom_sound`: Each IntPropAxiom is IValid (3 cases: K, S, EFQ)
- `int_soundness`: If `DerivationTree IntPropAxiom Gamma phi` then `phi$ forced at every world of every Kripke model where all of Gamma is forced
- `int_soundness_derivable`: `Derivable IntPropAxiom phi → IValid phi`

The soundness proof mirrors `prop_soundness` from `Soundness.lean` but uses `IForces` instead of `Evaluate`. The key differences:
- `implyK` case: need to show `∀ w', w ≤ w' → IForces ... w' phi → IForces ... w' (psi.imp phi)$. Given `w ≤ w'$ and `IForces ... w' phi$: need `∀ w'', w' ≤ w'' → IForces ... w'' psi → IForces ... w'' phi$. Given `w' ≤ w''$ and `IForces ... w'' psi$: need `IForces ... w'' phi$. By persistence from `w' ≤ w''$ and `IForces ... w' phi$.
- `implyS` case: similar with universal quantification over accessible worlds
- `efq` case: need `∀ w', w ≤ w' → IForces ... w' bot → IForces ... w' phi$. Given `IForces ... w' bot = False$: contradiction.
- `modus_ponens` case: apply IH1 to get `∀ w' ≥ w, IForces w' phi → IForces w' psi$; apply with `w' = w$ (reflexivity) and IH2.

### File 2: `IntLindenbaum.lean` (Medium Complexity)

**Imports**: `DeductionTheorem.lean`, `MCS.lean`

This file defines prime theories and proves the prime theory extension lemma (Lindenbaum for prime theories).

**Definitions**:
```lean
/-- A set is an Int-theory if it is deductively closed and consistent. -/
def IntTheory (S : Set (PL.Proposition Atom)) : Prop :=
  PropSetConsistent IntPropAxiom S ∧
  ∀ (L : List (PL.Proposition Atom)) (φ : PL.Proposition Atom),
    (∀ x ∈ L, x ∈ S) → (propDerivationSystem IntPropAxiom).Deriv L φ → φ ∈ S

/-- A set is Int-prime if it is an Int-theory with the implication witness property. -/
def IntPrime (S : Set (PL.Proposition Atom)) : Prop :=
  IntTheory S ∧
  ∀ (φ ψ : PL.Proposition Atom), φ.imp ψ ∉ S →
    ∃ T, S ⊆ T ∧ IntPrime T ∧ φ ∈ T ∧ ψ ∉ T
```

**PROBLEM**: `IntPrime` is defined recursively (references itself). In Lean 4, this needs to be defined as an inductive predicate or use well-foundedness.

**Alternative: Define without self-reference by using MCS as the witness type.**

```lean
/-- A set is Int-prime if it is an Int-theory with the property that
for any phi → psi ∉ S, there exists an IntPropAxiom-MCS T ⊇ S with
phi ∈ T and psi ∉ T. -/
def IntPrime (S : Set (PL.Proposition Atom)) : Prop :=
  IntTheory S ∧
  ∀ (φ ψ : PL.Proposition Atom), φ.imp ψ ∉ S →
    ∃ T, S ⊆ T ∧ PropSetMaximalConsistent IntPropAxiom T ∧ φ ∈ T ∧ ψ ∈ T ∧ ψ ∉ T
```

Wait, but the truth lemma needs the WITNESS `T` to also be a prime theory (for the inductive hypothesis). If `T$ is just MCS, we're back to the problem that MCS validates non-theorems.

**THE REAL INSIGHT**: Every IntPropAxiom-MCS IS a prime theory! The implication witness lemma (proved earlier) shows exactly this:

If `S$ is IntPropAxiom-MCS and `phi → psi ∉ S$, then there exists IntPropAxiom-MCS `T ⊇ S$ with `phi ∈ T$ and `psi ∉ T$.

So MCS = prime theory for IntPropAxiom! The issue was NOT with the definition of worlds, but with the final step of completeness (finding MCS excluding a non-derivable formula).

**SOLUTION FOR COMPLETENESS FINAL STEP**: Use an INDIRECT argument.

Since `⊬ phi$, and Int has soundness for Kripke models, `phi$ is not valid in all Kripke models (otherwise soundness+completeness would be contradictory, but we're PROVING completeness, so we can't use it).

Actually, we CAN construct a direct countermodel:

**Direct countermodel construction**: Since `⊬ phi$, we can build a Kripke countermodel WITHOUT the canonical model. Use a recursively-constructed finite model based on the syntax of `phi$.

But this seems complex. Let me think of the cleanest approach.

**CLEANEST APPROACH**: Use the MCS canonical model AND prove that `phi ∉ M$ for some MCS `M$ using a SEMANTIC argument:

1. By soundness (proved in IntSoundness.lean): every derivable formula is IValid.
2. Contrapositive: if `phi$ is not IValid, then `phi$ is not derivable.
3. For completeness (contrapositive): if `phi$ is not derivable, `phi$ is not IValid.
4. We NEED: `phi$ not derivable → some Kripke model refutes `phi$.

For (4), we can use the trivially-constructed countermodel: the single-world model with valuation `v p = True$ for all `p$ forces everything; the model with `v p = False$ for all `p$ only forces formulas derivable from `∅$ in the minimal logic. Hmm, this needs more care.

**THE CLEANER APPROACH**: Prove completeness as `IValid phi → Derivable IntPropAxiom phi$ (the positive direction, not contrapositive).

Assume `IValid phi$. Assume `⊬ phi$. Derive contradiction.

Key lemma: `phi$ being Int-valid means it's forced in EVERY Kripke model, including the canonical model (MCS + set inclusion).

By truth lemma: in the canonical model, `phi$ forced at world `S$ iff `phi ∈ S$.

If `phi$ is valid in the canonical model: `phi ∈ S$ for every MCS world `S$.

We need: `phi ∈ S$ for every MCS implies `⊢ phi$. 

**Proof**: `phi ∈ S$ for every MCS. Suppose `⊬ phi$. Consider any finite `L ⊆ S$. The set `{neg phi}$: if consistent, extend to MCS `M$. Then `neg phi ∈ M$, so `phi ∉ M$ (by `prop_mcs_not_mem_of_neg$), contradicting `phi ∈ M$ for every MCS. So `{neg phi}$ is inconsistent: `[neg phi] ⊢ bot$, giving `⊢ neg neg phi$.

But `⊢ neg neg phi$ does NOT give `⊢ phi$ in Int. So we can't derive the contradiction this way.

**HOWEVER**: the canonical model DOES validate `phi$ (since `phi ∈ S$ for every MCS). So `IValid phi$ holds for the canonical model. But `IValid$ quantifies over ALL models, and we assumed `IValid phi$. So the canonical model validates `phi$. This is consistent -- there's no contradiction yet.

The contradiction should come from the truth lemma applied to a specific world: `IForces ... S phi ↔ phi ∈ S$. If `phi ∈ S$ for all `S$, then `IForces ... S phi$ for all `S$. This is fine. We need `phi ∉ S$ for some `S$ to get the contradiction.

**And `phi ∉ S$ for some `S$ follows from `⊬ phi$... but we just showed this might fail!**

So the positive-direction proof ALSO fails at the same point.

### THE ULTIMATE SOLUTION

After this extensive analysis, the fundamental issue is clear and well-known in the literature:

**For intuitionistic logic in the imp/bot-only fragment, the standard Henkin/canonical-model completeness proof using MCS requires an additional lemma showing that non-derivable formulas are excluded from some world.**

The standard solution in the literature (e.g., Troelstra & van Dalen) is one of:

**(A)** Use the FULL intuitionistic language (with primitive ∨ and ∧), where MCS has the disjunction property and the completeness proof works smoothly. Our imp/bot-only language makes this harder.

**(B)** Use CZ's tableau approach, which naturally handles the exclusion.

**(C)** Use a DIFFERENT kind of canonical model where worlds are "saturated sets" rather than MCS.

**(D)** For the imp/bot fragment specifically, use the CLASSICAL completeness theorem (already proved) and the inter-derivability of Int and Cl for this fragment (this is actually FALSE as we showed -- atoms break it).

**(E)** **Use the semantic argument**: construct a direct finite countermodel from the syntax of the formula being refuted. This is CZ Theorem 2.43's proof approach (finite model property for Int).

**RECOMMENDED APPROACH FOR THIS TASK: (F) The modified Lindenbaum approach**

We can prove a STRONGER Lindenbaum lemma that simultaneously extends a consistent set AND excludes a specific formula:

**Theorem (lindenbaum_excluding)**: If `S$ is PropSetConsistent for IntPropAxiom and the derivation system `propDerivationSystem IntPropAxiom` does NOT derive `phi$ from any list `L ⊆ S$, then there exists IntPropAxiom-MCS `M ⊇ S$ with `phi ∉ M$.

**Proof**: Apply Zorn to the collection:
```
C = { T : Set F | S ⊆ T ∧ PropSetConsistent IntPropAxiom T ∧ 
      ∀ L, (∀ x ∈ L, x ∈ T) → ¬(propDerivationSystem IntPropAxiom).Deriv L phi }
```

Chain unions preserve both consistency and non-derivability of `phi$ (by the usual compactness/finiteness argument). So Zorn gives a maximal element `M$ of `C$.

**Claim**: `M$ is MCS.
- `M$ is consistent (by definition of `C$).
- If `psi ∉ M$, then `insert psi M ∉ C$. Either:
  (a) `insert psi M$ is inconsistent → standard MCS condition, or
  (b) `insert psi M$ derives `phi$ from some `L ⊆ insert psi M$. By DT: `L' ⊢ psi → phi$ for `L' ⊆ M$. So `psi → phi ∈ M$ by deductive closure (using closed_under_derivation... wait, we need `M$ to be deductively closed first).

Actually, `M$ being the maximal element of `C$ does NOT automatically make it MCS. Let me reconsider.

**Alternative**: Define `C$ more carefully so maximal elements ARE MCS.

OR: prove `phi ∉ M$ differently.

For any MCS `M$: either `phi ∈ M$ or `phi ∉ M$. If we show `phi ∈ M → S ⊢ phi$ for any MCS `M ⊇ S$, then `S ⊬ phi$ would give `phi ∉ M$.

But `phi ∈ M$ for MCS `M ⊇ S$ does NOT imply `S ⊢ phi$ (phi might be derivable from other formulas in M that are not in S).

**APPROACH (G): Direct countermodel from IForces semantics**

Since `⊬ phi$, build a Kripke model directly. The simplest approach:

Consider the following Kripke model:
- World = Unit (single world)
- Preorder = trivial
- Valuation: `v () p = False` for all atoms `p`
- bot_forces = `fun _ => False`

In this model, `IForces v bf () psi$ for a formula `psi$:
- `IForces v bf () (atom p)$ = `v () p$ = `False`
- `IForces v bf () bot$ = `bf ()$ = `False`
- `IForces v bf () (phi.imp psi)$ = `IForces v bf () phi → IForces v bf () psi$

So in this model, `IForces v bf ()$ is exactly `Evaluate (fun _ => False)$. So `IForces ... () phi$ iff `Evaluate (fun _ => False) phi$.

If `phi$ is a tautology (classically valid), then `Evaluate (fun _ => False) phi$ is True. But `phi$ might not be a classical tautology! If `⊬_Int phi$, is `phi$ also not a classical tautology?

Not necessarily! `phi$ might be classically valid but not Int-derivable (e.g., `neg neg p → p$, which IS classically valid but not Int-derivable).

So the single-world model doesn't work for all cases.

**APPROACH (H): Two-world countermodel**

Build a two-world model `{w0, w1}$ with `w0 < w1$. Choose valuations to refute `phi$ at `w0$.

This requires analyzing the structure of `phi$, which is complex for a general formula.

**APPROACH (I): Canonical model with NON-STANDARD accessibility**

Instead of `S ⊆ T$ (set inclusion), use `S R T iff ∀ psi, phi → psi ∈ S → psi ∈ T$ (like the modal canonical relation but for implication instead of box). This doesn't make sense for propositional logic.

**APPROACH (J): Use the "algebra of theories" approach**

Define the Lindenbaum-Tarski algebra of Int and use its prime filters. This is algebraically clean but requires significant setup.

### FINAL RECOMMENDED APPROACH

After all this analysis, here is the recommended approach that is:
1. Correct
2. Follows the codebase patterns
3. Avoids introducing heavy new infrastructure
4. Follows CZ's proof structure

**Architecture**:

**Worlds = IntPropAxiom-MCS** (reuse existing `PropSetMaximalConsistent`)

**Accessibility = set inclusion** (`S.val ⊆ T.val`)

**Truth Lemma = works correctly** (via implication witness lemma, proved above)

**Completeness final step**: Instead of the Peirce-based `neg_consistent_of_not_derivable`, use a DIFFERENT argument for Int:

**Lemma (int_not_derivable_excluded_from_mcs)**: If `phi$ is not `Derivable IntPropAxiom`, then there exists IntPropAxiom-MCS `M$ with `phi ∉ M$.

**Proof**: Apply Zorn's lemma to the collection:
```
C_phi = { T : Set (PL.Proposition Atom) | 
          PropSetConsistent IntPropAxiom T ∧ phi ∉ T }
```
ordered by inclusion.

- `C_phi$ is nonempty: `∅ ∈ C_phi$ (empty set is consistent and `phi ∉ ∅$).
- Chain unions: if `{T_i}$ is a chain in `C_phi$, then `⋃ T_i$ is consistent (by the standard argument) and `phi ∉ ⋃ T_i$ (if `phi ∈ ⋃ T_i$, then `phi ∈ T_i$ for some `i$, contradicting `T_i ∈ C_phi$).
- So Zorn gives maximal `M ∈ C_phi$: `M$ is consistent, `phi ∉ M$, and `M$ is maximal among consistent sets not containing `phi$.

**Claim**: `M$ is MCS (i.e., PropSetMaximalConsistent IntPropAxiom M).

We need: for every `psi ∉ M$, `insert psi M$ is inconsistent.

Case 1: `psi = phi$. Then `insert phi M$ might be consistent or inconsistent. If consistent, then `insert phi M ∈ C_phi$ would need `phi ∉ insert phi M$, but `phi ∈ insert phi M$. So `insert phi M ∉ C_phi$. But we chose `M$ maximal in `C_phi$, and `insert phi M ⊋ M$, so `insert phi M ∉ C_phi$ means either `insert phi M$ is inconsistent OR `phi ∈ insert phi M$ (the latter is trivially true). So maximality in `C_phi$ does NOT force `insert phi M$ to be inconsistent.

**THIS APPROACH FAILS**: Maximal elements of `C_phi$ are not necessarily MCS.

**APPROACH (K): Modified Zorn argument with "phi-excluding-MCS"**

Define a phi-excluding-MCS as: a set `M$ that is consistent, `phi ∉ M$, and for every `psi ∉ M$ with `psi ≠ phi$: `insert psi M$ is inconsistent OR `insert psi M$ derives `phi$.

This is non-standard and complex.

**APPROACH (L): Use `{neg phi}$ when possible, direct model otherwise**

Since `{neg phi}$ is consistent iff `⊬ neg neg phi$:
- If `⊬ neg neg phi$: `{neg phi}$ is consistent, extend to MCS, get `phi ∉ M$. Use canonical model.
- If `⊢ neg neg phi$ but `⊬ phi$: need a different countermodel. Build one from the classical countermodel.

For the second case: `⊬ phi$ but `⊢ neg neg phi$. Since `⊢ neg neg phi$ and Int has soundness for Kripke models, `neg neg phi$ is IValid. But `phi$ is not derivable, so (by what we want to prove) `phi$ is not IValid. So there exists a Kripke model refuting `phi$. We need to CONSTRUCT this model.

The formula `phi$ is not a classical tautology either (if it were, it would be Int-derivable since... wait, that's what CZ 2.47 would say, but we showed CZ 2.47 is false for atoms). Actually, `neg neg p → p$ IS a classical tautology but is NOT Int-derivable. So `phi$ CAN be a classical tautology.

If `phi$ is a classical tautology: it's true in every single-world Kripke model. But it might fail in a multi-world model. The canonical model with MCS worlds doesn't help (phi in every MCS). We need to build a specific multi-world countermodel.

**APPROACH (M): THE SIMPLEST CORRECT APPROACH**

**Insight**: We can bypass the issue entirely by reformulating the completeness theorem.

Instead of "IValid phi → Derivable IntPropAxiom phi", prove the STRONG completeness:

"If `Gamma ⊢_Int phi$ fails, then there exists a Kripke model and world `w$ such that `w |= Gamma$ but `w ⊭ phi$."

The starting point is `Gamma ⊬ phi$. Consider the set `Gamma ∪ {neg phi}$... same issue.

OR: prove the completeness via:

**Theorem**: `Derivable IntPropAxiom phi ↔ IValid phi$

Using the equivalence `IntPropAxiom ⊢ phi ↔ PropositionalAxiom ⊢ phi$ (which holds for imp/bot formulas) and `Tautology phi ↔ IValid phi$ (which holds because any bivalent valuation is a single-world Kripke model and vice versa).

Wait: `Tautology phi → IValid phi$ is true (any tautology is Kripke-valid, since single-world Kripke models correspond to bivalent valuations). And `IValid phi → Tautology phi$ is also true (specialize to single-world models).

So `Tautology phi ↔ IValid phi$ for imp/bot formulas!

And we already have `Tautology phi ↔ Derivable PropositionalAxiom phi$ (from Completeness.lean).

So we need: `Derivable IntPropAxiom phi ↔ Derivable PropositionalAxiom phi$ for imp/bot formulas.

The `→$ direction is trivial (IntPropAxiom ⊆ PropositionalAxiom).

The `←$ direction is: classical theorems of imp/bot are intuitionistic theorems. This is the "subsystem" direction. For the imp/bot fragment, is this true?

`neg neg p → p$ is a classical theorem. Is it an Int theorem? NO! So `Derivable PropositionalAxiom (neg neg p → p)$ is true but `Derivable IntPropAxiom (neg neg p → p)$ is false.

So `Derivable IntPropAxiom phi ↔ Derivable PropositionalAxiom phi$ is FALSE.

And `Tautology phi ↔ IValid phi$ for imp/bot formulas: let's check. `IValid (neg neg p → p)$? The formula `((p → ⊥) → ⊥) → p$ should fail in some Kripke model. Consider two worlds `w0 ≤ w1$, `v w0 p = False, v w1 p = True$. At `w0$: `IForces v bf w0 (neg neg p → p)$ means: for all `w' ≥ w0$, `IForces v bf w' (neg neg p)$ implies `IForces v bf w' p$. Take `w' = w0$: `IForces v bf w0 (neg neg p)$ means `IForces v bf w0 ((p → ⊥) → ⊥)$ = `∀ w'' ≥ w0, (∀ w''' ≥ w'', IForces v bf w''' p → False) → False$. At `w'' = w0$: `(∀ w''' ≥ w0, IForces v bf w''' p → False) → False$. But `IForces v bf w1 p = True$, so `∀ w''' ≥ w0, IForces v bf w''' p → False$ is False (fails at w1). So the inner part `(... → False) → False$ is `False → False$ = True. Hmm wait:

`∀ w''' ≥ w0, IForces v bf w''' p → False$: at `w''' = w1$: `True → False$ = `False$. So the universal is False. Then `False → False$ = True. So `IForces v bf w0 (neg neg p)$ = True.

But `IForces v bf w0 p$ = `v w0 p$ = False. So `IForces v bf w0 (neg neg p → p)$ requires: given `IForces v bf w0 (neg neg p)$ (True), conclude `IForces v bf w0 p$ (False). This fails!

Wait, `IForces v bf w0 (neg neg p → p)$ = `∀ w' ≥ w0, IForces v bf w' (neg neg p) → IForces v bf w' p$. At `w' = w0$: True → False = False. So `IForces v bf w0 (neg neg p → p)$ = False.

So `neg neg p → p$ is NOT IValid. 

And `Tautology (neg neg p → p)$? `Evaluate v (neg neg p → p)$ = `Evaluate v ((p → ⊥) → ⊥) → Evaluate v p$ = `((v p → False) → False) → v p$. If `v p = False$: `(True → False) → False$ = `False → False$ = True. So `True → False$ = False. Wait: `v p = False$. Then `(v p → False) = (False → False) = True$. Then `(True → False) = False$. Then `(False → v p) = (False → False) = True$. So `Evaluate v (neg neg p → p) = True$ when `v p = False$!

Wait, let me recalculate. `Evaluate v ((p → ⊥) → ⊥) → p)$:
- `Evaluate v (p → ⊥)$ = `Evaluate v p → False$ = `v p → False$
- `Evaluate v ((p → ⊥) → ⊥)$ = `(v p → False) → False$ = `¬¬(v p)$
- `Evaluate v (((p → ⊥) → ⊥) → p)$ = `¬¬(v p) → v p$

If `v p = True$: `True → True$ = True.
If `v p = False$: `¬¬False → False$ = `(¬False) → False$... `¬False = True$. `¬True = False$. So `¬¬False = ¬True = False$. So `False → False$ = True.

So `Evaluate v (neg neg p → p)$ = True for all `v$! So `neg neg p → p$ IS a tautology!

But `neg neg p → p$ is NOT IValid (we showed a Kripke countermodel above).

**So `Tautology phi ↔ IValid phi$ is FALSE for imp/bot formulas!**

Tautology is STRICTLY STRONGER than IValid: every IValid formula is a tautology (specialize to single-world models), but not every tautology is IValid.

This is exactly the difference between classical and intuitionistic validity.

Great, so the picture is:
- `IValid phi ⊆ Tautology phi$ (IValid implies tautology)
- `Derivable IntPropAxiom phi ⊆ IValid phi$ (soundness, to be proved)
- `IValid phi ⊆ Derivable IntPropAxiom phi$ (completeness, to be proved)
- `Derivable IntPropAxiom phi ⊂ Derivable PropositionalAxiom phi = Tautology phi$ (strict containment)

So completeness is: `IValid phi → Derivable IntPropAxiom phi$.

And the DEFINITIVE approach for the completeness proof:

**Use `{neg phi}$ because `⊬ phi$ implies `{neg phi}$ is consistent.**

Wait, does it? If `⊬ phi$, is `{neg phi}$ consistent?

`{neg phi}$ inconsistent means `[neg phi] ⊢ bot$, i.e., `⊢ neg neg phi$. 

If `⊢ neg neg phi$ then by soundness `neg neg phi$ is IValid. If `phi$ is also IValid, then... we'd need to show `IValid (neg neg phi) ∧ IValid phi$ leads to contradiction, which it doesn't (both could be IValid).

Actually, the completeness proof assumes `IValid phi$ and wants to show `⊢ phi$. Contrapositive: `⊬ phi → ¬IValid phi$.

If `⊬ phi$ and `⊢ neg neg phi$: then `neg neg phi$ is IValid (by soundness). Does `IValid (neg neg phi) ∧ ¬IValid phi$ lead to contradiction? No! `neg neg phi$ being IValid means `phi$ is "Kripke consistent" (forced somewhere), but `phi$ need not be IValid.

So we can't derive a contradiction this way.

**The actual question**: if `⊬ phi$, is `{neg phi}$ always IntPropAxiom-consistent?

If `[neg phi] ⊢ bot$: `⊢ neg neg phi$. By soundness: `neg neg phi$ is IValid. Now, is `phi$ still IValid? We're doing contrapositive, so we assumed `⊬ phi$ (not `IValid phi$).

Hmm, let me think about this differently. We want: `IValid phi → ⊢ phi$. We prove: `⊬ phi → ∃ model refuting phi$.

Given `⊬ phi$:
- If `{neg phi}$ is consistent: extend to MCS `M$, `neg phi ∈ M$, `phi ∉ M$. Truth lemma: `phi$ not forced at `M$ in canonical model. Canonical model is a valid Kripke model. So `phi$ is not IValid.
- If `{neg phi}$ is inconsistent: `⊢ neg neg phi$. We CANNOT find MCS excluding `phi$ via this route. We need a DIFFERENT countermodel.

**For the second case**: `⊢ neg neg phi$ but `⊬ phi$. We need to construct a Kripke model where `phi$ is not forced at some world.

**Observation**: the formula `neg neg phi → phi$ is NOT IValid (since `⊬ neg neg phi → phi$ and by what we're trying to prove, this should imply `¬IValid(neg neg phi → phi)$... but we haven't proved completeness yet, so we can't use it).

**But we CAN construct a countermodel for `phi$ directly**: 

Since `⊬ phi$ in Int, but `⊢ phi$ in Cl (because `⊢ neg neg phi$ in Int implies `⊢ neg neg phi$ in Cl implies `⊢ phi$ in Cl by DNE), we have `Tautology phi$ (classical completeness) but `¬IValid phi$. So there IS a Kripke model refuting `phi$, but it's not a single-world model (single-world models are classical).

We need to CONSTRUCT this multi-world model. The canonical model doesn't work (all MCS contain `phi$).

**KEY REALIZATION**: The issue only arises when `⊢ neg neg phi$ but `⊬ phi$. This means `phi$ is "almost derivable" -- its double negation is derivable. The countermodel must be a multi-world model.

**SIMPLEST FIX**: Use a **two-tier** canonical model. Define two kinds of worlds:
- Type 1: MCS containing `neg phi$ (if any exist)
- Type 2: MCS containing `phi$ (if some don't contain `neg phi$)

If Type 1 exists, we're done (phi not in that world).

If Type 1 doesn't exist (all MCS contain `phi$ and `neg neg phi$), we need a DIFFERENT construction.

**APPROACH (N): THE DEFINITIVE LINDENBAUM WITH EXCLUSION**

I believe the correct approach is a modified Lindenbaum lemma that builds a deductively-closed consistent set (NOT necessarily an MCS) that excludes `phi$. This is CZ's approach: the worlds are theories (deductively closed consistent sets), not necessarily MCS.

**Lemma (theory_excluding)**: If `⊬ phi$, there exists a deductively closed consistent set `T$ for IntPropAxiom with `phi ∉ T$.

**Proof**: Let `T = {psi | ⊢_Int psi}$ (all Int-theorems). Then:
- `T$ is deductively closed: if `L ⊆ T$ and `L ⊢ psi$, then by transitivity of derivation, `⊢ psi$, so `psi ∈ T$.
- `T$ is consistent: if `⊢ bot$, then by EFQ `⊢ phi$ for all `phi$, contradicting `⊬ phi$ for specific `phi$.
- `phi ∉ T$: because `⊬ phi$.

But `T$ is NOT an MCS (it's the minimum deductively closed consistent set). The canonical model using theories (not MCS) needs to work.

**Modified canonical model**: Worlds = all deductively closed consistent sets for IntPropAxiom. Accessibility = set inclusion. Valuation = atom membership.

**Problem with truth lemma**: For this to work, we need the implication witness property for deductively closed consistent sets (not just MCS):

If `S$ is a deductively closed consistent set and `phi → psi ∉ S$, then there exists a deductively closed consistent set `T ⊇ S$ with `phi ∈ T$ and `psi ∉ T$.

**Proof**: 
1. `S ∪ {phi}$ is consistent (same EFQ composition argument as before).
2. Let `T_0 = {chi | ∃ L ⊆ S ∪ {phi}, L ⊢ chi}$ (deductive closure of `S ∪ {phi}$).
3. `T_0$ is deductively closed by construction.
4. `T_0$ is consistent (because `S ∪ {phi}$ is consistent and deductive closure preserves consistency).
5. `phi ∈ T_0$ (derivable from `S ∪ {phi}$ by assumption rule).
6. `psi ∉ T_0$? We need: there is no `L ⊆ S ∪ {phi}$ with `L ⊢ psi$.

Is `psi ∉ T_0$? Suppose `L ⊢ psi$ for `L ⊆ S ∪ {phi}$. By DT (if `phi ∈ L$): `L' ⊢ phi → psi$ for `L' ⊆ S$. Since `S$ is deductively closed: `phi → psi ∈ S$, contradicting our assumption.

If `phi ∉ L$: `L ⊆ S$, so `psi ∈ S$ by deductive closure. But then `phi → psi ∈ S$ (by implyK: `psi → (phi → psi)$ and closure). Contradiction.

So `psi ∉ T_0$!

**THIS WORKS!** The implication witness holds for deductively closed consistent sets. And we don't need MCS at all!

**REVISED CANONICAL MODEL**:
- Worlds = deductively closed consistent sets for IntPropAxiom
- Accessibility = set inclusion
- Valuation = atom membership
- bot_forces = fun _ => False

**Truth Lemma**: `IForces v bf S phi ↔ phi ∈ S$ for deductively closed consistent `S$.

**Atom case**: `IForces v bf S (atom p) = v S p = (atom p ∈ S) ↔ atom p ∈ S$. Trivial.

**Bot case**: `IForces v bf S bot = False ↔ bot ∈ S$. Forward: False → anything. Backward: if `bot ∈ S$, then `S$ derives `bot$ (by assumption rule), contradicting consistency. So `bot ∉ S$, giving `bot ∈ S → False$.

**Imp case backward**: `phi → psi ∈ S → IForces v bf S (phi.imp psi)$. Need: `∀ T ⊇ S$ (dccs), `IForces v bf T phi → IForces v bf T psi$. Given `T ⊇ S$: `phi → psi ∈ T$ (by `S ⊆ T$). By IH: `IForces v bf T phi → phi ∈ T$. Then `phi ∈ T$ and `phi → psi ∈ T$ give `psi ∈ T$ (by deductive closure, via MP). By IH: `psi ∈ T → IForces v bf T psi$.

**Imp case forward**: `IForces v bf S (phi.imp psi) → phi → psi ∈ S$. Contrapositive: `phi → psi ∉ S → ¬IForces v bf S (phi.imp psi)$. By implication witness: exists dccs `T ⊇ S$ with `phi ∈ T$ and `psi ∉ T$. By IH backward: `IForces v bf T phi$. By IH forward: `psi ∉ T → ¬IForces v bf T psi$. So `T$ is a witness.

**Completeness**: `⊬ phi$. Let `T_0 = {psi | ⊢ psi}$ (Int-theorems). `T_0$ is dccs with `phi ∉ T_0$. By truth lemma: `¬IForces v bf T_0 phi$. So canonical model refutes `phi$ at `T_0$. Hence `¬IValid phi$.

**THIS IS THE CORRECT AND COMPLETE PROOF.**

---

## Summary of Definitive Architecture

### File 1: `Metalogic/IntSoundness.lean`

**Imports**: `Kripke.lean`, `Derivation.lean`

**Definitions**: None new.

**Theorems**:
- `int_axiom_sound`: Each IntPropAxiom axiom is IValid
- `int_soundness`: Soundness for DerivationTree IntPropAxiom (by induction on tree)
- `int_soundness_derivable`: Derivable IntPropAxiom phi → IValid phi

### File 2: `Metalogic/IntLindenbaum.lean`

**Imports**: `DeductionTheorem.lean`, `MCS.lean` (or directly `Consistency.lean`)

**Definitions**:
```lean
/-- A set is a deductively closed consistent set (dccs) for IntPropAxiom. -/
def IntDCCS (S : Set (PL.Proposition Atom)) : Prop :=
  PropSetConsistent IntPropAxiom S ∧
  ∀ (L : List (PL.Proposition Atom)) (φ : PL.Proposition Atom),
    (∀ x ∈ L, x ∈ S) →
    (propDerivationSystem IntPropAxiom).Deriv L φ → φ ∈ S
```

**Theorems**:
- `int_dccs_bot_not_mem`: bot ∉ S for IntDCCS S
- `int_dccs_imp_property`: imp closure for IntDCCS
- `int_deductive_closure`: The deductive closure of a consistent set is IntDCCS
- `int_deductive_closure_consistent`: Deductive closure preserves consistency
- `int_imp_witness`: The implication witness lemma for IntDCCS
- `int_theorems_dccs`: The set of Int-theorems {psi | ⊢ psi} is IntDCCS

### File 3: `Metalogic/IntCompleteness.lean`

**Imports**: `Kripke.lean`, `IntSoundness.lean`, `IntLindenbaum.lean`

**Definitions**:
```lean
/-- A canonical world for intuitionistic logic is a dccs for IntPropAxiom. -/
def IntCanonicalWorld := { S : Set (PL.Proposition Atom) // IntDCCS S }

/-- The canonical Kripke model for intuitionistic logic.
Worlds = IntDCCS, accessibility = set inclusion, valuation = atom membership. -/
-- Defined using IForces with appropriate v and bot_forces
```

**Theorems**:
- `int_canonical_preorder`: IntCanonicalWorld with S.val ⊆ T.val is a preorder
- `int_canonical_valuation_upward_closed`: Atom membership is upward closed
- `int_truth_lemma`: IForces v bf S phi ↔ phi ∈ S.val for IntCanonicalWorld S
- `int_completeness`: IValid phi → Derivable IntPropAxiom phi
- `int_soundness_completeness`: IValid phi ↔ Derivable IntPropAxiom phi

---

## Tactic Survey Results

| Goal | Tactic | Expected Result | Notes |
|------|--------|--------|-------|
| Soundness axiom cases | intro/exact | success | Pattern match on axiom, use persistence + IForces unfolding |
| Soundness modus_ponens | exact (IH application) | success | Apply IH1 at w with le_refl, feed IH2 result |
| Truth lemma atom | constructor/exact | success | Trivial bidirectional |
| Truth lemma bot | constructor/exact + absurd | success | Follows bot ∉ S |
| Truth lemma imp (backward) | intro + IH | success | Use S ⊆ T, imp closure, IH |
| Truth lemma imp (forward) | by_contra + imp_witness | medium | Key lemma is imp_witness |
| Imp witness consistency | by_contra + DT + EFQ composition | medium | Need `neg phi ⊢ phi → psi` derivation |
| Imp witness psi exclusion | closure + absurd | success | implyK gives `psi → (phi → psi)`, contradiction |
| Completeness | by_contra + truth_lemma | success | Use theorems-dccs as starting world |

---

## Key Derivations Needed

### Derivation 1: neg phi implies phi → psi (via EFQ composition)

```
-- Goal: [phi → bot] ⊢ phi → psi
-- Step 1: EFQ axiom: ⊢ bot → psi
-- Step 2: implyK: ⊢ (bot → psi) → (phi → (bot → psi))
-- Step 3: MP steps 1,2: ⊢ phi → (bot → psi)
-- Step 4: implyS: ⊢ (phi → (bot → psi)) → ((phi → bot) → (phi → psi))
-- Step 5: MP steps 3,4: ⊢ (phi → bot) → (phi → psi)
-- Step 6: MP with assumption [phi → bot]: [phi → bot] ⊢ phi → psi
```

### Derivation 2: psi implies phi → psi (via implyK)

```
-- Goal: [psi] ⊢ phi → psi
-- Step 1: implyK axiom: ⊢ psi → (phi → psi)
-- Step 2: MP with assumption [psi]: [psi] ⊢ phi → psi
```

---

## Import Dependencies

### IntSoundness.lean
```lean
import Cslib.Logics.Propositional.Semantics.Kripke
import Cslib.Logics.Propositional.ProofSystem.Derivation
```

### IntLindenbaum.lean
```lean
import Cslib.Logics.Propositional.Metalogic.DeductionTheorem
-- May also need: import Cslib.Logics.Propositional.Metalogic.MCS (for reuse)
```

### IntCompleteness.lean
```lean
import Cslib.Logics.Propositional.Metalogic.IntSoundness
import Cslib.Logics.Propositional.Metalogic.IntLindenbaum
import Cslib.Logics.Propositional.Semantics.Kripke
```
