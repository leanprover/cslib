# Research Report: Task #90

**Task**: Expand Modal Cube Proof Systems and Metalogic
**Date**: 2026-06-10
**Session**: sess_1749599400_orchestrate

## Summary

This report provides a comprehensive analysis of the work needed to bring the modal logic infrastructure to parity with the Temporal/ module. The current modal module has a complete metalogic pipeline for S5 only; the 14 other systems defined in Cube.lean are semantics-only. Expanding to K, T, D, S4 (and eventually B, K45, etc.) requires: (1) parameterizing `ModalAxiom` so that each system selects its own subset of axioms, (2) creating `Instances.lean` to bridge the concrete `DerivationTree` to the abstract `ProofSystem` typeclass hierarchy, (3) establishing soundness and completeness per-system via canonical model constructions with appropriate frame conditions, and (4) integrating the untracked `HilbertDerivedRules.lean` into the build. A typeclass-based architecture (extending the existing `ModalHilbert` hierarchy with intermediate classes like `ModalTHilbert`, `ModalDHilbert`, `ModalS4Hilbert`) is recommended over an enum-based parameterization.

## 1. Architecture Analysis: Parameterizing Modal Axiom Sets

### Current State

`ModalAxiom` (in `Metalogic/DerivationTree.lean`) is a monolithic inductive with 8 constructors (4 propositional + 4 modal: K, T, 4, B), hardcoded to S5. The `DerivationTree` uses `ModalAxiom` directly in its `ax` constructor. This means every derivation implicitly has access to all S5 axioms.

### Option A: Typeclass-Based Hierarchy (RECOMMENDED)

Extend the existing typeclass hierarchy in `ProofSystem.lean`:

```
ModalHilbert S           -- ClassicalHilbert + Necessitation + HasAxiomK
  |
  +-- ModalTHilbert S    -- + HasAxiomT
  |     |
  |     +-- ModalS4Hilbert S  -- + HasAxiom4
  |           |
  |           +-- ModalS5Hilbert S  -- + HasAxiomB (ALREADY EXISTS)
  |
  +-- ModalDHilbert S    -- + HasAxiomD
```

**Advantages**:
- Follows the established pattern from the propositional hierarchy (`MinimalHilbert -> IntuitionisticHilbert -> ClassicalHilbert`)
- Individual axiom typeclasses (`HasAxiomT`, `HasAxiom4`, `HasAxiomB`, `HasAxiom5`, `HasAxiomD`) already exist in `ProofSystem.lean`
- Generic theorems in `Foundations/Logic/Theorems/Modal/` already work against `[ModalHilbert S]` and `[ModalS5Hilbert S]`
- Can add intermediate classes without changing existing code
- Tag types (`Modal.HilbertK`, `Modal.HilbertS5`) already exist; just need to add `Modal.HilbertT`, `Modal.HilbertD`, `Modal.HilbertS4`

**Required new bundled classes** (add to `ProofSystem.lean`):

```lean
class ModalTHilbert (S : Type*) [HasBot F] [HasImp F] [HasBox F]
    [InferenceSystem S F]
    extends ModalHilbert S (F := F), HasAxiomT S (F := F)

class ModalDHilbert (S : Type*) [HasBot F] [HasImp F] [HasBox F]
    [InferenceSystem S F]
    extends ModalHilbert S (F := F), HasAxiomD S (F := F)

class ModalS4Hilbert (S : Type*) [HasBot F] [HasImp F] [HasBox F]
    [InferenceSystem S F]
    extends ModalTHilbert S (F := F), HasAxiom4 S (F := F)
```

**Required new tag types** (add to `ProofSystem.lean`):

```lean
opaque Modal.HilbertT : Type := Empty
opaque Modal.HilbertD : Type := Empty
opaque Modal.HilbertS4 : Type := Empty
```

(Note: `Modal.HilbertK` and `Modal.HilbertS5` already exist.)

**Impact on ModalS5Hilbert**: The existing `ModalS5Hilbert` extends `ModalHilbert` directly with T, 4, B. After the refactor it should extend `ModalS4Hilbert` with B. This is a breaking change but affects only the Bimodal Instances.lean and the Modal Instances.lean (which doesn't exist yet). The change is:

```lean
-- BEFORE:
class ModalS5Hilbert extends ModalHilbert S, HasAxiomT S, HasAxiom4 S, HasAxiomB S

-- AFTER:
class ModalS5Hilbert extends ModalS4Hilbert S, HasAxiomB S
```

This refactoring is straightforward because the `extends` mechanism in Lean 4 handles diamond inheritance correctly. All existing code using `[ModalS5Hilbert S]` continues to work since the fields are the same.

### Option B: Parameterized ModalAxiom with Axiom Set

Define a type-level axiom set selector:

```lean
inductive ModalSystem | K | T | D | S4 | S5

inductive ModalAxiom (sys : ModalSystem) : Proposition Atom -> Prop where
  | implyK ... -- always available
  | modalK ... -- always available
  | modalT ... -- available when sys ∈ {T, S4, S5}
  -- etc.
```

**Disadvantages**:
- Requires a major rewrite of `DerivationTree`, `DeductionTheorem`, `MCS`, `Soundness`, `Completeness`
- Does not integrate with the typeclass hierarchy
- Cannot share generic theorems across systems at compile time
- No established pattern in the codebase

**Verdict**: Reject Option B. The typeclass approach aligns with the existing architecture and requires minimal refactoring of existing code.

### Option C: Separate DerivationTree per System

Create `DerivationTree.K`, `DerivationTree.T`, etc. each with their own `ModalAxiom` inductive.

**Disadvantages**:
- Massive code duplication (the deduction theorem proof alone is ~200 lines)
- Maintenance nightmare: any bug fix must be applied to all copies
- Propositional axioms and structural rules are identical across systems

**Verdict**: Reject Option C. The duplication is unacceptable.

### Recommended Architecture

**Use Option A** with the following concrete plan:

1. **Refactor `ModalAxiom`** into a parameterized form using a predicate:

```lean
/-- Axiom predicate parameterized by which modal axioms are included. -/
inductive ModalAxiomBase (includeT : Prop) (include4 : Prop) (includeB : Prop) :
    Proposition Atom -> Prop where
  | implyK ...     -- always
  | implyS ...     -- always
  | efq ...        -- always
  | peirce ...     -- always
  | modalK ...     -- always
  | modalT (h : includeT) ... -- conditional
  | modalFour (h : include4) ... -- conditional
  | modalB (h : includeB) ...    -- conditional
```

However, this approach creates complexity in the proofs. A cleaner alternative:

2. **Alternative: Use a single `ModalAxiom` with predicates** (PREFERRED):

Keep the current `ModalAxiom` inductive as-is but introduce a predicate `ModalAxiomFor` that restricts which axioms are available:

```lean
/-- Which modal axioms are available for a given system. -/
def ModalAxiomFor (sys : ModalSystemTag) : Proposition Atom -> Prop :=
  fun phi => ModalAxiom phi ∧ match sys with
  | .K => ¬isModalT phi ∧ ¬isModal4 phi ∧ ¬isModalB phi
  | .T => ¬isModal4 phi ∧ ¬isModalB phi
  | ...
```

This is also unwieldy. After deeper analysis, the cleanest approach is:

3. **BEST APPROACH: Separate inductive per axiom set, shared DerivationTree**:

Define per-system axiom predicates that are simple restrictors of the existing `ModalAxiom`:

```lean
/-- K axioms: propositional + K distribution only. -/
inductive AxiomK : Proposition Atom -> Prop where
  | implyK | implyS | efq | peirce | modalK

/-- T axioms: K + reflexivity. -/
inductive AxiomT : Proposition Atom -> Prop where
  | implyK | implyS | efq | peirce | modalK | modalT

/-- S4 axioms: T + transitivity. -/
inductive AxiomS4 : Proposition Atom -> Prop where
  | implyK | implyS | efq | peirce | modalK | modalT | modalFour
```

Then parameterize `DerivationTree` over the axiom predicate:

```lean
inductive DerivationTree (Axioms : Proposition Atom -> Prop) :
    List (Proposition Atom) -> Proposition Atom -> Type _ where
  | ax (Gamma) (phi) (h : Axioms phi) : DerivationTree Axioms Gamma phi
  | assumption ... | modus_ponens ... | necessitation ... | weakening ...
```

**Key insight**: The `DerivationTree` constructors 2-5 (assumption, modus_ponens, necessitation, weakening) are identical across all systems. Only the `ax` constructor's predicate changes. The deduction theorem proof works identically for any axiom predicate since it never inspects the `ax` payload -- it only needs `implyK` and `implyS`, which are in every predicate.

This means:
- **DeductionTheorem**: Write ONCE, parameterized over `Axioms`
- **MCS**: Write ONCE, parameterized (needs `HasDeductionTheorem` which follows from the parameterized DT)
- **Soundness**: Write per-system (different frame conditions)
- **Completeness**: Write per-system (different canonical model properties)
- **Instances.lean**: Write per-system (different typeclass registrations)

**Backward compatibility**: The existing `ModalAxiom` becomes `AxiomS5` (or is kept as an alias). All existing code compiles unchanged.

## 2. Per-System Analysis

### 2.1 System K (Minimal Normal Modal Logic)

**Axioms**: ImplyK, ImplyS, EFQ, Peirce, K distribution
**Rules**: Modus ponens, Necessitation
**Frame condition**: None (all frames)
**Typeclass**: `ModalHilbert` (ALREADY EXISTS in `ProofSystem.lean`)
**Tag type**: `Modal.HilbertK` (ALREADY EXISTS)

**Soundness**: Straightforward. Only the K axiom and propositional axioms need semantic verification. All of these are valid on arbitrary frames. The existing `axiom_sound` theorem already handles these cases -- just need to drop the frame condition hypotheses for the propositional and K cases.

**Completeness**: The canonical model construction works with NO frame property requirements. The canonical relation `R S T iff forall psi, box psi in S -> psi in T` is arbitrary (no special properties). The truth lemma for `box` uses:
- Forward: `box phi in S -> for all T with R S T, phi in T` (by definition of R)
- Backward: `box phi not in S -> exists T with R S T and phi not in T` (box witness)

The box witness proof for K is SIMPLER than for S5 because `{psi | box psi in S} union {neg phi}` is consistent without needing to invoke axioms T, 4, B.

**Key difference from S5**: The `derive_box_from_inconsistency` lemma in `MCS.lean` currently uses `mcs_box_closure` (which relies on axiom T) in the case where `neg phi not in L`. For K, this case needs a different argument: if all elements of L have box-versions in S, we use the K axiom + necessitation to derive box(bot) in S from L deriving bot, then show this contradicts consistency. Actually, revisiting: the standard K completeness proof for the box witness works differently -- it shows `{psi | box psi in S} union {neg phi}` is consistent directly by showing that if L derives bot and all elements come from that set, then we can get box(phi) in S using iterated deduction + necessitation + K distribution, contradicting the assumption. This is exactly what `derive_box_from_inconsistency` does in the `neg phi in L` case. The `neg phi not in L` case does NOT need T -- it just says all of L is in S (via the definition of the witness set minus neg phi, where elements come from `{psi | box psi in S}`), so if L derives bot, S is inconsistent, contradiction. But wait -- for K, `box psi in S` does NOT imply `psi in S` (that's T). So the `neg phi not in L` case must be handled differently.

**Resolution**: For K, the box witness set should be `{psi | box psi in S}` (without needing box_closure). The inconsistency argument: if L derives bot and all L elements are in `{psi | box psi in S}`, then all L elements have box-versions in S. By iterated deduction theorem + necessitation + K distribution, we get `box(bot)` in S. Since `box(bot) -> bot` is derivable (from K + efq: `box(bot -> phi) -> (box bot -> box phi)`, set phi = bot, then `box bot -> box bot`, which just gives box bot... Actually `box bot -> bot` is NOT derivable in K. In K, `box bot` is consistent.

**Critical realization**: In system K, `box bot` is consistent! A model with empty accessibility makes `box phi` true for all phi. This means the box witness proof for K needs a different structure.

Let me re-examine the standard completeness proof for K:

The standard approach: Show `{psi | box psi in S} union {neg phi}` is consistent.
- Suppose L derives bot, with all L elements from that set.
- Separate L into L' (from `{psi | box psi in S}`) and possibly neg phi.
- If neg phi not in L: all L elements are psi with box psi in S. If L derives bot, then by iterated DT + necessitation + K: box(bot) in S. But S is an MCS of K, and bot is NOT in S (since S is consistent). However, box(bot) in S does not imply bot in S in K. So this is NOT a contradiction in K.

**This means the standard K completeness proof uses a DIFFERENT construction.** The correct approach for K:

Define `R S T iff {phi | box phi in S} subset T`. Then:
- Box witness: if box phi not in S, need T such that R S T and phi not in T.
- Take W = {psi | box psi in S} union {neg phi}. Show W is consistent.
- If W is inconsistent, L derives bot with L subset W. Extract the box-elements and neg phi.
  - Case 1: neg phi in L. By DT, L' derives (phi -> bot) -> bot where L' = L minus neg phi. All L' elements are psi with box psi in S. By iterated DT + necessitation + K: box((phi->bot)->bot) in S. By K + necessitation of Peirce/DNE: box(phi) in S. Contradiction.
  - Case 2: neg phi not in L. All elements are psi with box psi in S. By iterated DT + necessitation + K: box(bot) in S. Now, in any MCS of K, is box(bot) necessarily absent? Let's check: K is sound over all frames. There exist frames where box(bot) holds (empty-accessibility worlds). So box(bot) is NOT a theorem of K, and it's consistent to have box(bot) in an MCS. BUT: we also need all elements of L to be in some MCS T with R S T. In an MCS T of K with all of {psi | box psi in S} subset T, we'd have bot in T if L derives bot, contradicting T being consistent.

Wait, I think I was overcomplicating this. Let me reconsider:

If L subset {psi | box psi in S} and L derives bot, then L subset T for any T with R S T (by definition of R). So T derives bot (by weakening), contradicting T being consistent. So if ANY MCS T with R S T exists, we get a contradiction. But the issue is: we want to FIND such a T.

Actually, the box witness for K works as follows:
- We want to show: `{psi | box psi in S} union {neg phi}` is consistent.
- Suppose it's not. Then some finite L from this set derives bot.
- By the standard argument (split into box-part and neg phi), we derive box(phi) in S.
- This contradicts our assumption that box phi not in S.

The derivation of box(phi) from the inconsistency: this is EXACTLY what `derive_box_from_inconsistency` does in the existing code. Let me re-examine the `neg phi not in L` case:

Currently: "All elements of L have box-versions in S, so in S by box_closure." -- This uses T. For K, we DON'T have box_closure. But we don't need it! If all elements of L are psi with box psi in S, and L derives bot, then by iterated DT + necessitation + K distribution, box(bot) in S. Then K + EFQ: box(bot -> phi) is a theorem, so box(bot -> phi) in S. Then by K distribution: box(bot) in S and box(bot -> phi) in S gives box(phi) in S. Contradiction with box phi not in S.

**YES, this works!** The K case just needs a different argument for the `neg phi not in L` branch. Instead of using `mcs_box_closure` to show elements are in S and then deriving a contradiction via set consistency, we use `derive_box_from_box_context` to get `box(bot)` in S, then use K + necessitated EFQ to get `box(phi)` in S.

**Estimated effort**: Medium. Need to:
1. Define `AxiomK` predicate
2. Parameterize `DerivationTree` over axiom predicate
3. Adapt the deduction theorem (mechanical, just parameterize)
4. Adapt MCS theory (mechanical, just parameterize)
5. Write K-specific soundness (simple -- drop frame conditions)
6. Write K-specific completeness (moderate -- adjust box witness proof)
7. Create K typeclass instances

**Lines estimate**: ~300 new lines for K-specific metalogic, ~200 for refactoring shared code.

### 2.2 System T (Reflexive Frames)

**Axioms**: K + T (box phi -> phi)
**Frame condition**: Reflexive (`Std.Refl m.r`)
**Typeclass**: `ModalTHilbert` (NEW, to be created)
**Tag type**: `Modal.HilbertT` (NEW)

**Soundness**: Add T axiom verification with reflexivity. The existing `axiom_sound` case for `modalT` already uses `h_refl`. Just need to remove transitivity and Euclidean hypotheses.

**Completeness**: Canonical model is reflexive. The proof that `R S S` holds uses `mcs_box_closure` (axiom T: box phi in S -> phi in S), which gives `forall phi, box phi in S -> phi in S`, which is exactly `R S S`. This is already proven as `canonical_refl` in the existing code.

The box witness proof works exactly as for S5 in the `neg phi not in L` case: box_closure gives psi in S for all psi with box psi in S, so L subset S, L derives bot contradicts S consistent. The `neg phi in L` case uses the same double negation + Peirce argument as S5.

**Key difference from S5 completeness**: The canonical model is reflexive but NOT transitive or Euclidean. The truth lemma works identically. The completeness theorem conclusion quantifies over reflexive frames only.

**Estimated effort**: Low. The T completeness is essentially a simplification of the S5 completeness, removing the transitive and Euclidean cases.

**Lines estimate**: ~250 new lines.

### 2.3 System D (Serial Frames)

**Axioms**: K + D (box phi -> diamond phi)
**Frame condition**: Serial (`Relation.Serial m.r`)
**Typeclass**: `ModalDHilbert` (NEW)
**Tag type**: `Modal.HilbertD` (NEW)

**Soundness**: The D axiom validity proof already exists in `Basic.lean` as `Satisfies.d`, which requires `[Relation.Serial m.r]`. The Relation.Serial class is defined in `Relation.lean` with `serial : Relator.LeftTotal r`.

**Completeness**: The canonical model must be serial: for every MCS S, there exists MCS T with R S T. This requires showing that `{psi | box psi in S}` is consistent (which then extends to an MCS T by Lindenbaum). The proof: if L derives bot and L subset `{psi | box psi in S}`, then by iterated DT + necessitation + K, box(bot) in S. By D: box(bot) -> diamond(bot). So diamond(bot) in S. But diamond(bot) = neg(box(neg bot)) = neg(box(top)) ... Actually, let's think about this more carefully.

In D, we have `box phi -> diamond phi` for all phi. If box(bot) in S, then diamond(bot) in S. diamond(bot) = (box(bot -> bot_prop)) -> bot_prop. Hmm, unfolding: diamond(bot) = neg(box(neg bot)). neg bot = bot -> bot = top. So diamond(bot) = neg(box(top)) = (box(top)) -> bot. So if box(bot) in S and box(top) in S (which holds since top is a theorem, hence box(top) is derivable by necessitation, hence in S), then bot in S. Contradiction with S being consistent.

Wait, let me redo: diamond(phi) = neg(box(neg phi)). So diamond(bot) = neg(box(neg bot)) = neg(box(bot -> bot)). And neg(box(bot -> bot)) = (box(bot -> bot)) -> bot. Now, bot -> bot is a theorem (implyK with phi = psi = bot gives bot -> (bot -> bot), then... actually just use the identity axiom pattern). So box(bot -> bot) is in every MCS (by necessitation of a theorem). So diamond(bot) = (box(bot -> bot)) -> bot. Having diamond(bot) in S and box(bot -> bot) in S gives bot in S. Contradiction.

Actually, the standard approach is simpler: Axiom D says box(phi) -> diamond(phi). Set phi = bot. Then box(bot) -> diamond(bot). Since diamond(bot) is equivalent to "there exists an accessible world satisfying bot", and no world satisfies bot, we need a different argument at the syntactic level. The point is:

D axiom: box(bot) -> diamond(bot). diamond(bot) = neg(box(neg bot)) = neg(box(top)). Since top is a theorem, box(top) is derivable, so box(top) in S. So neg(box(top)) means (box(top)) -> bot. So diamond(bot) in S gives (box(top) -> bot) in S. Combined with box(top) in S gives bot in S. Contradiction.

So the seriality proof for D's canonical model follows from: if {psi | box psi in S} is inconsistent, then box(bot) in S, then diamond(bot) in S (via D), then bot in S (as shown above). QED.

**Estimated effort**: Medium. Similar to K but need to prove seriality of canonical relation.

**Lines estimate**: ~300 new lines.

### 2.4 System S4 (Preorder / Reflexive + Transitive Frames)

**Axioms**: K + T + 4 (box phi -> box box phi)
**Frame condition**: Reflexive and transitive (`Std.Refl m.r` and `IsTrans World m.r`)
**Typeclass**: `ModalS4Hilbert` (NEW)
**Tag type**: `Modal.HilbertS4` (NEW)

**Soundness**: Combine T soundness (reflexivity) and 4 soundness (transitivity). Both cases already exist in `axiom_sound` -- just remove the Euclidean hypothesis.

**Completeness**: The canonical model must be reflexive AND transitive.
- Reflexive: Same as T (from axiom T, via `mcs_box_closure`).
- Transitive: Same as S5 (from axiom 4, via `mcs_box_box`). Already proven as `canonical_trans`.

The box witness proof is simpler than S5 -- the `neg phi not in L` case uses box_closure (from T) exactly as in the S5 code. The `neg phi in L` case uses the same double negation argument.

**Estimated effort**: Low-Medium. S4 is essentially S5 minus the Euclidean property. Most of the existing canonical model code can be reused directly.

**Lines estimate**: ~250 new lines.

### 2.5 System S5 (Equivalence Relations)

**Axioms**: K + T + 4 + B (phi -> box diamond phi)
**Frame condition**: Reflexive, transitive, Euclidean (equivalently: equivalence relation)
**Typeclass**: `ModalS5Hilbert` (ALREADY EXISTS)
**Tag type**: `Modal.HilbertS5` (ALREADY EXISTS)

**Current status**: COMPLETE. Full metalogic pipeline exists:
- `DerivationTree.lean` (187 lines): 5 constructors, height function
- `DeductionTheorem.lean` (193 lines): Well-founded recursion, HasDeductionTheorem instance
- `MCS.lean` (325 lines): Lindenbaum, box_witness, all MCS properties
- `Soundness.lean` (139 lines): Structural induction
- `Completeness.lean` (263 lines): Canonical model, truth lemma, completeness theorem

**Required changes**: Refactor to use parameterized axiom set (the existing code becomes the S5 specialization). The `ModalAxiom` type is renamed/aliased and the `DerivationTree` is parameterized.

### 2.6 Summary Table

| System | Axioms | Frame | Typeclass | Soundness | Completeness | Effort |
|--------|--------|-------|-----------|-----------|--------------|--------|
| K | K | All | `ModalHilbert` (exists) | Easy | Medium | Medium |
| T | K, T | Refl | `ModalTHilbert` (new) | Easy | Easy | Low |
| D | K, D | Serial | `ModalDHilbert` (new) | Easy | Medium | Medium |
| S4 | K, T, 4 | Preorder | `ModalS4Hilbert` (new) | Easy | Easy-Med | Low-Med |
| S5 | K, T, 4, B | Equiv | `ModalS5Hilbert` (exists) | Done | Done | Refactor only |

## 3. Creating Modal/ProofSystem/Instances.lean

### Current Gap

The concrete `DerivationTree` in `Logics/Modal/Metalogic/` and the abstract typeclass hierarchy in `Foundations/Logic/ProofSystem.lean` are disconnected. The tag types `Modal.HilbertK` and `Modal.HilbertS5` exist but have no `InferenceSystem` or `HasAxiom*` instances.

### Required Instances (for S5, following the pattern from Temporal/Bimodal)

Following the pattern in `Temporal/ProofSystem/Instances.lean`:

```lean
-- InferenceSystem: maps HilbertS5-derivation to DerivationTree [] phi
instance : InferenceSystem Modal.HilbertS5 (Modal.Proposition Atom) where
  derivation phi := Modal.DerivationTree [] phi

-- ModusPonens
instance : ModusPonens Modal.HilbertS5 (F := Modal.Proposition Atom) where
  mp := fun h1 h2 => by
    obtain ⟨d1⟩ := h1; obtain ⟨d2⟩ := h2
    exact ⟨Modal.DerivationTree.modus_ponens [] _ _ d1 d2⟩

-- Necessitation
instance : Necessitation Modal.HilbertS5 (F := Modal.Proposition Atom) where
  nec := fun h => by
    obtain ⟨d⟩ := h
    exact ⟨Modal.DerivationTree.necessitation _ d⟩

-- Propositional axioms: HasAxiomImplyK, HasAxiomImplyS, HasAxiomEFQ, HasAxiomPeirce
-- Modal axioms: HasAxiomK, HasAxiomT, HasAxiom4, HasAxiomB

-- Bundled instances: ClassicalHilbert, ModalHilbert, ModalS5Hilbert
```

**For K** (separate instances):
```lean
instance : InferenceSystem Modal.HilbertK (Modal.Proposition Atom) where
  derivation phi := Modal.DerivationTreeK [] phi  -- K-restricted tree

-- Only: HasAxiomImplyK, HasAxiomImplyS, HasAxiomEFQ, HasAxiomPeirce, HasAxiomK
-- Bundled: ClassicalHilbert, ModalHilbert
```

**Lines estimate**: ~80 lines per system (InferenceSystem + ModusPonens + Necessitation + 4 propositional + N modal axioms + bundled classes).

### File Organization

```
Cslib/Logics/Modal/
  ProofSystem/
    Instances.lean      -- All typeclass instances (K, T, D, S4, S5)
  Metalogic/
    DerivationTree.lean -- Parameterized over axiom set
    DeductionTheorem.lean -- Generic (works for any axiom set)
    MCS.lean            -- Generic
    Soundness/
      K.lean            -- K-specific soundness
      T.lean            -- T-specific soundness
      S4.lean           -- etc.
      S5.lean
    Completeness/
      K.lean
      T.lean
      S4.lean
      S5.lean
```

## 4. Integrating HilbertDerivedRules.lean

### Current State

`Cslib/Logics/Propositional/NaturalDeduction/HilbertDerivedRules.lean`:
- 447 lines, sorry-free
- Imports `FromHilbert.lean`
- Provides derived intro/elim rules for Lukasiewicz-encoded connectives
- Not imported by any module in the project

### Integration Options

**Option A (Minimal)**: Add an import of `HilbertDerivedRules` in a propositional aggregator module. Since it depends on `FromHilbert` which depends on `Basic` and propositional `Derivation`, it fits naturally in the NaturalDeduction submodule. Just needs to be imported somewhere in the module graph.

**Option B (Add to build via root import)**: If there's a root `Cslib/Logics/Propositional/NaturalDeduction.lean` aggregator, add `public import` there. Otherwise create one.

**Recommendation**: Option A. Add `public import Cslib.Logics.Propositional.NaturalDeduction.HilbertDerivedRules` to the `Equivalence.lean` file or to a new aggregator module. This makes the rules available downstream and verifies they compile in CI.

**Risk**: Low. The file is sorry-free and only provides new definitions/theorems, so it cannot break existing code.

## 5. Integration with Cube.lean

### Current State

`Cube.lean` defines 15 modal systems SEMANTICALLY as sets of propositions valid over classes of frames:

```lean
def K World Atom := logic (Set.univ)           -- all frames
def T World Atom := logic {m | Std.Refl m.r}    -- reflexive
def D World Atom := logic {m | Relation.Serial m.r}  -- serial
def S4 World Atom := (K) union (T) union (Four) -- reflexive + transitive
def S5 World Atom := (K) union (T) union (Four) union (Five)  -- equivalence
```

Note: S4 and S5 use set UNION of logic-sets, not logic of frame-intersection. This is correct semantically (a formula is in S4 iff it's valid in K AND valid in T AND valid in Four).

Wait, actually this is incorrect. Let me re-read:

```lean
def S4 World Atom := (K World Atom) ∪ (T World Atom) ∪ (Four World Atom)
```

This defines S4 as the UNION of K-valid, T-valid, and Four-valid formulas. This is wrong as a definition of S4! S4 is the set of formulas valid on ALL reflexive transitive frames, which is:

```lean
logic {m : Model World Atom | Std.Refl m.r ∧ IsTrans World m.r}
```

The union definition says phi is in S4 iff phi is valid on all frames (K) OR valid on all reflexive frames (T) OR valid on all transitive frames (Four). This is a SUBSET of the correct S4 (it misses formulas that are valid on reflexive+transitive frames but not on reflexive-only or transitive-only frames).

**This is a potential issue that should be investigated**, but it may be intentional -- defining S4 as the deductive closure of K + T + 4 axiom schemata, which is equivalent to the set of formulas valid on preorder frames by soundness and completeness. The union definition captures the deductive closure correctly IF the intent is "the logic axiomatized by K, T, and 4 schemata." In that case, the completeness theorem would establish `S4 = logic {m | Std.Refl m.r ∧ IsTrans}`, proving the two definitions coincide.

### Bridge from Cube to Proof Systems

Once per-system completeness is established, the bridge theorems would be:

```lean
/-- K-valid formulas are exactly the K-derivable formulas. -/
theorem K_eq_derivable : K World Atom = {phi | Modal.DerivableK phi}

/-- S4-valid formulas are exactly the S4-derivable formulas. -/
theorem S4_eq_derivable : S4 World Atom = {phi | Modal.DerivableS4 phi}
```

These follow directly from soundness + completeness for each system. They connect the semantic definitions in Cube.lean to the syntactic proof systems.

**Note**: This bridge work is a separate task that follows naturally from establishing per-system metalogic. It should not block the core proof system work.

## 6. Dependency Ordering and Parallelization

### Phase 0: Infrastructure (Must be first)

1. **Refactor `ModalAxiom` / `DerivationTree`**: Parameterize the axiom predicate
2. **Add intermediate typeclasses**: `ModalTHilbert`, `ModalDHilbert`, `ModalS4Hilbert` to `ProofSystem.lean`
3. **Add tag types**: `Modal.HilbertT`, `Modal.HilbertD`, `Modal.HilbertS4`
4. **Generalize `DeductionTheorem`**: Parameterize over axiom predicate
5. **Generalize `MCS`**: Parameterize over axiom predicate (the `modalDerivationSystem` becomes parameterized)

### Phase 1: S5 Preservation (Must follow Phase 0)

6. **Verify S5 still works**: Ensure existing metalogic passes with the parameterized framework
7. **Create `Modal/ProofSystem/Instances.lean`**: Register S5 typeclass instances
8. **Integrate `HilbertDerivedRules.lean`**: Add import

### Phase 2: Per-System Metalogic (Can be PARALLELIZED after Phase 1)

These are independent and can be developed in parallel:

| Track A | Track B | Track C |
|---------|---------|---------|
| K soundness | T soundness | D soundness |
| K completeness | T completeness | D completeness |
| K instances | T instances | D instances |

S4 should follow T (since S4 = T + 4, and T's reflexivity proof is needed).

### Phase 3: Cube Bridge (After Phase 2)

9. **Bridge theorems**: K_eq_derivable, T_eq_derivable, etc.
10. **Cube.lean update**: Add syntactic characterizations alongside semantic definitions

### Dependency DAG

```
Phase 0: [Refactor DerivationTree] -> [Generalize DT] -> [Generalize MCS]
                                    -> [Add typeclasses/tags]
Phase 1: [Phase 0] -> [Verify S5] -> [Create Instances.lean]
                                   -> [Integrate HilbertDerivedRules]
Phase 2: [Phase 1] -> [K metalogic]  (parallel)
                    -> [T metalogic]  (parallel)
                    -> [D metalogic]  (parallel)
                    -> [S4 metalogic] (after T)
Phase 3: [Phase 2] -> [Cube bridge theorems]
```

## 7. Risk Assessment

### Low Risk

- **Typeclass additions**: Adding new bundled classes and tag types to `ProofSystem.lean` is additive and cannot break existing code.
- **Instances.lean creation**: Follows an established pattern exactly (copy from Temporal, adapt to Modal).
- **HilbertDerivedRules integration**: Sorry-free, additive only.
- **T and S4 completeness**: These are simplifications of the existing S5 completeness (fewer frame properties to prove).
- **Soundness proofs (all systems)**: These are straightforward -- just verify each axiom against the appropriate frame condition. All semantic validity proofs already exist in `Basic.lean`.

### Medium Risk

- **DerivationTree refactoring**: Parameterizing over axiom sets requires touching the core type and all downstream modules. Risk of breaking the existing S5 pipeline.
  - **Mitigation**: Keep `ModalAxiom` as an alias for the S5 axiom set. Test incrementally.
- **K completeness box witness**: The standard box witness for K differs slightly from the S5 version because `box_closure` (axiom T) is unavailable. Need a different argument for the `neg phi not in L` case.
  - **Mitigation**: The argument is well-understood in the literature and straightforward: derive `box(bot)` from the inconsistency, then use K + necessitated EFQ to get `box(phi)`.
- **D completeness**: Proving seriality of the canonical model requires a non-trivial argument involving axiom D.
  - **Mitigation**: The argument is standard (see Blackburn et al. Ch. 4).

### Higher Risk

- **`ModalS5Hilbert` refactoring**: Changing `ModalS5Hilbert` to extend `ModalS4Hilbert` instead of `ModalHilbert` directly could have ripple effects through Bimodal.
  - **Mitigation**: Test with `lake build` after the change. The actual field set is unchanged; only the inheritance path changes.
- **Cube.lean semantic definitions**: The union-based definitions of S4, S5, etc. may need to be verified as equivalent to the frame-intersection definitions. If they differ, bridge theorems become more complex.
  - **Mitigation**: The equivalence follows from soundness + completeness, so this is resolved naturally by the metalogic work.

### Where Sorry Might Be Needed

Based on analysis, **no sorry should be required**. All proof techniques are standard and well-understood:
- Soundness: Direct semantic verification (already done for each axiom in Basic.lean)
- Completeness: Canonical model + truth lemma (proven for S5, adaptable to simpler systems)
- Deduction theorem: Structural induction (generic over axiom set)
- MCS theory: Zorn's lemma (generic framework already exists in Consistency.lean)

If difficulties arise, the most likely place is the K completeness box witness, where the absence of axiom T requires a careful alternative argument. However, the technique (using necessitated EFQ + K distribution to lift inconsistency through the box) is standard.

## 8. Effort Estimates

| Work Item | Lines | Difficulty | Dependencies |
|-----------|-------|------------|--------------|
| Refactor DerivationTree (parameterize) | ~150 | Medium | None |
| Generalize DeductionTheorem | ~50 | Low | Refactored DT |
| Generalize MCS | ~100 | Low-Medium | Generalized DT |
| Add typeclasses + tags | ~50 | Low | None |
| Verify S5 preservation | ~50 | Low | Refactored infrastructure |
| Create Instances.lean (all systems) | ~400 | Low | Typeclasses + DTs |
| K soundness | ~80 | Low | Parameterized DT |
| K completeness | ~250 | Medium | Generalized MCS |
| T soundness | ~60 | Low | Parameterized DT |
| T completeness | ~200 | Low | Generalized MCS |
| D soundness | ~60 | Low | Parameterized DT |
| D completeness | ~250 | Medium | Generalized MCS |
| S4 soundness | ~70 | Low | Parameterized DT |
| S4 completeness | ~220 | Low-Medium | T completeness |
| Integrate HilbertDerivedRules | ~10 | Trivial | None |
| Cube bridge theorems | ~200 | Medium | Per-system completeness |
| **TOTAL** | **~2,200** | | |

## 9. Additional Infrastructure Needs

### Naming Alignment

- Modal uses `Proposition`; Temporal/Bimodal use `Formula`. This is a cosmetic inconsistency. **No action needed** for this task, but worth noting for future alignment.

### Documentation

- The `Metalogic.lean` aggregator module docstring should be updated to reflect multi-system support.
- Each per-system completeness file should document its canonical model construction and frame properties.
- The Cube.lean module should cross-reference the proof system files once they exist.

### Testing

- No test/example files exist for modal logic. Creating a small `Examples.lean` demonstrating derivations in each system (K, T, D, S4, S5) would be valuable for verification and documentation.

## 10. Recommendations

1. **Adopt Option A** (typeclass-based hierarchy) for parameterization.
2. **Start with Phase 0** (infrastructure refactoring) as it unblocks all per-system work.
3. **Prioritize S5 preservation** in Phase 1 -- the existing pipeline must not regress.
4. **Develop K, T, D in parallel** in Phase 2, with S4 following T.
5. **Defer Cube bridge** (Phase 3) as it depends on all per-system completeness proofs.
6. **Do not introduce sorry** -- all techniques are standard and proven feasible by the existing S5 implementation.
7. **The DerivationTree parameterization** is the highest-risk item and should receive the most careful attention during implementation.

## References

- `Cslib/Logics/Modal/Basic.lean` -- Semantic definitions, axiom-frame correspondences
- `Cslib/Logics/Modal/Cube.lean` -- 15 modal systems defined semantically
- `Cslib/Logics/Modal/Metalogic/` -- S5 metalogic pipeline (5 files, ~1100 lines)
- `Cslib/Foundations/Logic/ProofSystem.lean` -- Typeclass hierarchy, tag types
- `Cslib/Logics/Temporal/ProofSystem/Instances.lean` -- Reference pattern for instances
- `Cslib/Logics/Bimodal/ProofSystem/Instances.lean` -- Reference pattern for instances
- `Cslib/Foundations/Logic/Metalogic/Consistency.lean` -- Generic MCS framework
- `Cslib/Foundations/Logic/Theorems/Modal/` -- Generic K-level and S5-level theorems
- `Cslib/Logics/Propositional/NaturalDeduction/HilbertDerivedRules.lean` -- Unimported derived rules
- Blackburn, de Rijke, Venema -- *Modal Logic*, Ch. 4 (Canonical Models)
