# Task 30: Modal Metalogic Research Report

**Session**: sess_1780979445_1b23fa
**Date**: 2026-06-08

## 1. Existing Modal Infrastructure in cslib

### 1.1 File Listing

| File | Key Types/Definitions |
|------|----------------------|
| `Cslib/Logics/Modal/Basic.lean` | `Proposition` (4-constructor inductive: `atom`, `bot`, `imp`, `box`), `Model` (World/Atom parameterized), `Satisfies` (truth at world), `Judgement`, derived connectives (`neg`, `top`, `or`, `and`, `diamond`, `iff`), notation (`□`, `◇`, `→`, `∧`, `∨`, `¬`, `↔`), `theory`, `TheoryEq`, `Proposition.valid`, `logic`, semantic axiom theorems (K, T, B, 4, 5, D) |
| `Cslib/Logics/Modal/Cube.lean` | Modal logic cube definitions (`K`, `T`, `B`, `Four`, `Five`, `D`, `S4`, `S5`, etc.), subset theorems (`k_subset_d`, `d_subset_t`, etc.), validity examples |
| `Cslib/Logics/Modal/Denotation.lean` | `Proposition.denotation` (denotational semantics), `satisfies_mem_denotation` characterization, `theoryEq_denotation_eq` |

### 1.2 Key Type Signatures

```lean
-- Formula type
inductive Proposition (Atom : Type u) : Type u where
  | atom (p : Atom) | bot | imp (φ₁ φ₂ : Proposition Atom) | box (φ : Proposition Atom)
  deriving DecidableEq, BEq

-- Model
structure Model (World : Type*) (Atom : Type*) where
  r : World → World → Prop
  v : World → Atom → Prop

-- Satisfaction
def Satisfies (m : Model World Atom) (w : World) : Proposition Atom → Prop

-- Connective instances
instance : ModalConnectives (Proposition Atom)
instance : Bot (Proposition Atom)
instance : HasInferenceSystem (Judgement World Atom)
```

### 1.3 What Exists vs. What's Missing

**Exists**: Full semantic infrastructure (models, satisfaction, validity, frame conditions, modal cube). Semantic proofs of axiom soundness (K, T, B, 4, 5, D). Theory/theory-equivalence. Denotational semantics.

**Missing**: No syntactic proof system (no `DerivationTree` for modal logic). No derivability relation. No deduction theorem. No MCS theory. No soundness/completeness theorems linking syntax and semantics. This is precisely what Task 30 must build.

## 2. Generic MCS API (Task 29)

### 2.1 Location

`Cslib/Foundations/Logic/Metalogic/Consistency.lean`

### 2.2 Available Definitions and Theorems

```lean
-- Core structure
structure DerivationSystem (F : Type*) [HasBot F] [HasImp F] where
  Deriv : List F → F → Prop
  weakening : ∀ {Γ Δ : List F} {φ : F}, Deriv Γ φ → (∀ x ∈ Γ, x ∈ Δ) → Deriv Δ φ
  assumption : ∀ {Γ : List F} {φ : F}, φ ∈ Γ → Deriv Γ φ
  mp : ∀ {Γ : List F} {φ ψ : F}, Deriv Γ (HasImp.imp φ ψ) → Deriv Γ φ → Deriv Γ ψ

-- Consistency
def Consistent (D : DerivationSystem F) (Γ : List F) : Prop
def SetConsistent (D : DerivationSystem F) (S : Set F) : Prop
def SetMaximalConsistent (D : DerivationSystem F) (S : Set F) : Prop

-- Chain union and Lindenbaum
theorem consistent_chain_union : ... → SetConsistent D (⋃₀ C)
theorem set_lindenbaum : SetConsistent D S → ∃ M, S ⊆ M ∧ SetMaximalConsistent D M

-- Deduction theorem hypothesis
def HasDeductionTheorem (D : DerivationSystem F) : Prop :=
  ∀ {Γ : List F} {φ ψ : F}, D.Deriv (φ :: Γ) ψ → D.Deriv Γ (HasImp.imp φ ψ)

-- Closure properties (require HasDeductionTheorem)
theorem SetMaximalConsistent.closed_under_derivation
theorem SetMaximalConsistent.implication_property
theorem SetMaximalConsistent.negation_complete
theorem set_consistent_not_both
```

### 2.3 How to Instantiate for Modal Logic

To use the generic API, Task 30 must:

1. **Define `Modal.DerivationTree`**: An inductive type with constructors for axiom, assumption, modus ponens, necessitation, and weakening.
2. **Define `Modal.Deriv`**: Wrap `DerivationTree` into a `Prop` (existential).
3. **Construct `Modal.derivationSystem : DerivationSystem (Proposition Atom)`**: Provide proofs of weakening, assumption, and mp from the DerivationTree constructors.
4. **Prove `HasDeductionTheorem Modal.derivationSystem`**: By structural induction on DerivationTree (the most substantial proof in the deduction theorem module).

The generic API then immediately provides SetConsistent, SetMaximalConsistent, Lindenbaum's lemma, and all closure properties.

## 3. BimodalLogic Metalogic Patterns

### 3.1 DerivationTree Structure (BimodalLogic)

The BimodalLogic `DerivationTree` has 7 constructors:
1. `axiom` -- axiom schema instance
2. `assumption` -- formula from context
3. `modus_ponens` -- from `Γ ⊢ φ → ψ` and `Γ ⊢ φ`
4. `necessitation` -- from `[] ⊢ φ` derive `[] ⊢ □φ` (empty context only)
5. `temporal_necessitation` -- from `[] ⊢ φ` derive `[] ⊢ Gφ` (not needed for modal)
6. `temporal_duality` -- swap temporal connectives (not needed for modal)
7. `weakening` -- from `Γ ⊢ φ` and `Γ ⊆ Δ` derive `Δ ⊢ φ`

For the standalone modal logic, we need only constructors 1-4 and 7 (5 constructors total), as specified in the task description.

### 3.2 Deduction Theorem Pattern

The BimodalLogic deduction theorem uses well-founded recursion on `DerivationTree.height`. Key insight: the weakening case where `A ∈ Γ'` but `Γ' ≠ A :: Γ` requires a helper `deduction_with_mem` that recurses on the subderivation directly, avoiding non-terminating exchange patterns.

For the modal version, the same pattern applies but is simpler (no temporal rules). The necessitation case is trivially handled because it requires an empty context, so `A ∈ []` is impossible.

### 3.3 MCS Properties Pattern

BimodalLogic proves:
- `closed_under_derivation` (derivable formulas are in MCS)
- `implication_property` (MP reflected in membership)
- `negation_complete` (either φ or ¬φ in MCS)
- `box_closure` (□φ ∈ S → φ ∈ S, using axiom T)
- `box_box` (□φ ∈ S → □□φ ∈ S, using axiom 4)
- `diamond_box_duality` (¬□φ ↔ ◇¬φ)

All of these are available in the generic framework (Task 29) except the modal-specific ones (`box_closure`, `box_box`, diamond-box duality). Those require the modal axioms and are built on top of `closed_under_derivation`.

### 3.4 Soundness Pattern

BimodalLogic soundness works by:
1. Proving each axiom valid over the appropriate frame class (semantic proofs)
2. Proving inference rules (MP, necessitation) preserve validity
3. Induction on DerivationTree: each constructor case reduces to axiom validity or rule preservation

For modal S5 soundness, the cslib `Basic.lean` already has semantic proofs of K, T, B, 4, 5 axiom validity. The remaining work is connecting these to the syntactic proof system via the DerivationTree.

### 3.5 Completeness Pattern

The standard canonical model construction for S5:
1. **Worlds**: Set-based maximal consistent sets (MCS)
2. **Accessibility**: Universal relation (for S5) or `R(S, T) iff ∀φ, □φ ∈ S → φ ∈ T`
3. **Valuation**: `v(S, p) iff atom(p) ∈ S`
4. **Truth Lemma**: By structural induction on formulas, `Satisfies canonical_model S φ ↔ φ ∈ S`
5. **Completeness**: If φ is not derivable, then {¬φ} is consistent, extends to MCS M by Lindenbaum, and M is a world in the canonical model that does not satisfy φ.

For S5, the universal accessibility relation makes the truth lemma for □ straightforward: `□φ ∈ S ↔ ∀ T, φ ∈ T` because S5's axioms ensure all MCS agree on boxed formulas.

## 4. Proposed File Structure

```
Cslib/Logics/Modal/Metalogic/
├── DerivationTree.lean    -- Modal DerivationTree, Deriv, DerivationSystem instance
├── DeductionTheorem.lean  -- Deduction theorem + HasDeductionTheorem proof
├── MCS.lean               -- Modal MCS: import generic + modal-specific properties
├── Soundness.lean         -- Soundness theorem
└── Completeness.lean      -- Canonical model construction + completeness
```

## 5. Key Type Signatures

### 5.1 DerivationTree (~300 lines total for DerivationTree.lean + DeductionTheorem.lean)

```lean
namespace Cslib.Logic.Modal

-- Axiom schema for S5 modal logic
inductive ModalAxiom : Proposition Atom → Prop where
  | prop_k (φ ψ χ : Proposition Atom) : ModalAxiom (φ.imp (ψ.imp φ))  -- ImplyK
  | prop_s (φ ψ χ : Proposition Atom) : ModalAxiom ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ)))
  | efq (φ : Proposition Atom) : ModalAxiom (Proposition.bot.imp φ)
  | peirce (φ ψ : Proposition Atom) : ModalAxiom (((φ.imp ψ).imp φ).imp φ)
  | modal_k (φ ψ : Proposition Atom) : ModalAxiom ((□(φ.imp ψ)).imp ((□φ).imp (□ψ)))
  | modal_t (φ : Proposition Atom) : ModalAxiom ((□φ).imp φ)
  | modal_4 (φ : Proposition Atom) : ModalAxiom ((□φ).imp (□(□φ)))
  | modal_b (φ : Proposition Atom) : ModalAxiom (φ.imp (□(◇φ)))

-- DerivationTree (5 constructors)
inductive DerivationTree : List (Proposition Atom) → Proposition Atom → Type where
  | axiom (Γ) (φ) : ModalAxiom φ → DerivationTree Γ φ
  | assumption (Γ) (φ) : φ ∈ Γ → DerivationTree Γ φ
  | modus_ponens (Γ) (φ ψ) : DerivationTree Γ (φ.imp ψ) → DerivationTree Γ φ → DerivationTree Γ ψ
  | necessitation (φ) : DerivationTree [] φ → DerivationTree [] (□φ)
  | weakening (Γ Δ) (φ) : DerivationTree Γ φ → (Γ ⊆ Δ) → DerivationTree Δ φ

-- Wrapper
def Deriv (Γ : List (Proposition Atom)) (φ : Proposition Atom) : Prop :=
  Nonempty (DerivationTree Γ φ)

-- DerivationSystem instance
def modalDerivationSystem : DerivationSystem (Proposition Atom) where
  Deriv := Deriv
  weakening := ...  -- from DerivationTree.weakening
  assumption := ... -- from DerivationTree.assumption
  mp := ...         -- from DerivationTree.modus_ponens
```

### 5.2 DeductionTheorem (~300 lines)

```lean
-- Main theorem
noncomputable def deduction_theorem (Γ : List (Proposition Atom)) (A B : Proposition Atom)
    (h : DerivationTree (A :: Γ) B) : DerivationTree Γ (A.imp B)

-- HasDeductionTheorem instance
theorem modal_has_deduction_theorem :
    HasDeductionTheorem (@modalDerivationSystem Atom)
```

### 5.3 MCS (~400 lines)

```lean
-- Generic imports give us:
-- SetConsistent, SetMaximalConsistent, set_lindenbaum
-- closed_under_derivation, implication_property, negation_complete

-- Modal-specific additions:
theorem SetMaximalConsistent.box_closure
    (h_mcs : SetMaximalConsistent modalDerivationSystem S)
    (h_box : □φ ∈ S) : φ ∈ S

theorem SetMaximalConsistent.box_box
    (h_mcs : SetMaximalConsistent modalDerivationSystem S)
    (h_box : □φ ∈ S) : □(□φ) ∈ S

-- For canonical model accessibility:
theorem SetMaximalConsistent.box_witness
    (h_mcs : SetMaximalConsistent modalDerivationSystem S)
    (h_not_box : □φ ∉ S) :
    ∃ T, SetMaximalConsistent modalDerivationSystem T ∧ (∀ ψ, □ψ ∈ S → ψ ∈ T) ∧ φ ∉ T
```

### 5.4 Soundness (~350 lines)

```lean
-- Validity for S5 class of frames (reflexive + transitive + Euclidean)
theorem axiom_valid (h : ModalAxiom φ) :
    ∀ (m : Model World Atom), Std.Refl m.r → IsTrans World m.r →
    Relation.RightEuclidean m.r → ∀ w, Satisfies m w φ

-- Main soundness theorem
theorem soundness (Γ : List (Proposition Atom)) (φ : Proposition Atom)
    (h : Deriv Γ φ) :
    ∀ (m : Model World Atom), Std.Refl m.r → IsTrans World m.r →
    Relation.RightEuclidean m.r →
    ∀ w, (∀ ψ ∈ Γ, Satisfies m w ψ) → Satisfies m w φ
```

### 5.5 Completeness (~450 lines)

```lean
-- Canonical model
def CanonicalModel (Atom : Type*) : Model (CanonicalWorld Atom) Atom where
  r := fun S T => ∀ φ, □φ ∈ S.val → φ ∈ T.val
  v := fun S p => .atom p ∈ S.val

-- Truth lemma
theorem truth_lemma (S : CanonicalWorld Atom) (φ : Proposition Atom) :
    Satisfies (CanonicalModel Atom) S φ ↔ φ ∈ S.val

-- Completeness theorem
theorem completeness (φ : Proposition Atom)
    (h_valid : ∀ (m : Model World Atom), Std.Refl m.r → IsTrans World m.r →
      Relation.RightEuclidean m.r → ∀ w, Satisfies m w φ) :
    Deriv [] φ
```

## 6. Mathlib Dependencies

### 6.1 Already Used (from Basic.lean and Consistency.lean)
- `Mathlib.Order.Zorn` -- `zorn_subset_nonempty` for Lindenbaum
- `Mathlib.Data.Set.Basic` -- Set operations
- `Mathlib.Order.Defs.Unbundled` -- Order typeclasses
- `Mathlib.Logic.Nonempty` -- Nonempty

### 6.2 Additional Needed
- `Mathlib.Data.List.Basic` -- List membership, filter, append
- Potentially `Mathlib.Order.Preorder.Chain` for chain properties

### 6.3 Mathlib Modal Logic Status
No Mathlib support for Kripke semantics, modal logic proof systems, or modal completeness. Everything is built from scratch in cslib.

## 7. Estimated Complexity Per Component

| Component | Estimated Lines | Difficulty | Key Challenge |
|-----------|----------------|------------|---------------|
| DerivationTree + Axioms | ~150 | Low | Straightforward inductive type |
| DeductionTheorem | ~300 | High | Well-founded recursion on height, weakening case analysis |
| MCS (modal-specific) | ~400 | Medium | box_witness requires careful Lindenbaum application |
| Soundness | ~350 | Medium | Mostly connecting existing semantic proofs to DerivationTree |
| Completeness | ~450 | High | Canonical model construction, truth lemma induction |
| **Total** | **~1,650** | | |

### 7.1 Risk Assessment

**DeductionTheorem**: Highest risk. The well-founded recursion on derivation height with the weakening case is notoriously tricky. The BimodalLogic pattern (with `deduction_with_mem` helper) provides a proven approach but adapting it requires care with termination proofs.

**Completeness**: Second highest risk. The truth lemma for the box case requires proving that the canonical accessibility relation has the right properties (reflexive, transitive, Euclidean for S5), and that box_witness produces the right MCS. The S5 case simplifies this because the relation is essentially universal on the canonical model, but formalizing this cleanly requires careful coordination.

**Soundness**: Lower risk since `Basic.lean` already has all the semantic axiom validity proofs. The main work is the inductive step over DerivationTree constructors.

## 8. Design Decisions

### 8.1 S5 vs. General Modal Logic

The task description mentions S5. The canonical model construction is significantly simpler for S5 because the accessibility relation collapses to a universal relation among MCS (due to axioms T+4+B together). For K or weaker logics, the canonical relation `R(S,T) iff ∀φ, □φ ∈ S → φ ∈ T` requires more frame-condition verification.

**Recommendation**: Build the DerivationTree and MCS infrastructure for general S5, with the canonical model using the simplified universal relation. This matches the cslib Cube.lean which defines S5 as the logic of reflexive+transitive+Euclidean frames.

### 8.2 DerivationTree as Type vs Prop

Following BimodalLogic's pattern, `DerivationTree` should be a `Type` (not `Prop`) to enable pattern matching and computable height functions. The `Deriv` wrapper provides the `Prop` version for the generic DerivationSystem.

### 8.3 Axiom Schema Representation

Two options:
- **Inductive Axiom type** (BimodalLogic pattern): `ModalAxiom : Proposition Atom → Prop`
- **Typeclass-based** (cslib ProofSystem.lean pattern): `HasAxiomK`, `HasAxiomT`, etc.

**Recommendation**: Use the inductive `ModalAxiom` type directly in the DerivationTree (simpler, self-contained). The typeclass infrastructure in ProofSystem.lean is designed for polymorphic use across logics but adds complexity for a standalone metalogic module. The typeclass instances can be connected later if needed.

### 8.4 Formula Parameterization

The existing `Proposition Atom` is parameterized over `Atom : Type u`. The DerivationTree and all metalogic should be similarly parameterized. For completeness (which needs Lindenbaum's lemma), no cardinality assumptions on Atom are needed since we work with set-based MCS.

## 9. Phasing Recommendation

1. **Phase 1**: DerivationTree.lean -- Define ModalAxiom, DerivationTree, height function, Deriv, and the DerivationSystem instance
2. **Phase 2**: DeductionTheorem.lean -- Prove deduction theorem by structural induction, provide HasDeductionTheorem
3. **Phase 3**: MCS.lean -- Import generic MCS + prove modal-specific properties (box_closure, box_box, box_witness, conjunction/disjunction properties)
4. **Phase 4**: Soundness.lean -- Connect semantic axiom proofs to DerivationTree, prove soundness by induction
5. **Phase 5**: Completeness.lean -- Canonical model construction, truth lemma, completeness theorem
6. **Phase 6**: Integration -- Connect to existing Modal/Basic.lean semantics, verify `lake build`

Each phase depends on the previous one. Phases 4 and 5 could potentially be parallelized since soundness and completeness have different proof structures, but completeness requires MCS from Phase 3.
