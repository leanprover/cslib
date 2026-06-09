# Research Report: Port Bimodal Hilbert-Style Proof System

**Task**: 4 — Port the Bimodal Hilbert-style proof system to Cslib/Logics/Bimodal/ProofSystem/
**Date**: 2026-06-08
**Session**: sess_1780980276_702f7c_4

---

## 1. Executive Summary

This task ports 5 files (~2000 lines) from BimodalLogic to cslib, creating the Bimodal proof system.
The port is structurally straightforward: the existing Temporal/ProofSystem/ port provides a near-exact
template, and the cslib infrastructure (HasAxiom* typeclasses, BimodalTMHilbert, tag types) is already
complete.

**Key findings**:
- The argument order convention for `untl(event, guard)` is consistent between BimodalLogic and cslib
  (both use first=event, second=guard after Task 32)
- The bimodal Formula type in cslib is missing `swap_temporal` and `atoms` definitions; these must
  be added as prerequisites in the bimodal Formula module
- The concrete Axiom inductive has 42 constructors; 37 are Base, 2 Dense, 3 Discrete
- The cslib BimodalTMHilbert typeclass covers only Base-level axioms; frame-class-specific axioms
  (uniformity, Prior, Z1, density) exist in the Axiom inductive but do not need new typeclasses
- The Temporal/ProofSystem/ port can be used as a direct template, with additions for modal operators

## 2. Source Analysis (BimodalLogic)

### 2.1 Axioms.lean (~485 lines)

**42 axiom constructors** organized in 8 layers:

| Layer | Count | Constructors |
|-------|-------|-------------|
| Propositional | 4 | prop_k, prop_s, ex_falso, peirce |
| S5 Modal | 5 | modal_t, modal_4, modal_b, modal_5_collapse, modal_k_dist |
| BX Temporal | 22 | serial_future/past, left_mono_until_G/since_H, right_mono_until/since, connect_future/past, enrichment_until/since, self_accum_until/since, absorb_until/since, linear_until/since, until_F, since_P, temp_linearity/past, F_until_equiv, P_since_equiv |
| Interaction | 1 | modal_future (MF: box phi -> box(G phi)) |
| Uniformity | 5 | discrete_symm_fwd/bwd, discrete_propagate_fwd/bwd, discrete_box_necessity |
| Prior | 2 | prior_UZ, prior_SZ |
| Z1 | 1 | z1 |
| Density | 2 | density, dense_indicator |

**FrameClass**: `Base | Dense | Discrete` with partial order and `minFrameClass` function.

**Port notes**: Direct 1:1 port. The cslib bimodal Formula is parameterized over `Atom : Type u`
(unlike BimodalLogic's concrete `Atom` type), so all constructors need the universe parameter.

### 2.2 Derivation.lean (~385 lines)

**7 inference rules** in `DerivationTree fc Gamma phi`:
1. `axiom` — gated by `h.minFrameClass <= fc`
2. `assumption` — membership in context
3. `modus_ponens` — implication elimination
4. `necessitation` — from empty context, derive box(phi)
5. `temporal_necessitation` — from empty context, derive G(phi)
6. `temporal_duality` — from empty context, derive swap_temporal(phi)
7. `weakening` — context monotonicity

Plus:
- `DerivationTree.lift` for frame class monotonicity
- `DerivationTree.height` computable measure
- Height properties (6 theorems)
- Notations: `Gamma |- phi`, `Gamma |-[fc] phi`, `|- phi`, `|-[fc] phi`
- Example derivations (5 examples)

**Port notes**: The Temporal/ProofSystem/Derivation.lean has 6 rules (no `necessitation`).
The bimodal version adds `necessitation` for the modal box operator. Otherwise structurally identical.

### 2.3 Derivable.lean (~220 lines)

Prop-valued wrapper using `Nonempty (DerivationTree fc G p)`:
- `Derivable.ofTree` — coercion from tree
- `Derivable.lift` — frame class monotonicity
- 7 constructor-mirroring lemmas: `ax`, `assume`, `mp`, `nec`, `temp_nec`, `temp_dual`, `weaken`
- aesop/simp attributes on key lemmas
- 6 test examples

**Port notes**: Direct port following Temporal/ProofSystem/Derivable.lean template, adding
`nec` for modal necessitation.

### 2.4 Substitution.lean (~460 lines)

Uniform substitution theorem:
- `Formula.subst q r` — substitute atom q with atom r
- 10+ structural simp lemmas (subst_atom_eq/ne, subst_bot, subst_imp, subst_box, etc.)
- Derived operator substitution lemmas (neg, and, or, diamond, some_past, some_future)
- `subst_fresh_eq` — freshness preservation
- `subst_atoms` — atoms-of-substituted-formula
- `Context.subst` — context substitution
- `atoms_of_context` with membership lemmas
- `axiom_subst` — axiom preservation under substitution (42 cases)
- `swap_temporal_subst` — commutativity
- `axiom_subst_minFrameClass` — frame class preservation
- `derivation_subst` — main theorem (7 cases)

**Port notes**: Requires `Formula.atoms : Finset Atom` (not yet in cslib bimodal Formula).
Also requires `swap_temporal` on bimodal Formula. This is the most complex file due to the
42-case `axiom_subst` proof.

### 2.5 LinearityDerivedFacts.lean (~83 lines)

- Documentation of non-derivability of linearity from base axioms
- Counterexample explanation
- Single convenience definition `temp_linearity_derivation`

**Port notes**: Trivial port (mostly documentation + one definition).

## 3. Cslib Infrastructure Analysis

### 3.1 What Already Exists

| Component | Location | Status |
|-----------|----------|--------|
| Bimodal Formula type | `Cslib/Logics/Bimodal/Syntax/Formula.lean` | Complete (101 lines) |
| Bimodal Context type | `Cslib/Logics/Bimodal/Syntax/Context.lean` | Complete |
| Connective typeclasses | `Cslib/Foundations/Logic/Connectives.lean` | Complete |
| InferenceSystem | `Cslib/Foundations/Logic/InferenceSystem.lean` | Complete |
| Polymorphic axiom abbrevs | `Cslib/Foundations/Logic/Axioms.lean` | Complete (all 22 temporal + 1 interaction + 4 prop + 6 modal) |
| HasAxiom* typeclasses | `Cslib/Foundations/Logic/ProofSystem.lean` | Complete (all typeclasses) |
| BimodalTMHilbert class | `Cslib/Foundations/Logic/ProofSystem.lean` | Complete |
| Bimodal.HilbertTM tag | `Cslib/Foundations/Logic/ProofSystem.lean` | Complete |
| BimodalConnectives instance | `Cslib/Logics/Bimodal/Syntax/Formula.lean` | Complete |
| Temporal ProofSystem (template) | `Cslib/Logics/Temporal/ProofSystem/` | Complete (4 files) |

### 3.2 What Must Be Added (Prerequisites)

**P1: `swap_temporal` on Bimodal Formula** (critical — needed for DerivationTree.temporal_duality)

The bimodal Formula adds `box` to the temporal formula, so `swap_temporal` must handle it:
```lean
def swap_temporal : Formula Atom -> Formula Atom
  | .atom s => .atom s
  | .bot => .bot
  | .imp phi psi => .imp (swap_temporal phi) (swap_temporal psi)
  | .box phi => .box (swap_temporal phi)      -- NEW vs temporal
  | .untl phi psi => .snce (swap_temporal phi) (swap_temporal psi)
  | .snce phi psi => .untl (swap_temporal phi) (swap_temporal psi)
```

Plus involution theorem and distributional lemmas (neg, some_future/past, all_future/past, diamond).

**P2: `Formula.atoms` on Bimodal Formula** (needed for Substitution.lean)

```lean
def atoms [DecidableEq Atom] : Formula Atom -> Finset Atom
  | .atom s => {s}
  | .bot => {}
  | .imp phi psi => phi.atoms ∪ psi.atoms
  | .box phi => phi.atoms
  | .untl phi psi => phi.atoms ∪ psi.atoms
  | .snce phi psi => phi.atoms ∪ psi.atoms
```

These prerequisites can be added directly to the bimodal Formula module or as separate files.

### 3.3 Naming Convention Mapping

BimodalLogic uses swapped names for propositional axioms:
- BimodalLogic `prop_k` = cslib `ImplyS` (distribution: (phi -> (psi -> chi)) -> ((phi -> psi) -> (phi -> chi)))
- BimodalLogic `prop_s` = cslib `ImplyK` (weakening: phi -> (psi -> phi))

This is already handled correctly in the Temporal instance registration.

### 3.4 Axiom Convention Differences

**Axiom 5 / 5-Collapse**:
- BimodalLogic has BOTH `modal_b` (phi -> box(diamond(phi))) AND `modal_5_collapse` (diamond(box(phi)) -> box(phi))
- cslib ModalS5Hilbert extends K + T + 4 + B (no 5-collapse required)
- cslib has `HasAxiom5` (Euclidean: diamond(phi) -> box(diamond(phi))) but BimodalTMHilbert doesn't require it
- Resolution: The Axiom inductive keeps both. Instance registration uses `modal_b` for `HasAxiomB`. The `modal_5_collapse` is available in the concrete Axiom type but not needed for the typeclass.

**Frame-class-specific axioms** (uniformity, Prior, Z1, density):
- These are NOT covered by any cslib typeclass
- They exist only in the concrete Axiom inductive
- The `minFrameClass` function gates them
- No new typeclasses needed (these are specialized axioms, not part of the general TM system)

## 4. Argument Order Convention

**VERIFIED**: Both BimodalLogic and cslib use the same convention after Task 32:
- `untl(event, guard)` — first arg = event, second arg = guard
- `snce(event, guard)` — first arg = event, second arg = guard
- `some_future phi = untl phi top` — event = phi, guard = top

All 42 axiom constructors use this convention consistently. No argument swapping needed during port.

## 5. Structural Differences Between BimodalLogic and Cslib

### 5.1 Parameterization

| Aspect | BimodalLogic | cslib |
|--------|-------------|-------|
| Atom type | Concrete `Atom` (natural number-based) | Generic `Atom : Type u` |
| Formula | `Formula` (no params) | `Formula Atom` |
| Context | `Context` | `Context Atom` |
| Namespace | `Bimodal.ProofSystem` | `Cslib.Logic.Bimodal` |

### 5.2 Module System

BimodalLogic uses `import`; cslib uses `module` declarations with `public import` and
`@[expose] public section` patterns.

### 5.3 Derived Connectives

Both define derived connectives as `abbrev`:
- BimodalLogic: `Formula.neg`, `Formula.top`, `Formula.and`, `Formula.or`, `Formula.diamond`,
  `Formula.some_future`, `Formula.all_future`, `Formula.some_past`, `Formula.all_past`
- cslib: Same names and definitions, using the parametric `Formula Atom`

### 5.4 Temporal DerivationTree Differences

The Temporal DerivationTree in cslib has 6 rules. The Bimodal version needs 7:

| Rule | Temporal | Bimodal |
|------|----------|---------|
| axiom | Yes | Yes |
| assumption | Yes | Yes |
| modus_ponens | Yes | Yes |
| necessitation | No | **Yes** (modal box) |
| temporal_necessitation | Yes | Yes |
| temporal_duality | Yes | Yes |
| weakening | Yes | Yes |

## 6. Implementation Strategy

### Phase 1: Prerequisites (Formula extensions)

Add to `Cslib/Logics/Bimodal/Syntax/Formula.lean`:
- `swap_temporal` function with `box` case
- `swap_temporal_involution` theorem
- Distributional lemmas: `swap_temporal_neg`, `swap_temporal_diamond`,
  `swap_temporal_some_future`, `swap_temporal_some_past`, `swap_temporal_all_future`,
  `swap_temporal_all_past`
- `Formula.atoms` function (requires `[DecidableEq Atom]`, `Finset`)

### Phase 2: Axioms.lean

Create `Cslib/Logics/Bimodal/ProofSystem/Axioms.lean`:
- Port `FrameClass` inductive with LE, DecidableRel, PartialOrder instances
- Port 42-constructor `Axiom` inductive (parametric over `Atom`)
- Port `Axiom.minFrameClass` function
- Port `FrameClass.base_le` theorem

### Phase 3: Derivation.lean

Create `Cslib/Logics/Bimodal/ProofSystem/Derivation.lean`:
- Port `DerivationTree` with 7 rules (adding `necessitation`)
- Port `DerivationTree.lift`
- Port `DerivationTree.height` and height properties
- Port notations (scoped to avoid conflicts with Temporal)

### Phase 4: Derivable.lean

Create `Cslib/Logics/Bimodal/ProofSystem/Derivable.lean`:
- Port `Derivable` definition
- Port all constructor-mirroring lemmas (7)
- Port lift theorem
- Port test examples

### Phase 5: Substitution.lean

Create `Cslib/Logics/Bimodal/ProofSystem/Substitution.lean`:
- Port `Formula.subst` function
- Port all structural simp lemmas
- Port derived operator substitution lemmas
- Port `subst_fresh_eq`, `subst_atoms`
- Port `Context.subst`, `atoms_of_context`
- Port `axiom_subst` (42 cases — most tedious part)
- Port `swap_temporal_subst`, `axiom_subst_minFrameClass`
- Port `derivation_subst` main theorem

### Phase 6: LinearityDerivedFacts.lean

Create `Cslib/Logics/Bimodal/ProofSystem/LinearityDerivedFacts.lean`:
- Port documentation
- Port `temp_linearity_derivation`

### Phase 7: Instance Registration (Instances.lean)

Create `Cslib/Logics/Bimodal/ProofSystem/Instances.lean`:
- Register `InferenceSystem Bimodal.HilbertTM (Bimodal.Formula Atom)`
- Register `ModusPonens`, `Necessitation` instances
- Register 4 propositional HasAxiom* instances (with name swap)
- Register 5 modal HasAxiom* instances (K, T, 4, B for ModalS5Hilbert)
- Register `TemporalNecessitation` instance (via temporal_necessitation + duality for past)
- Register 22 temporal HasAxiom* instances
- Register `HasAxiomMF` instance
- Register bundled `PropositionalHilbert`, `ModalHilbert`, `ModalS5Hilbert`, `TemporalBXHilbert`, `BimodalTMHilbert`

## 7. Risk Assessment

### Low Risk
- Axioms.lean: Direct 1:1 port with parametric Atom
- Derivation.lean: Template from Temporal, plus necessitation rule
- Derivable.lean: Template from Temporal, plus nec lemma
- LinearityDerivedFacts.lean: Trivial port
- Instances.lean: Template from Temporal, plus modal instances

### Medium Risk
- Substitution.lean: 42-case axiom_subst is tedious but mechanical
- Prerequisites (swap_temporal, atoms): Must be added to Formula module

### Potential Issues
1. **`module` declaration**: cslib uses `module` keyword — new files must include it
2. **`@[expose] public section`**: Some files may need this pattern
3. **Namespace conflicts**: Bimodal notations (F, G, H, P, S, U) conflict with Temporal
   — use `scoped` notations and careful namespace opening
4. **Finset import**: `Formula.atoms` needs `Finset` import, which may not be in scope
5. **`all_past`/`all_future` are `abbrev`s**: In BimodalLogic these are primitive constructors;
   in cslib they are derived (`all_future = neg (some_future (neg phi))`). The axiom formulas
   use these derived forms, so axiom constructor types must be verified to reduce correctly.

### No Issues
- Argument order: Consistent (event, guard) convention in both
- FrameClass: Same structure in both
- DerivationTree structure: Nearly identical (just add necessitation)

## 8. Estimated Scope

| File | Source Lines | Estimated Port Lines | Complexity |
|------|-------------|---------------------|------------|
| Prerequisites (Formula.lean additions) | N/A | ~100 | Low |
| Axioms.lean | 485 | ~450 | Low |
| Derivation.lean | 385 | ~300 | Low |
| Derivable.lean | 220 | ~180 | Low |
| Substitution.lean | 460 | ~450 | Medium |
| LinearityDerivedFacts.lean | 83 | ~70 | Low |
| Instances.lean | N/A | ~220 | Medium |
| **Total** | **~1630** | **~1770** | **Low-Medium** |

## 9. Dependencies

| Dependency | Status | Impact |
|------------|--------|--------|
| Task 2 (Bimodal Syntax) | Completed | Formula + Context types available |
| Task 20 (Propositional Theorems) | Completed | PropositionalHilbert infrastructure |
| Task 22 (Temporal HasAxiom* infra) | Completed | All HasAxiom* typeclasses, BimodalTMHilbert |
| Task 32 (untl argument order fix) | Completed | Argument order convention settled |

All dependencies are satisfied. No blockers.
