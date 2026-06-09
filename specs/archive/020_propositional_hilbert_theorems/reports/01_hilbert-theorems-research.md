# Research Report: Port Propositional Hilbert-Style Theorems

## Task
Port propositional Hilbert-style theorems from BimodalLogic to `Cslib/Foundations/Logic/Theorems/` as generic `[PropositionalHilbert S]` lemmas.

## 1. PropositionalHilbert Typeclass (cslib)

**Location**: `Cslib/Foundations/Logic/ProofSystem.lean` (lines 141-147)

```lean
class PropositionalHilbert (S : Type*) [HasBot F] [HasImp F]
    [InferenceSystem S F]
    extends ModusPonens S (F := F),
            HasAxiomImplyK S (F := F),
            HasAxiomImplyS S (F := F),
            HasAxiomEFQ S (F := F),
            HasAxiomPeirce S (F := F)
```

**Fields provided (via extends)**:
- `ModusPonens.mp`: From `DerivableIn S (imp phi psi)` and `DerivableIn S phi`, derive `DerivableIn S psi`
- `HasAxiomImplyK.implyK`: `DerivableIn S (phi -> (psi -> phi))` (weakening/K-combinator)
- `HasAxiomImplyS.implyS`: `DerivableIn S ((phi -> (psi -> chi)) -> ((phi -> psi) -> (phi -> chi)))` (distribution/S-combinator)
- `HasAxiomEFQ.efq`: `DerivableIn S (bot -> phi)` (ex falso quodlibet)
- `HasAxiomPeirce.peirce`: `DerivableIn S (((phi -> psi) -> phi) -> phi)` (Peirce's law)

**Note on `HasAxiomDNE`**: Exists as a separate typeclass (line 100) but is NOT part of `PropositionalHilbert`. DNE is instead a derived theorem from EFQ + Peirce in the BimodalLogic source, which is the correct approach for cslib.

**Derivability type**: `InferenceSystem.DerivableIn S (a : F)` is defined as `Nonempty (S[down]a)`. This is a `Prop`-valued wrapper (existential), not the `Type`-valued `DerivationTree` from BimodalLogic. All ported theorems must work at this `DerivableIn` level.

## 2. CRITICAL: Naming Inversion Between BimodalLogic and cslib

BimodalLogic and cslib use **inverted names** for K and S axioms:

| Axiom Schema | BimodalLogic Name | cslib Name |
|---|---|---|
| `phi -> (psi -> phi)` (weakening) | `Axiom.prop_s` | `Axioms.ImplyK` / `HasAxiomImplyK` |
| `(phi -> (psi -> chi)) -> ((phi -> psi) -> (phi -> chi))` (distribution) | `Axiom.prop_k` | `Axioms.ImplyS` / `HasAxiomImplyS` |

This means every occurrence of `Axiom.prop_s` in the BimodalLogic source maps to `HasAxiomImplyK.implyK` in cslib, and `Axiom.prop_k` maps to `HasAxiomImplyS.implyS`. This is a systematic renaming that must be applied throughout the port.

## 3. Source Files Analysis

### 3.1 Combinators.lean (675 lines)

**BimodalLogic Location**: `Theories/Bimodal/Theorems/Combinators.lean`

**Contents** (all derivable from K+S axioms, no deduction theorem needed):
| Theorem | Signature | Lines | Deduction Theorem? |
|---|---|---|---|
| `imp_trans` | `(A -> B) -> (B -> C) -> (A -> C)` | 83-90 | No |
| `mp` | Helper wrapper for modus ponens | 95-97 | No |
| `identity` | `A -> A` (SKK) | 107-113 | No |
| `b_combinator` | `(B -> C) -> (A -> B) -> (A -> C)` | 126-136 | No |
| `theorem_flip` | `(A -> B -> C) -> (B -> A -> C)` | 147-268 | No |
| `theorem_app1` | `A -> (A -> B) -> B` | 279-296 | No |
| `theorem_app2` | `A -> B -> (A -> B -> C) -> C` | 307-529 | No |
| `pairing` | `A -> B -> (A and B)` | 567-574 | No |
| `dni` | `A -> neg(neg(A))` | 600-601 | No |
| `combine_imp_conj` | `(P -> A) -> (P -> B) -> (P -> A and B)` | 614-622 | No |
| `combine_imp_conj_3` | `(P -> A) -> (P -> B) -> (P -> C) -> (P -> A and (B and C))` | 631-636 | No |
| `temp_future_derived` | `box(phi) -> G(box(phi))` | 661-672 | No (modal-specific, skip) |

**Portability**: HIGH. All theorems are pure combinator proofs using only K, S, and modus ponens. No deduction theorem or contexts needed. Only `temp_future_derived` is modal-specific and should not be ported here.

**Estimated output**: ~250-300 lines (the proofs will be shorter in DerivableIn style since we don't need explicit formula arguments to modus_ponens).

### 3.2 Propositional/Core.lean (730 lines)

**BimodalLogic Location**: `Theories/Bimodal/Theorems/Propositional/Core.lean`

**Contents**:
| Theorem | Signature | Deduction Theorem? | Portable? |
|---|---|---|---|
| `lem` | `A or neg(A)` | No | Yes (unfolds to `identity`) |
| `efq_axiom` | `bot -> phi` | No | Yes (axiom wrapper) |
| `peirce_axiom` | `((phi -> psi) -> phi) -> phi` | No | Yes (axiom wrapper) |
| `double_negation` | `neg(neg(phi)) -> phi` | No | Yes (EFQ+Peirce+b_combinator) |
| `ecq` | `[A, neg(A)] |- B` | Uses contexts | Partial -- needs context mechanism |
| `raa` | `A -> (neg(A) -> B)` | No | Yes (pure combinator) |
| `efq_neg` | `neg(A) -> (A -> B)` | No | Yes (flip of raa) |
| `ldi` | `[A] |- A or B` | Uses contexts | Partial -- needs context mechanism |
| `rdi` | `[B] |- A or B` | Uses contexts | Partial -- needs context mechanism |
| `rcp` | `(neg(A) -> neg(B)) -> (B -> A)` | Uses weakening/contexts but proof is combinator-based | Yes (result is implication form) |
| `lce` | `[A and B] |- A` | Uses contexts | Partial -- needs context mechanism |
| `rce` | `[A and B] |- B` | Uses contexts | Partial -- needs context mechanism |
| `lce_imp` | `(A and B) -> A` | Yes (deduction theorem) | BLOCKED without deduction theorem |
| `rce_imp` | `(A and B) -> B` | Yes (deduction theorem) | BLOCKED without deduction theorem |

**Key insight**: The context-based theorems (`ecq`, `ldi`, `rdi`, `lce`, `rce`) operate on `DerivationTree fc [A, B] phi`, which has no counterpart in the cslib `DerivableIn` framework. These must either:
- Be omitted (contexts are per-logic)
- Have their implication forms derived by other means

The implication forms `lce_imp` and `rce_imp` use the deduction theorem. Since the task description says "DeductionTheorem stays per-logic", these are BLOCKED for the generic port. However, we can potentially derive them using Peirce's law and combinator techniques directly (without the deduction theorem). This is a non-trivial proof engineering challenge.

**Alternative approach for lce_imp/rce_imp**: These can be proven purely from K, S, EFQ, Peirce using the following strategy:
- `lce_imp`: Show `(A and B) -> A` where `A and B = neg(A -> neg(B))`. This requires showing `neg(A -> neg(B)) -> A`. Use Peirce: assume `(A -> psi) -> A`, then `A`. The key is constructing the right instance of Peirce.
- This is feasible but requires careful combinator proofs (~40-60 lines each).

**Estimated output**: ~350-400 lines (context-free theorems only, combinator-based proofs for lce_imp/rce_imp).

### 3.3 Propositional/Connectives.lean (745 lines)

**BimodalLogic Location**: `Theories/Bimodal/Theorems/Propositional/Connectives.lean`

**Contents**:
| Theorem | Signature | Deduction Theorem? | Portable? |
|---|---|---|---|
| `classical_merge` | `(P -> Q) -> ((neg(P) -> Q) -> Q)` | Yes | NEEDS pure combinator proof |
| `iff_intro` | From `A -> B` and `B -> A`, derive `(A -> B) and (B -> A)` | No | Yes (uses pairing) |
| `iff_elim_left` | `[(A iff B), A] |- B` | Uses contexts | Context-dependent |
| `iff_elim_right` | `[(A iff B), B] |- A` | Uses contexts | Context-dependent |
| `contrapose_imp` | `(A -> B) -> (neg(B) -> neg(A))` | No | Yes |
| `contraposition` | Meta: from `A -> B`, derive `neg(B) -> neg(A)` | No | Yes |
| `contrapose_iff` | From `A iff B`, derive `neg(A) iff neg(B)` | No | Yes (uses lce_imp/rce_imp) |
| `iff_neg_intro` | Direct iff_intro for negated formulas | No | Yes |
| `demorgan_conj_neg_forward` | `neg(A and B) -> (neg(A) or neg(B))` | No | Yes |
| `demorgan_conj_neg_backward` | `(neg(A) or neg(B)) -> neg(A and B)` | Yes | NEEDS pure combinator proof |
| `demorgan_conj_neg` | Biconditional of above | No | Yes (composition) |
| `demorgan_disj_neg_forward` | `neg(A or B) -> (neg(A) and neg(B))` | No | Yes |
| `demorgan_disj_neg_backward` | `(neg(A) and neg(B)) -> neg(A or B)` | No | Yes |
| `demorgan_disj_neg` | Biconditional of above | No | Yes |

**Deduction theorem dependencies**: `classical_merge` and `demorgan_conj_neg_backward` currently use the deduction theorem. However, `demorgan_conj_neg_backward` has a proof that uses `lce_imp`/`rce_imp` which themselves require the deduction theorem. So the dependency chain is:
- `classical_merge` <- deduction theorem
- `demorgan_conj_neg_backward` <- `lce_imp`/`rce_imp` <- deduction theorem

If `lce_imp`/`rce_imp` can be proven without the deduction theorem (see Section 3.2 alternative), then `demorgan_conj_neg_backward` becomes portable. `classical_merge` would need a separate pure combinator proof.

**Note**: `contrapose_iff` uses `lce_imp` and `rce_imp`. If these are proven without deduction theorem, `contrapose_iff` becomes portable too.

**Estimated output**: ~300-350 lines (excluding context-based theorems, including combinator-based rewrites of DT-dependent proofs).

### 3.4 Propositional/Reasoning.lean (247 lines)

**BimodalLogic Location**: `Theories/Bimodal/Theorems/Propositional/Reasoning.lean`

**Contents**:
| Theorem | Signature | Deduction Theorem? | Portable? |
|---|---|---|---|
| `ni` | Negation Introduction: `Gamma,A |- neg(B)` and `Gamma,A |- B` implies `Gamma |- neg(A)` | Yes | Context + DT dependent |
| `ne` | Negation Elimination: `Gamma,neg(A) |- neg(B)` and `Gamma,neg(A) |- B` implies `Gamma |- A` | Yes | Context + DT dependent |
| `bi_imp` | `(A -> B) -> ((B -> A) -> (A iff B))` | Yes | Can be proven with pairing alone |
| `de` | Disjunction Elimination: `Gamma,A |- C` and `Gamma,B |- C` implies `Gamma,(A or B) |- C` | Yes | Context + DT dependent |
| `or_elim_neg_neg` | From `Gamma |- A or B`, `Gamma |- neg(A)`, `Gamma |- neg(B)`, derive `Gamma |- bot` | Yes | Context + DT dependent |

**Portability**: LOW for most. `ni`, `ne`, `de`, `or_elim_neg_neg` are inherently context-based AND use the deduction theorem. Only `bi_imp` can be ported -- and it is essentially just `pairing` applied to `(A -> B)` and `(B -> A)`, so it can be proven without the deduction theorem.

**Estimated output**: ~20-30 lines (just bi_imp and wrappers).

### 3.5 ContextualProofs.lean (451 lines)

**BimodalLogic Location**: `Theories/Bimodal/Theorems/ContextualProofs.lean`

**Contents**: 12 "Category A" propositional-in-context theorems, 8 "Category B" modal-in-context theorems, 8 "Category C" temporal-in-context theorems, plus ~20 weakening variants and ~20 pure weakening entries.

**Portability**: ZERO for generic PropositionalHilbert port. These theorems are:
1. Context-based (`[A, B] |- C` form)
2. Many are modal/temporal (use box, all_future, etc.)
3. They are explicitly designed for the BimodalLogic `DerivationTree` type

These theorems will be reconstructed per-logic when concrete proof systems are defined. They should NOT be in the generic `PropositionalHilbert` port.

### 3.6 BigConj (Syntax/BigConj.lean, 49 lines)

**BimodalLogic Location**: `Theories/Bimodal/Syntax/BigConj.lean`

**Contents**: `bigconj : List Formula -> Formula` and `neg_bigconj`, plus 4 simp lemmas.

**Portability**: MEDIUM. The syntactic definition can be ported generically using `HasBot F`, `HasImp F`, and `LukasiewiczDerived F`. However, the derivation-tree level lemmas (`bigconj_intro`, `bigconj_mem_iff`) are NOT in this file (they are in the chain-step seed consistency proof).

The task description mentions "BigConj generic (~500)" which likely refers to both the syntactic definition AND derivation-level lemmas that exist elsewhere (possibly in the Fisher-Ladner `EnrichedClosure` proof). Since the BigConj syntax file is only 49 lines, the "500 lines" likely includes derivation-level theorems scattered across other files.

**For this port**: Define `bigconj` generically over `[HasBot F] [HasImp F] [LukasiewiczDerived F]`, plus prove generic elimination/introduction lemmas as `[PropositionalHilbert S]` theorems.

**Estimated output**: ~80-120 lines (syntax + basic lemmas about derivability of bigconj members).

## 4. Target Structure

The target directory is `Cslib/Foundations/Logic/Theorems/`. Currently this directory does not exist.

**Proposed file organization**:

```
Cslib/Foundations/Logic/Theorems/
  Combinators.lean          -- I/B/C/S combinators, imp_trans, pairing, dni
  Propositional/
    Core.lean               -- LEM, double_negation, raa, efq_neg, rcp, lce_imp, rce_imp
    Connectives.lean        -- classical_merge, iff ops, contraposition, De Morgan
    Reasoning.lean          -- bi_imp (implication form)
  BigConj.lean              -- bigconj syntax + derivability lemmas
```

Each file should:
1. Import `Cslib.Foundations.Logic.ProofSystem`
2. Work over `variable {F : Type*} [HasBot F] [HasImp F] {S : Type*} [InferenceSystem S F] [PropositionalHilbert S]`
3. Use `LukasiewiczDerived F` for derived connectives (neg, and, or, top)
4. State theorems in terms of `InferenceSystem.DerivableIn S (...)` 

## 5. Generalization Strategy

### 5.1 Translation Pattern

Each BimodalLogic theorem follows this pattern:

**BimodalLogic** (concrete):
```lean
def imp_trans {fc : FrameClass} {A B C : Formula}
    (h1 : DerivationTree fc [] (A.imp B))
    (h2 : DerivationTree fc [] (B.imp C)) : DerivationTree fc [] (A.imp C) := ...
```

**cslib** (generic):
```lean
theorem imp_trans [PropositionalHilbert S (F := F)]
    {phi psi chi : F}
    (h1 : InferenceSystem.DerivableIn S (HasImp.imp phi psi))
    (h2 : InferenceSystem.DerivableIn S (HasImp.imp psi chi)) :
    InferenceSystem.DerivableIn S (HasImp.imp phi chi) := ...
```

### 5.2 Key Translation Rules

1. **Type**: `DerivationTree fc [] phi` --> `InferenceSystem.DerivableIn S phi`
2. **Axiom access**: `DerivationTree.axiom [] _ (Axiom.prop_s phi psi) ...` --> `HasAxiomImplyK.implyK` (note name inversion!)
3. **Axiom access**: `DerivationTree.axiom [] _ (Axiom.prop_k phi psi chi) ...` --> `HasAxiomImplyS.implyS`
4. **Modus ponens**: `DerivationTree.modus_ponens [] A B h_imp h_a` --> `ModusPonens.mp h_imp h_a`
5. **EFQ**: `DerivationTree.axiom [] _ (Axiom.ex_falso phi) ...` --> `HasAxiomEFQ.efq`
6. **Peirce**: `DerivationTree.axiom [] _ (Axiom.peirce phi psi) ...` --> `HasAxiomPeirce.peirce`
7. **Formula constructors**: `Formula.imp A B` --> `HasImp.imp phi psi`; `Formula.bot` --> `HasBot.bot`
8. **Negation**: `Formula.neg` --> `LukasiewiczDerived.neg` (or explicit `HasImp.imp phi HasBot.bot`)
9. **Conjunction**: `Formula.and` --> `LukasiewiczDerived.and`
10. **Disjunction**: `Formula.or` --> `LukasiewiczDerived.or`
11. **Context-based proofs** (`[A] |- B`): Skip or convert to implication form
12. **FrameClass parameter**: Drop entirely (generic over S)
13. **Weakening/assumption**: Not available in `DerivableIn` (no context)
14. **`DerivationTree.lift`**: Not needed (no frame class hierarchy)

### 5.3 Noncomputability

BimodalLogic `DerivationTree` is `Type`-valued, so proofs are computable term constructions. The cslib `DerivableIn` is `Prop`-valued (`Nonempty`), so ported proofs will need `noncomputable` or should use `Nonempty.intro`/`Nonempty.elim` patterns. Most ported theorems will be `noncomputable` since they compose existential witnesses.

### 5.4 LukasiewiczDerived Dependency

The derived connectives (neg, and, or, top) in BimodalLogic are defined on the `Formula` inductive type directly. In cslib, they are defined via the `LukasiewiczDerived` typeclass. The ported theorems need to ensure definitional equality between:
- `LukasiewiczDerived.neg phi` and `HasImp.imp phi HasBot.bot`
- `LukasiewiczDerived.and phi psi` and the nested imp/bot encoding
- `LukasiewiczDerived.or phi psi` and the neg/imp encoding

Since `LukasiewiczDerived` uses default implementations that match the BimodalLogic definitions, these should be definitionally equal after unfolding. However, if `LukasiewiczDerived` is an open typeclass (where instances could override defaults), there might be issues. Need to verify that an instance assumption `[LukasiewiczDerived F]` uses the default definitions.

**Recommendation**: Either add a typeclass assumption that the derived connectives match the Lukasiewicz defaults, or work directly with `HasImp.imp phi HasBot.bot` instead of `LukasiewiczDerived.neg phi` in theorem statements.

## 6. Deduction Theorem Blockers

### 6.1 Theorems Requiring Deduction Theorem

The following theorems in the source currently use the deduction theorem:

| Theorem | Can Rewrite Without DT? | Difficulty |
|---|---|---|
| `lce_imp` | Yes (direct combinator proof) | Hard |
| `rce_imp` | Yes (direct combinator proof) | Hard |
| `classical_merge` | Yes (using Peirce directly) | Hard |
| `ni` | No (inherently context-based) | N/A |
| `ne` | No (inherently context-based) | N/A |
| `bi_imp` | Yes (already essentially `pairing`) | Easy |
| `de` | No (inherently context-based) | N/A |
| `or_elim_neg_neg` | No (inherently context-based) | N/A |
| `demorgan_conj_neg_backward` | Yes (if lce_imp available) | Medium |

### 6.2 Strategy for DT-Free Proofs

**lce_imp**: `(A and B) -> A` where `A and B = neg(imp A (neg B))`.
- Goal: `neg(A -> neg(B)) -> A`
- Proof sketch: By Peirce with `psi = neg(B)`: `((A -> neg(B)) -> A) -> A`. We need to show `neg(A -> neg(B)) -> ((A -> neg(B)) -> A)`. This holds since from `neg(A -> neg(B))` and `A -> neg(B)`, we get `bot`, then `A` by EFQ.
- This is: `neg(X) -> (X -> A)` which is exactly `efq_neg X A` with `X = A -> neg(B)`. Then compose with Peirce.

**rce_imp**: `(A and B) -> B` -- similar strategy.

**classical_merge**: `(P -> Q) -> ((neg(P) -> Q) -> Q)`.
- Can be proved using Peirce directly: From `P -> Q` and `neg(P) -> Q`, we need `Q`. Instantiate Peirce at `Q` with `psi = bot`: `((Q -> bot) -> Q) -> Q`. Show `(Q -> bot) -> Q`: from `neg(Q)` and `P -> Q`, derive `neg(P)` by contraposition; from `neg(P) -> Q`, derive `Q` -- contradiction with `neg(Q)`.
- This requires composition of `contrapose_imp`, `imp_trans`, and Peirce.

These are feasible but require careful combinator proofs. Each is ~30-60 lines.

## 7. Dependencies Assessment

### 7.1 Mathlib Dependencies
None. The ProofSystem typeclass hierarchy uses only Lean 4 builtins and cslib's own `InferenceSystem` framework.

### 7.2 cslib Infrastructure Needed
All required infrastructure exists:
- `InferenceSystem` (`Cslib.Foundations.Logic.InferenceSystem`)
- `HasBot`, `HasImp` (`Cslib.Foundations.Logic.Connectives`)
- `LukasiewiczDerived` (`Cslib.Foundations.Logic.Connectives`)
- `ModusPonens`, `HasAxiomImplyK`, `HasAxiomImplyS`, `HasAxiomEFQ`, `HasAxiomPeirce` (`Cslib.Foundations.Logic.ProofSystem`)
- `PropositionalHilbert` (`Cslib.Foundations.Logic.ProofSystem`)
- `Axioms.ImplyK`, `Axioms.ImplyS`, `Axioms.EFQ`, `Axioms.Peirce` (`Cslib.Foundations.Logic.Axioms`)

### 7.3 Missing Infrastructure
1. **No context mechanism** in cslib `InferenceSystem` -- context-based theorems must be skipped or converted
2. **BigConj syntax definition** does not exist in cslib yet (needs to be created)
3. **LukasiewiczDerived instance** assumption needs to be verified or added as a constraint

## 8. Scope Revision

Given the analysis, the actual portable scope is smaller than the ~2,400 line estimate:

| Component | Source Lines | Portable Lines (est.) | Notes |
|---|---|---|---|
| Combinators | 675 | 250-300 | Drop modal-specific `temp_future_derived` |
| Propositional/Core | 730 | 350-400 | Drop context-based, rewrite lce_imp/rce_imp |
| Propositional/Connectives | 745 | 300-350 | Rewrite DT-dependent proofs |
| Propositional/Reasoning | 247 | 20-30 | Only bi_imp portable |
| ContextualProofs | 451 | 0 | Entirely per-logic |
| BigConj | 49 + scattered | 80-120 | Syntax + generic derivability lemmas |
| **Total** | **~2,900** | **~1,000-1,200** | |

The reduction from ~2,400 to ~1,000-1,200 is because:
- ContextualProofs (451 lines) is entirely per-logic
- Many Core.lean and Reasoning.lean theorems are context-based
- Proofs will be shorter in `DerivableIn` style (no explicit formula arguments to constructors)
- The "500 lines" BigConj estimate likely included derivation-level lemmas that are per-logic

## 9. Risk Assessment

### Low Risk
- Combinators port: Pure K+S+MP proofs, direct translation
- Axiom wrapper theorems (efq_axiom, peirce_axiom): Trivial
- Simple derived theorems (lem, raa, efq_neg, contrapose_imp): Straightforward

### Medium Risk
- `double_negation` proof: 7-step combinator proof, needs careful translation
- `rcp` (reverse contraposition): Complex combinator proof with DNI/DNE composition
- De Morgan laws: Multiple composition steps
- BigConj: Requires new syntactic definition plus lemmas

### High Risk
- `lce_imp` / `rce_imp` without deduction theorem: Requires novel combinator proof
- `classical_merge` without deduction theorem: Requires novel proof using Peirce
- `LukasiewiczDerived` definitional equality: Could cause unification issues if defaults are not used

### Mitigation
- Start with Combinators (lowest risk, highest value -- foundation for everything else)
- Prove lce_imp/rce_imp early since many other theorems depend on them
- Test `LukasiewiczDerived` unfolding behavior early in implementation
- If LukasiewiczDerived causes issues, work with raw `HasImp.imp phi HasBot.bot` patterns

## 10. Recommendations

1. **File structure**: Create `Cslib/Foundations/Logic/Theorems/` with `Combinators.lean`, `Propositional/Core.lean`, `Propositional/Connectives.lean`, `Propositional/Reasoning.lean`, and `BigConj.lean`.

2. **Phase order**: Combinators first (no dependencies), then Core (depends on Combinators), then Connectives (depends on Core), then Reasoning and BigConj.

3. **DT-free proofs**: Invest effort in proving `lce_imp`, `rce_imp`, and `classical_merge` without the deduction theorem. These unlock the rest of the connective theorems.

4. **Skip ContextualProofs entirely**: These are per-logic and will be reconstructed when concrete proof systems are instantiated.

5. **LukasiewiczDerived strategy**: Use `[LukasiewiczDerived F]` as an additional typeclass constraint and verify that the default implementations match. If they do not (because instances override defaults), define simp lemmas to normalize.

6. **Naming convention**: Use cslib naming (ImplyK, ImplyS) not BimodalLogic naming (prop_s, prop_k). Name theorems descriptively following Mathlib conventions (e.g., `PropositionalHilbert.imp_trans`, `PropositionalHilbert.identity`).
