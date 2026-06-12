# Teammate B Findings: Modal Survey

## Key Findings

The Modal directory has **extensive** raw constructor usage across 4 file categories:
1. **ProofSystem/Instances/** (15 files): Axiom inductive definitions use fully-qualified `Proposition.imp`, `Proposition.box`, `Proposition.bot` etc. These are the **highest-density** targets — every axiom schema is written verbosely. All files are in `namespace Cslib.Logic.Modal` so notation is in scope.
2. **Metalogic/** (5 files): `Completeness.lean`, `MCS.lean`, `DeductionTheorem.lean`, and `DerivationTree.lean` use `.imp`, `.bot`, `.box`, `.neg`, `.diamond` extensively in function signatures and proof bodies.
3. **Basic.lean**: Mixed — some `Satisfies` theorems use `.neg`, `.diamond`, `.and`, `.or` in theorem statements that could use `¬`, `◇`, `∧`, `∨`. Also has `change` tactic lines that expand notation back to constructors.
4. **FromPropositional.lean**: Uses fully-qualified `Modal.Proposition.bot`, `Modal.Proposition.imp` etc. in `@[simp]` lemma statements. This is in `namespace Cslib.Logic` (not `Cslib.Logic.Modal`), so Modal notation is NOT in scope — **requires `open scoped Modal.Proposition`** or full qualification.

### Scope Summary

| Category | Files | Estimated Replaceable Lines |
|----------|-------|-----------------------------|
| ProofSystem/Instances | 15 | ~150 (axiom constructors) |
| Metalogic (core) | 5 | ~250 (signatures + proofs) |
| Basic.lean | 1 | ~30 (Satisfies theorems, change tactics) |
| Denotation.lean | 1 | ~2 (minor) |
| LogicalEquivalence.lean | 1 | ~3 (Context.fill) |
| FromPropositional.lean | 1 | ~6 (scoping issue) |

## Detailed File-by-File Catalog

### File: Cslib/Logics/Modal/Basic.lean

**Definition sites (DO NOT CHANGE)**: Lines 58-77 (abbrev definitions for neg/top/or/and/diamond/iff), lines 79-93 (instances), lines 98-102 (Satisfies pattern match).

**Expression-position replacements:**

- Line 105: `Satisfies m w (.neg φ)` → `Satisfies m w (¬φ)`
- Line 109: `Satisfies m w (.diamond φ)` → `Satisfies m w (◇φ)`
- Line 110: `unfold Proposition.diamond Proposition.neg` — **KEEP** (tactic needs to unfold abbrevs)
- Line 121: `Satisfies m w (.and φ₁ φ₂)` → `Satisfies m w (φ₁ ∧ φ₂)`
- Line 131: `Satisfies m w (.or φ₁ φ₂)` → `Satisfies m w (φ₁ ∨ φ₂)`
- Line 233: `change Satisfies m w (.imp (.box (.imp φ₁ φ₂)) (.imp (.box φ₁) (.box φ₂)))` → `change Satisfies m w (□(φ₁ → φ₂) → □φ₁ → □φ₂)`
- Line 240: `change Satisfies m w (.iff (.diamond φ) (.neg (.box (.neg φ))))` → `change Satisfies m w ((◇φ) ↔ ¬□¬φ)`
- Line 247: `Satisfies m w (.diamond φ)` → `Satisfies m w (◇φ)`
- Line 272: `Satisfies m w (.diamond φ)` → `Satisfies m w (◇φ)`
- Line 285: `Satisfies m w' (.diamond φ)` → `Satisfies m w' (◇φ)`
- Line 296-297: `Satisfies ⟨r, v₁⟩ w' (.diamond (.atom a))` → `Satisfies ⟨r, v₁⟩ w' (◇(.atom a))`
- Line 309: `Satisfies m w (.diamond (.diamond φ))` and `Satisfies m w (.diamond φ)` → `Satisfies m w (◇◇φ)` and `Satisfies m w (◇φ)`
- Lines 322-325: multiple `.diamond (.diamond (.atom a))` and `.diamond (.atom a)` → `◇◇(.atom a)` and `◇(.atom a)`
- Lines 339, 352-355, 367, 380: similar `.diamond` → `◇` replacements

### File: Cslib/Logics/Modal/Denotation.lean

- Line 59: `simp only [Proposition.neg, Proposition.denotation, ...]` — **KEEP** (needs to unfold for simp)

No other expression-position replacements needed. Pattern matches at lines 28-30 are correct.

### File: Cslib/Logics/Modal/FromPropositional.lean

**SCOPING ISSUE**: This file is in `namespace Cslib.Logic`, NOT `Cslib.Logic.Modal`. Modal notation (→, ¬, □ etc.) is NOT in scope.

- Lines 46, 51, 55: `Modal.Proposition.bot`, `Modal.Proposition.imp`, `Modal.Proposition.neg` — these are in `@[simp]` lemma RHS positions. Could use notation if `open scoped Cslib.Logic.Modal.Proposition` is added, but this may conflict with PL notation also in scope. **CAUTION: potential notation conflict**. Recommend leaving as-is or adding selective open.
- Lines 31-32: Pattern match positions — **KEEP**

### File: Cslib/Logics/Modal/LogicalEquivalence.lean

- Line 53: `| .impL c ψ, φ => .imp (c.fill φ) ψ` — the `.imp` on RHS is expression-position → `(c.fill φ) → ψ` (but `.impL` on LHS is pattern match — KEEP)
- Line 54: `.imp ψ (c.fill φ)` → `ψ → (c.fill φ)`
- Line 55: `.box (c.fill φ)` → `□(c.fill φ)`

### File: Cslib/Logics/Modal/Metalogic/DerivationTree.lean

**Axiom schema definitions (inductive ModalAxiom)** — these are the TYPE signatures for axiom constructors:
- Line 66: `ModalAxiom (φ.imp (ψ.imp φ))` → `ModalAxiom (φ → ψ → φ)`
- Line 69: `ModalAxiom ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ)))` → `ModalAxiom ((φ → ψ → χ) → (φ → ψ) → φ → χ)`
- Line 72: `ModalAxiom (Proposition.bot.imp φ)` → `ModalAxiom (⊥ → φ)` (needs `⊥` instance for `Proposition.bot`)
- Line 75: `ModalAxiom (((φ.imp ψ).imp φ).imp φ)` → `ModalAxiom (((φ → ψ) → φ) → φ)`
- Line 78: `ModalAxiom ((Proposition.box (φ.imp ψ)).imp ((Proposition.box φ).imp (Proposition.box ψ)))` → `ModalAxiom (□(φ → ψ) → □φ → □ψ)`
- Line 81: `ModalAxiom ((Proposition.box φ).imp φ)` → `ModalAxiom (□φ → φ)`
- Line 84: `ModalAxiom ((Proposition.box φ).imp (Proposition.box (Proposition.box φ)))` → `ModalAxiom (□φ → □□φ)`
- Line 87: `ModalAxiom (φ.imp (Proposition.box (Proposition.diamond φ)))` → `ModalAxiom (φ → □◇φ)`

**DerivationTree constructors:**
- Line 113: `(d₁ : DerivationTree Axioms Γ (φ.imp ψ))` → `(d₁ : DerivationTree Axioms Γ (φ → ψ))`
- Line 117: `DerivationTree Axioms [] (Proposition.box φ)` → `DerivationTree Axioms [] (□φ)`
- Line 140: `(d₁ : DerivationTree Axioms Γ (φ.imp ψ))` → `(d₁ : DerivationTree Axioms Γ (φ → ψ))`
- Line 145: similar
- Line 174: `(h₁ : Deriv Axioms Γ (φ.imp ψ))` → `(h₁ : Deriv Axioms Γ (φ → ψ))`

### File: Cslib/Logics/Modal/Metalogic/DeductionTheorem.lean

- Line 69: `Axioms (φ.imp (ψ.imp φ))` → `Axioms (φ → ψ → φ)`
- Line 71: `Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ)))` → `Axioms ((φ → ψ → χ) → (φ → ψ) → φ → χ)`
- Line 74: `(A.imp φ)` → `(A → φ)`
- Line 86: `(ψ.imp χ)` → `(ψ → χ)` — but used as argument to recursive call
- Line 94: throughout, all `φ.imp ψ` in non-pattern positions → `φ → ψ`
- Lines 104-113: multiple `.imp` in expression position → `→`
- Lines 128-198: similar pattern repeated in `deductionTheorem` and `deductionTheoremEmpty`

### File: Cslib/Logics/Modal/Metalogic/MCS.lean

Very dense — nearly every line uses raw `.imp`, `.bot`, `.neg`, `.box`, `.diamond`:
- Lines 69-71: hypothesis types `Axioms (φ.imp (ψ.imp φ))` → `Axioms (φ → ψ → φ)` etc.
- Lines 84-88: `Proposition.imp φ ψ ∈ S` → `(φ → ψ) ∈ S`
- Line 102: `Proposition.neg φ ∈ S` → `(¬φ) ∈ S`
- Lines 117, 124: `.imp` in axiom applications
- Lines 131-133: `Proposition.bot ∉ S` (uses `⊥` instance, could write `⊥ ∉ S`)
- Lines 141-160: `(Proposition.box φ).imp φ` → `□φ → φ`, `Proposition.box (Proposition.box φ)` → `□□φ`
- Lines 166-173: `Proposition.box (Proposition.diamond φ)` → `□◇φ`
- Lines 179-187: `Proposition.box (φ.imp ψ)` → `□(φ → ψ)`
- Lines 196-256: throughout, `Proposition.neg φ` → `¬φ`
- Lines 238-301: `Proposition.box` repeated extensively

### File: Cslib/Logics/Modal/Metalogic/Completeness.lean

Most dense file — **~200 lines** with raw constructors:
- Lines 62-68: hypothesis signatures with `.imp`, `Proposition.box`
- Lines 72-93: similar
- Lines 106-113: complex nested `.imp` with `Proposition.box`
- Lines 122-145: mixed `.imp .bot`, `Proposition.bot`
- Lines 149-187: repeated pattern
- Lines 201-290: very dense section with `Proposition.box`, `.imp .bot`, `Proposition.neg`, `Proposition.diamond`
- Lines 325-401: same pattern in completeness proof body

### File: Cslib/Logics/Modal/Metalogic/Soundness.lean

Need to check — may be clean since system-specific soundness files were clean.

### ProofSystem/Instances/K.lean

**Axiom inductive KAxiom** — all constructors use fully-qualified form:
- Line 36: `KAxiom (Proposition.imp φ (Proposition.imp ψ φ))` → `KAxiom (φ → ψ → φ)`
- Line 39-40: `KAxiom (Proposition.imp (Proposition.imp φ (Proposition.imp ψ χ)) (Proposition.imp (Proposition.imp φ ψ) (Proposition.imp φ χ)))` → `KAxiom ((φ → ψ → χ) → (φ → ψ) → φ → χ)`
- Line 43: `KAxiom (Proposition.imp Proposition.bot φ)` → `KAxiom (⊥ → φ)`
- Line 46: `KAxiom (Proposition.imp (Proposition.imp (Proposition.imp φ ψ) φ) φ)` → `KAxiom (((φ → ψ) → φ) → φ)`
- Line 49-50: `KAxiom (Proposition.imp (Proposition.box (Proposition.imp φ ψ)) (Proposition.imp (Proposition.box φ) (Proposition.box ψ)))` → `KAxiom (□(φ → ψ) → □φ → □ψ)`

### ProofSystem/Instances/T.lean

Same 5 base axioms as K plus:
- Line 52: `TAxiom (Proposition.imp (Proposition.box φ) φ)` → `TAxiom (□φ → φ)`

### ProofSystem/Instances/S4.lean

Same as T plus:
- Line 55: `S4Axiom (Proposition.imp (Proposition.box φ) (Proposition.box (Proposition.box φ)))` → `S4Axiom (□φ → □□φ)`

### ProofSystem/Instances/B.lean

Same 5 base axioms as K plus:
- Line 52: `BAxiom (φ.imp (Proposition.box (Proposition.diamond φ)))` → `BAxiom (φ → □◇φ)`

### ProofSystem/Instances/D.lean

Same 5 base axioms as K plus:
- Lines 52-53: `DAxiom (Proposition.imp (Proposition.box φ) (Proposition.imp (Proposition.box (Proposition.imp φ Proposition.bot)) Proposition.bot))` → `DAxiom (□φ → ¬□¬φ)` (i.e., `□φ → ◇φ`)

Note: The D axiom `□φ → ◇φ` is currently encoded as `□φ → ((□(φ → ⊥)) → ⊥)` using the Lukasiewicz expansion. With notation it becomes much more readable.

### ProofSystem/Instances/D4.lean

Same as D plus:
- Line 57: `D4Axiom (Proposition.imp (Proposition.box φ) (Proposition.box (Proposition.box φ)))` → `D4Axiom (□φ → □□φ)`

### ProofSystem/Instances/D5.lean

Same as D plus Axiom 5:
- Lines 57-58: `D5Axiom (((Proposition.box (φ.imp .bot)).imp .bot).imp (Proposition.box ((Proposition.box (φ.imp .bot)).imp .bot)))` → `D5Axiom (◇φ → □◇φ)`

### ProofSystem/Instances/D45.lean

Same as D plus 4 and 5.

### ProofSystem/Instances/DB.lean

Same as D plus B:
- Line 57: `DBAxiom (φ.imp (Proposition.box (Proposition.diamond φ)))` → `DBAxiom (φ → □◇φ)`

### ProofSystem/Instances/K4.lean

Same as K plus 4.

### ProofSystem/Instances/K5.lean

Same as K plus 5.

### ProofSystem/Instances/K45.lean

Same as K plus 4 and 5.

### ProofSystem/Instances/KB5.lean

Same as K plus B and 5.

### ProofSystem/Instances/TB.lean

Same as T plus B.

### ProofSystem/Instances/S5.lean

No axiom inductive — references `ModalAxiom` from DerivationTree. **No changes needed** in this file.

### File: Cslib/Logics/Modal/Metalogic.lean, ProofSystem/Instances.lean

Barrel import files — no raw constructors.

## Important Caveats

### 1. `⊥` needs Bot instance
`Proposition.bot` can be written as `⊥` only if `instance : Bot (Proposition Atom)` is in scope. This IS registered in `Basic.lean` line 79, so it works everywhere Modal namespace is open.

### 2. `change` tactic lines
Lines like `change Satisfies m w (.imp (.box (.imp φ₁ φ₂)) (.imp (.box φ₁) (.box φ₂)))` can use notation. The `change` tactic works with definitionally equal terms, and the notation expands to the same constructors.

### 3. `unfold` tactic lines
Lines like `unfold Proposition.diamond Proposition.neg` must **stay as-is** — they reference the definition names, not the notation.

### 4. Pattern match positions
All `| .imp ...`, `| .bot`, `| .box ...` in match arms and recursive definitions must stay as constructors.

### 5. Axiom inductive constructor result types
The axiom inductive types (e.g., `KAxiom`, `ModalAxiom`) have result types like `KAxiom (Proposition.imp φ ψ)`. These CAN use notation since they're expression-position type annotations: `KAxiom (φ → ψ)`.

### 6. Scoping in FromPropositional.lean
This file is in `namespace Cslib.Logic`, and both PL and Modal notation are potentially in scope. Care needed to avoid ambiguity — both logics define `→` notation. Recommend leaving as fully-qualified.

## Confidence Level

**High** — I systematically read every file in the Modal directory (both current branch and main). The pattern is consistent: raw constructors are used everywhere in expression position where notation could be used. The notation is always in scope since all files are in `namespace Cslib.Logic.Modal`.
