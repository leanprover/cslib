# Teammate A Findings: Propositional + Foundations Survey

## Key Findings

1. **Propositional/ directory**: ~340 raw constructor usages, of which ~12 are legitimate pattern matches and ~9 are definition/notation sites. This leaves **~320 expression-position usages** that could use notation (`→`, `∧`, `∨`, `¬`, `⊥`).

2. **Foundations/Logic/ directory**: ~750 usages of `HasImp.imp`, `HasBot.bot`, `HasBox.box` etc. These are **typeclass method calls** on a polymorphic type `F`, not concrete constructor calls. Currently **no notation exists** for these. Adding notation (e.g., `φ ⟶ ψ` for `HasImp.imp φ ψ`) would dramatically improve readability of the Foundations layer, but is a separate design decision.

3. **Most impactful files** (by count of replaceable usages):
   - `Metalogic/Completeness.lean`: ~60 usages
   - `Metalogic/IntLindenbaum.lean`: ~40 usages
   - `Metalogic/MinLindenbaum.lean`: ~35 usages
   - `Metalogic/MCS.lean`: ~30 usages
   - `NaturalDeduction/DerivedRules.lean`: ~30 usages
   - `NaturalDeduction/HilbertDerivedRules.lean`: ~40 usages
   - `NaturalDeduction/FromHilbert.lean`: ~30 usages
   - `NaturalDeduction/Equivalence.lean`: ~15 usages
   - `ProofSystem/Axioms.lean`: ~15 usages
   - `ProofSystem/Derivation.lean`: ~10 usages
   - `Metalogic/DeductionTheorem.lean`: ~30 usages

4. **Key replacement patterns**:
   - `φ.imp ψ` / `.imp φ ψ` → `φ → ψ` (most common, ~200+ occurrences)
   - `Proposition.bot` / `.bot` → `⊥` (~50 occurrences)
   - `Proposition.neg φ` / `.neg φ` → `¬φ` (~30 occurrences)
   - `φ.and ψ` / `.and φ ψ` → `φ ∧ ψ` (~15 occurrences)
   - `φ.or ψ` / `.or φ ψ` → `φ ∨ ψ` (~10 occurrences)
   - `Proposition.bot.imp φ` → `⊥ → φ` (EFQ pattern, ~20 occurrences)

## Detailed File-by-File Catalog

### Propositional/ Files

---

### File: Cslib/Logics/Propositional/ProofSystem/Axioms.lean

These are inside `inductive` constructor result types — they ARE expression-position but define the axiom schema. Using notation here would make the axioms more readable and match their docstrings.

- Line 44: `PropositionalAxiom (φ.imp (ψ.imp φ))` → `PropositionalAxiom (φ → ψ → φ)`
- Line 47: `PropositionalAxiom ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ)))` → `PropositionalAxiom ((φ → ψ → χ) → (φ → ψ) → φ → χ)`
- Line 50: `PropositionalAxiom (Proposition.bot.imp φ)` → `PropositionalAxiom (⊥ → φ)`
- Line 53: `PropositionalAxiom (((φ.imp ψ).imp φ).imp φ)` → `PropositionalAxiom (((φ → ψ) → φ) → φ)`
- Line 66: `IntPropAxiom (φ.imp (ψ.imp φ))` → `IntPropAxiom (φ → ψ → φ)`
- Line 69: `IntPropAxiom ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ)))` → `IntPropAxiom ((φ → ψ → χ) → (φ → ψ) → φ → χ)`
- Line 72: `IntPropAxiom (Proposition.bot.imp φ)` → `IntPropAxiom (⊥ → φ)`
- Line 84: `MinPropAxiom (φ.imp (ψ.imp φ))` → `MinPropAxiom (φ → ψ → φ)`
- Line 87: `MinPropAxiom ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ)))` → `MinPropAxiom ((φ → ψ → χ) → (φ → ψ) → φ → χ)`

---

### File: Cslib/Logics/Propositional/ProofSystem/Derivation.lean

- Line 77: `(d₁ : DerivationTree Axioms Γ (φ.imp ψ))` → `(d₁ : DerivationTree Axioms Γ (φ → ψ))`
- Line 100: `(d₁ : DerivationTree Axioms Γ (φ.imp ψ))` → `(d₁ : DerivationTree Axioms Γ (φ → ψ))`
- Line 105: `(d₁ : DerivationTree Axioms Γ (φ.imp ψ))` → `(d₁ : DerivationTree Axioms Γ (φ → ψ))`
- Line 134: `(h₁ : Deriv Axioms Γ (φ.imp ψ))` → `(h₁ : Deriv Axioms Γ (φ → ψ))`

---

### File: Cslib/Logics/Propositional/Metalogic/Completeness.lean

- Line 44: `PropositionalAxiom (φ.imp (ψ.imp φ))` → `PropositionalAxiom (φ → ψ → φ)`
- Line 52: `((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ)))` → `((φ → ψ → χ) → (φ → ψ) → φ → χ)`
- Line 89: `(φ.imp ψ)` → `(φ → ψ)` (multiple on this line)
- Line 97: `(L := [(φ.imp ψ).imp .bot])` → `(L := [(φ → ψ) → ⊥])` (note: `.imp .bot` = `→ ⊥` = `¬`)
- Line 108: `[φ.imp ψ, (φ.imp ψ).imp .bot]` → `[φ → ψ, ¬(φ → ψ)]`
- Line 109: `Proposition.bot` → `⊥`
- Line 110: `.modus_ponens _ (φ.imp ψ) .bot` → `.modus_ponens _ (φ → ψ) ⊥`
- Line 118: `[φ.imp ψ, (φ.imp ψ).imp .bot] φ` → `[φ → ψ, ¬(φ → ψ)] φ`
- Line 119: `.modus_ponens _ .bot φ` → `.modus_ponens _ ⊥ φ`
- Line 125-133: Multiple `.imp` and `.bot` usages → use `→` and `⊥`
- Line 147-183: Multiple `.imp .bot` patterns → use `¬` and `→`
- Line 209: `({Proposition.neg φ} :` → keep `Proposition.neg` or use `({¬φ} :`
- Line 215-218: `[Proposition.neg φ] Proposition.bot` → `[¬φ] ⊥`, `.bot` → `⊥`
- Line 225: `(Proposition.neg φ) .bot` → `(¬φ) ⊥` or `¬φ → ⊥`
- Line 227: `Proposition.neg φ` → `¬φ`
- Line 230-254: Extensive `.imp`, `Proposition.bot`, `neg_phi` usages → use `→`, `⊥`, `¬`
- Line 267: `((φ.imp Proposition.bot).imp φ).imp φ` → `((φ → ⊥) → φ) → φ`
- Line 268: `.peirce φ Proposition.bot` → `.peirce φ ⊥` (note: `⊥` is `Proposition.bot` but with `Bot` instance)
- Line 278: `Proposition.neg φ` → `¬φ`
- Line 283: `(Proposition.neg φ)` → `(¬φ)`

---

### File: Cslib/Logics/Propositional/Metalogic/DeductionTheorem.lean

- Line 73: `Axioms (φ.imp (ψ.imp φ))` → `Axioms (φ → ψ → φ)`
- Line 75: `Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ)))` → notation
- Line 78: `(A.imp φ)` → `(A → φ)`
- Line 98: `(ψ.imp χ)` → `(ψ → χ)`
- Line 106: `(A.imp ψ)` → `(A → ψ)`
- Line 111: `(ψ.imp (A.imp ψ))` → `(ψ → A → ψ)`
- Line 115: `ψ (A.imp ψ)` → `ψ (A → ψ)`
- Line 130-135: Multiple `.imp` → `→`
- Line 158-181: Multiple `.imp` → `→`
- Line 198-200: Multiple `.imp` → `→`

---

### File: Cslib/Logics/Propositional/Metalogic/MCS.lean

- Line 68: `Axioms (φ.imp (ψ.imp φ))` → `Axioms (φ → ψ → φ)`
- Line 70: `Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ)))` → notation
- Line 83-85: Same pattern repeated for another theorem
- Line 88: `Proposition.imp φ ψ ∈ S` → `(φ → ψ) ∈ S`
- Line 97-99: Same `h_implyK`/`h_implyS` pattern
- Line 101: `Proposition.neg φ ∈ S` → `¬φ ∈ S`
- Line 113: `Proposition.bot ∉ S` → `⊥ ∉ S`
- Line 115: `h_mcs.1 [Proposition.bot]` → `h_mcs.1 [⊥]`
- Line 123-127: Same `h_implyK`/`h_implyS` + `Proposition.neg φ` → `¬φ`
- Line 135-139: Same pattern
- Line 147-151: Same pattern

---

### File: Cslib/Logics/Propositional/Metalogic/IntLindenbaum.lean

- Line 36: `IntPropAxiom (φ.imp (ψ.imp φ))` → `IntPropAxiom (φ → ψ → φ)`
- Line 41: `IntPropAxiom ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ)))` → notation
- Line 56: `Proposition.bot ∉ S` → `⊥ ∉ S`
- Line 58: `h.1 [Proposition.bot]` → `h.1 [⊥]`
- Line 65: `φ.imp ψ ∈ S` → `(φ → ψ) ∈ S`
- Line 66: `h [φ.imp ψ, φ]` → `h [φ → ψ, φ]`
- Line 80-92: Multiple `.imp`, `.bot`, `Proposition.neg`, `Proposition.bot.imp` → notation
- Line 98: `(φ.imp ψ)` → `(φ → ψ)`
- Line 107-124: Multiple `.imp` → `→`
- Line 134-185: Extensive `.imp` patterns → `→`
- Line 246-254: `.imp`, `Proposition.neg` → `→`, `¬`
- Line 283: `Proposition.bot` → `⊥`

---

### File: Cslib/Logics/Propositional/Metalogic/MinLindenbaum.lean

Very similar to IntLindenbaum — same patterns with `MinPropAxiom` instead of `IntPropAxiom`.

- Line 48: `MinPropAxiom (φ.imp (ψ.imp φ))` → notation
- Line 53: Distribution axiom → notation
- Lines 73-74, 107, 134-167, 213, 248: Same `.imp` → `→` patterns

---

### File: Cslib/Logics/Propositional/Metalogic/IntCompleteness.lean

- Line 92: `h_imp_T : φ.imp ψ ∈ T.val` → `(φ → ψ) ∈ T.val`
- Lines 74, 78: Pattern matches (`.bot`, `.imp`) — keep as-is

---

### File: Cslib/Logics/Propositional/Metalogic/MinCompleteness.lean

- Line 72: `Proposition.bot ∈ w.val` → `⊥ ∈ w.val`
- Line 107: `φ.imp ψ ∈ T.val` → `(φ → ψ) ∈ T.val`
- Lines 92-93: Pattern matches — keep as-is

---

### File: Cslib/Logics/Propositional/NaturalDeduction/DerivedRules.lean

- Line 82: `Proposition.neg A` → `¬A`
- Line 90: `Proposition.neg A` → `¬A`
- Line 114: `A.and B` → `A ∧ B`
- Line 130: `Proposition.neg (Proposition.neg A)` → `¬¬A`
- Line 144: `A.and B` → `A ∧ B`
- Line 150: `(A := Proposition.neg A)` → `(A := ¬A)`
- Line 154: `(B := Proposition.bot)` → `(B := ⊥)`
- Line 175: `A.and B` → `A ∧ B`
- Line 181: `(A := Proposition.neg B)` → `(A := ¬B)`
- Line 185: `(B := Proposition.bot)` → `(B := ⊥)`
- Line 191-192: `Proposition.neg B` → `¬B`
- Line 203: `A.or B` → `A ∨ B`
- Line 221: `A.or B` → `A ∨ B`
- Line 233: `A.or B` → `A ∨ B`
- Line 238: `A.imp C` → `A → C`
- Line 240: `B.imp C` → `B → C`
- Line 242: `Proposition.neg A |>.imp C` → `(¬A) → C` or `¬A → C`
- Line 247: `(A := Proposition.neg A)` → `(A := ¬A)`
- Line 253: `(A := Proposition.neg C)` → `(A := ¬C)`
- Line 256: `Proposition.neg C` → `¬C`
- Line 265: `Proposition.neg C` → `¬C`
- Line 280-281: `A.imp B`, `B.imp A` → `A → B`, `B → A`
- Line 291: `A.imp B` → `A → B`
- Line 300: `B.imp A` → `B → A`
- Line 308: `Proposition.neg A` → `¬A`
- Line 313: `Proposition.neg A` → `¬A`
- Line 327: `A.and B` → `A ∧ B`
- Line 332, 338: `A.and B` → `A ∧ B`
- Line 345, 351: `A.or B` → `A ∨ B`
- Line 364: `Proposition.neg (Proposition.neg A)` → `¬¬A`
- Line 370-371: `A.imp B`, `B.imp A` → `A → B`, `B → A`
- Line 378: `A.imp B` → `A → B`
- Line 384: `B.imp A` → `B → A`

---

### File: Cslib/Logics/Propositional/NaturalDeduction/HilbertDerivedRules.lean

- Line 66-68: `h_implyK`/`h_implyS` patterns → notation
- Line 71-72: `Proposition.bot`, `Proposition.neg A` → `⊥`, `¬A`
- Line 83-85: Same patterns
- Line 95-99: `Proposition.bot.imp φ` → `⊥ → φ`, `Proposition.bot` → `⊥`
- Line 111-118: Multiple `.imp` → `→`, `A.and B` → `A ∧ B`
- Line 138-145: Same pattern + `A.or B` → `A ∨ B`
- Line 162-169: `A.or B` → `A ∨ B`, `.imp Proposition.bot` → `→ ⊥`
- Line 180-186: `.imp` → `→`
- Line 195-201: `Proposition.bot`, `Proposition.neg A` → `⊥`, `¬A`
- Line 209-211: `Proposition.neg A`, `Proposition.bot` → `¬A`, `⊥`
- Line 217: `Proposition.bot.imp φ` → `⊥ → φ`
- Line 225-232: Multiple patterns
- Line 238-244: Multiple patterns
- Line 250-253: Multiple patterns
- Line 259-261: Multiple patterns

---

### File: Cslib/Logics/Propositional/NaturalDeduction/FromHilbert.lean

- Line 73-75: `h_implyK`/`h_implyS` patterns → notation
- Line 79: `A.imp B` → `A → B`
- Line 88: `A.imp B` → `A → B`
- Line 99: `Proposition.bot.imp φ` → `⊥ → φ`
- Line 102: `Proposition.bot` → `⊥`
- Line 104: `Proposition.bot A` → `⊥`
- Line 137-139: Same patterns
- Line 151: `A.imp B` → `A → B`
- Line 173-179: Same patterns
- Line 188-200: Same patterns
- Line 208-210: Same patterns

---

### File: Cslib/Logics/Propositional/NaturalDeduction/Equivalence.lean

- Line 144: `Axioms (φ.imp (ψ.imp φ))` → notation
- Line 146: Distribution axiom → notation
- Line 147: `Proposition.bot.imp φ` → `⊥ → φ`
- Line 172-175: Same patterns
- Line 191-194: Same patterns

---

### File: Cslib/Logics/Propositional/Defs.lean

Most are definition sites (keep as-is) or pattern matches (keep as-is).

- Line 78: `(A.imp B).and (B.imp A)` → `(A → B) ∧ (B → A)` (in `iff` definition — arguable, since it defines the abbrev using other abbrevs)
- Line 123: `Set.range (Proposition.imp ⊥ ·)` → this already uses `⊥` but uses `Proposition.imp` — could be `Set.range (· → ⊥)` but semantics differ; keep as-is or use `Set.range (⊥ → ·)` if scoped notation is open

---

### File: Cslib/Logics/Propositional/Semantics/Basic.lean

- Lines 40-41: Pattern matches in `Evaluate` — keep as-is

---

### File: Cslib/Logics/Propositional/Semantics/Kripke.lean

- Lines 83-84: Pattern matches in `IForces` — keep as-is

---

### Foundations/Logic/ Files

---

### File: Cslib/Foundations/Logic/Connectives.lean

All usages are in class definitions (`LukasiewiczDerived`) — these ARE the typeclass method definitions. Keep as-is.

---

### File: Cslib/Foundations/Logic/Axioms.lean

~40 usages of `HasImp.imp`, `HasBot.bot`, `HasBox.box`. These are **polymorphic** axiom definitions operating on abstract type `F`. Currently NO notation for these. If notation were added (e.g., `φ ⟶ ψ` for `HasImp.imp φ ψ`, `⊥ₗ` for `HasBot.bot`, `□ₗ` for `HasBox.box`), all lines would benefit. However, this is a design decision for the Foundations layer.

Example replaceable lines (if notation were created):
- Line 64: `HasImp.imp φ (HasImp.imp ψ φ)` → `φ ⟶ ψ ⟶ φ`
- Line 68-69: `HasImp.imp (HasImp.imp φ (HasImp.imp ψ χ)) ...` → nested `⟶`
- Lines 73, 77, 82, 93-121: All similar

---

### File: Cslib/Foundations/Logic/Metalogic/Consistency.lean

~20 usages of `HasImp.imp`, `HasBot.bot`. Same as Axioms.lean — polymorphic, no notation exists.

---

### File: Cslib/Foundations/Logic/Metalogic/DeductionHelpers.lean

~15 usages of `HasImp.imp`. Same situation.

---

### File: Cslib/Foundations/Logic/ProofSystem.lean

~12 usages of `HasImp.imp`, `HasBot.bot`, `HasBox.box`, `HasUntil.untl`, `HasSince.snce`. Same situation.

---

### File: Cslib/Foundations/Logic/Theorems/Combinators.lean

**~60 usages** of `HasImp.imp` — this is the most heavily affected Foundations file. Extremely dense with nested `HasImp.imp` calls that would be dramatically more readable with notation.

---

### File: Cslib/Foundations/Logic/Theorems/Propositional/Core.lean

~50 usages of `HasImp.imp`, `HasBot.bot`. Very dense negation/conjunction proofs.

---

### File: Cslib/Foundations/Logic/Theorems/Propositional/Connectives.lean

~40 usages. Dense biconditional/contrapositive proofs.

---

### File: Cslib/Foundations/Logic/Theorems/Modal/Basic.lean

~50 usages of `HasImp.imp`, `HasBot.bot`, `HasBox.box`. Modal K distribution and contraposition proofs.

---

### File: Cslib/Foundations/Logic/Theorems/Modal/S5.lean

~60 usages. S5 diamond/four proofs, extremely dense.

---

### File: Cslib/Foundations/Logic/Theorems/Temporal/TemporalDerived.lean

~40 usages. Temporal operator distribution proofs.

---

### File: Cslib/Foundations/Logic/Theorems/BigConj.lean

~15 usages. Big conjunction definitions and lemmas.

---

## Summary of Replaceable Patterns

### Propositional/ (immediate, scoped notation already exists)

| Pattern | Replacement | Count (approx) |
|---------|-------------|----------------|
| `φ.imp ψ` / `.imp φ ψ` | `φ → ψ` | ~200 |
| `Proposition.bot` / `.bot` | `⊥` | ~50 |
| `Proposition.neg φ` | `¬φ` | ~30 |
| `φ.and ψ` | `φ ∧ ψ` | ~15 |
| `φ.or ψ` | `φ ∨ ψ` | ~10 |
| `Proposition.bot.imp φ` | `⊥ → φ` | ~15 |
| **Total** | | **~320** |

### Foundations/Logic/ (requires new notation design)

| Pattern | Potential Replacement | Count (approx) |
|---------|----------------------|----------------|
| `HasImp.imp φ ψ` | New notation needed | ~400 |
| `HasBot.bot` | New notation needed | ~150 |
| `HasBox.box φ` | New notation needed | ~80 |
| `HasUntil.untl` / `HasSince.snce` | New notation needed | ~30 |
| **Total** | | **~660** |

## Recommendations

1. **Phase 1 (immediate)**: Replace all ~320 expression-position raw constructors in Propositional/ with existing scoped notation. This is safe and unambiguous since all files open `Cslib.Logic.PL` namespace.

2. **Phase 2 (design decision)**: Consider adding notation for the Foundations/Logic polymorphic layer. This would transform ~660 usages and dramatically improve readability of dense proof files like `Combinators.lean` and `Modal/S5.lean`. Possible notation: reuse `→`, `⊥`, `¬`, `□` via typeclass instances, OR use distinct symbols (`⟶`, `⊥ₗ`).

## Confidence Level

**High** for the Propositional/ catalog — every file was read and usages identified.
**High** for the Foundations/ assessment — scope and pattern clear, but exact line counts are approximate since many files are very large.
