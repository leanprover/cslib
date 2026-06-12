# Teammate C Findings: Critic Analysis

## Part 1: Temporal Survey

### Scope
Temporal files total **~1,845 expression-position** raw constructor occurrences across 31 files. The heaviest files:

| File | Count | Notes |
|------|-------|-------|
| `Chronicle/PointInsertion.lean` | 664 | Massive; deep structural manipulation |
| `Chronicle/CounterexampleElimination.lean` | 173 | |
| `Chronicle/RRelation.lean` | 139 | |
| `Metalogic/MCS.lean` | 123 | |
| `Metalogic/CompletenessHelpers.lean` | 86 | |
| `Metalogic/TemporalContent.lean` | 86 | |
| `Chronicle/ChronicleConstruction.lean` | 82 | |
| `Syntax/Formula.lean` | 52 | Includes definitions (partially exempt) |
| `Metalogic/WitnessSeed.lean` | 50 | |
| `ProofSystem/Axioms.lean` | 48 | |

### Available Notation (scoped to `Cslib.Logic.Temporal`)
- `→ ∧ ∨ ¬ ↔ ⊥` — propositional connectives
- `U S` — until and since (plain ASCII infix)
- `𝐅 𝐆 𝐏 𝐇` — temporal operators (Unicode bold)
- `△ ▽` — always/sometimes

### Replaceable Patterns in Temporal/

**Derived operator definitions** (lines 397–443 of `Formula.lean`): These use fully-qualified `Formula.and`, `Formula.neg`, `Formula.or`, `Formula.untl`, `Formula.snce` etc. in expression position. Example:
```lean
def release (φ ψ : Formula Atom) : Formula Atom :=
  Formula.neg (Formula.untl (Formula.neg ψ) (Formula.neg φ))
-- Could be: ¬(¬ψ U ¬φ)
```

**Theorem statement types** (widespread): Uses like `(Formula.neg φ).swapTemporal` could be `(¬φ).swapTemporal` or `swapTemporal (¬φ)`.

**Simp lemma statements** (lines 537–550): `(Formula.bot : Formula Atom)` could use `⊥`, `(Formula.imp p q)` could use `p → q`, etc.

### NOT Replaceable in Temporal/

- **Pattern match arms** (~85 occurrences): `| .imp φ ψ =>`, `| .bot =>`, etc.
- **`congrArg₂` arguments** (lines 192, 202, 212): `congrArg₂ Formula.imp` requires the constructor name
- **Complexity function patterns** (lines 331–357): Deep structural matching like `| .imp (.untl (.imp φ .bot) (.imp .bot .bot)) .bot =>` — these match the definitional expansion and MUST use raw constructors
- **`encodeNat` function** (lines 153–158): Constructor-level encoding, must distinguish by constructor tag

---

## Part 2: Risk Analysis

### Risk 1: Pattern Match Arms (SAFE — no change needed)
**Severity**: N/A (universally understood)

Pattern match arms like `| .imp A B =>` MUST keep raw constructors. This is standard Lean — notation cannot appear on the left side of `=>` in a `match`. Approximately **525 pattern match lines** across all Logics/ directories. These are correctly excluded from replacement scope.

### Risk 2: `unfold` Dependencies (LOW risk)
**Severity**: Low

Found 7 `unfold` sites across all Logics/:
- `Cslib/Logics/Modal/Basic.lean:110` — `unfold Proposition.diamond Proposition.neg`
- `Cslib/Logics/Bimodal/` — 5 occurrences (`Formula.diamond`, `Formula.or`, `Formula.somePast`, `Formula.someFuture`, `Formula.top`)

These `unfold` calls reference the **definition name**, not the notation. Replacing the _input expression_ (what appears before the `unfold`) with notation is safe because `unfold` operates on the definition name in its argument, not on the syntactic form of the goal. For example:
```lean
-- Before:
show Satisfies m w (.diamond φ)  -- ← this can use ◇φ
unfold Proposition.diamond       -- ← this references the def name, stays unchanged
```
However, if the GOAL displayed after `unfold` is referenced in subsequent tactics with raw constructors, those would also need updating. **Recommendation**: Test each `unfold` site individually.

### Risk 3: `show` Targets (LOW risk)
**Severity**: Low

Found ~20 `show` sites using raw constructors (mostly in Bimodal). Since `abbrev` definitions are definitionally transparent, `show Satisfies m w (¬φ)` and `show Satisfies m w (.neg φ)` are interchangeable. Lean's elaborator unfolds both to the same term. **Safe to replace**.

### Risk 4: Scoping Issues (MEDIUM risk — requires care)
**Severity**: Medium

**Three files explicitly avoid opening their own namespace** to prevent notation conflicts:
1. `Cslib/Logics/Temporal/ProofSystem/Instances.lean` — "Do not open Cslib.Logic.Temporal to avoid scoped notation conflicts (F, G, H, P, S, U are all scoped notation)"
2. `Cslib/Logics/Bimodal/ProofSystem/Instances.lean` — "Do not open Cslib.Logic.Bimodal to avoid scoped notation conflicts"
3. `Cslib/Logics/Bimodal/Theorems/Perpetuity/Helpers.lean` — same

In these files, notation `→ ∧ ∨ ¬` is **NOT available** because the scoped notation isn't brought into scope. Raw constructors must stay in these files.

**However**: The `namespace` keyword also brings scoped notation into scope. Most Temporal/Modal files use `namespace Cslib.Logic.Temporal` or `namespace Cslib.Logic.Modal`, which DOES activate the notation. So the vast majority of files can use notation.

**Cross-namespace references**: A file working in `Cslib.Logic.Modal` that references `PL.Proposition` would not have PL's `→` notation. But this is rare — each logic level works with its own formula type.

### Risk 5: `→` Ambiguity with Function Type (LOW risk)
**Severity**: Low

The scoped `→` notation is at precedence 30 (same as Lean's built-in `→`). When the scoped notation is active, Lean resolves ambiguity by **type inference**:
- If both operands are `Formula Atom` / `Proposition Atom`, it resolves to the formula connective
- If either operand is a type, it resolves to the function type

This works reliably in practice. The only edge case would be a polymorphic context where the type is unconstrained, but these files always have explicit type constraints.

**One concern**: In `∀` and `fun` binders, `(φ : Proposition Atom) → ...` always means the function type because the left side is a binder. No conflict.

### Risk 6: `abbrev` Transparency (SAFE)
**Severity**: None

Since `neg`, `and`, `or`, `diamond`, `iff`, `top`, `someFuture`, `allFuture`, `somePast`, `allPast` are all `abbrev`, they are definitionally equal to their expansions. Notation resolves to the same `abbrev` and then to the same constructor term. Using `¬φ` vs `.neg φ` produces identical elaborated terms. **No risk**.

### Risk 7: Structural Recursion Bodies (SAFE with nuance)
**Severity**: Low

Recursive functions like `swapTemporal`, `encodeNat`, `complexity`, `temporalDepth`, `atoms` use raw constructors in both pattern positions (necessary) and body positions (replaceable). In the body (right of `=>`), notation can be used:
```lean
-- Pattern: must stay raw       Body: can use notation
| .imp φ ψ => .imp (swapTemporal φ) (swapTemporal ψ)
-- Could become:
| .imp φ ψ => swapTemporal φ → swapTemporal ψ
```

However, for consistency within a pattern-match block, keeping raw constructors in the body MAY be preferred for visual alignment with the pattern. This is a style choice, not a correctness issue.

### Risk 8: `congrArg`/`congrArg₂` Arguments (CANNOT REPLACE)
**Severity**: N/A (universally applies)

`congrArg₂ Formula.imp (iha h3) (ihb h4)` requires the **function name** `Formula.imp`, not notation. These must stay as-is. Found ~9 occurrences in Temporal, more in other directories.

### Risk 9: `simp only [Formula.neg, ...]` Lemma Names (CANNOT REPLACE)
**Severity**: N/A

Tactic arguments like `simp only [Formula.neg, Formula.and, swapTemporal]` reference definition names, not notation. These stay unchanged. The EXPRESSIONS that appear in theorem statements adjacent to these proofs CAN use notation.

### Risk 10: Foundations/Logic Layer (OUT OF SCOPE)
**Severity**: N/A

The Foundations/Logic directory (~844 `HasImp.imp`/`HasBot.bot` occurrences) works at the **typeclass level** with abstract `F : Type*` — not concrete formula types. No scoped notation exists for these generic operations, and adding notation for `HasImp.imp` would be a separate design decision. These are **not candidates** for this refactoring.

---

## Safe vs Unsafe Patterns Summary

### SAFE to Replace
| Pattern | Example | Replacement |
|---------|---------|-------------|
| Expression-position `.imp` | `φ.imp ψ` | `φ → ψ` |
| Expression-position `.bot` | `.bot` | `⊥` |
| Expression-position `.neg` | `φ.neg` / `.neg φ` / `Formula.neg φ` | `¬φ` |
| Expression-position `.and` | `φ.and ψ` / `Formula.and φ ψ` | `φ ∧ ψ` |
| Expression-position `.or` | `φ.or ψ` / `Formula.or φ ψ` | `φ ∨ ψ` |
| Expression-position `.box` | `φ.box` / `.box φ` | `□φ` |
| Expression-position `.diamond` | `.diamond φ` | `◇φ` |
| Expression-position `.untl` | `Formula.untl φ ψ` | `φ U ψ` |
| Expression-position `.snce` | `Formula.snce φ ψ` | `φ S ψ` |
| Expression-position temporal ops | `Formula.someFuture φ` | `𝐅φ` (Temporal) / `Fφ` (Bimodal) |
| `show` targets | `show ... (.neg φ)` | `show ... (¬φ)` |
| Theorem type signatures | `PropositionalAxiom (φ.imp (ψ.imp φ))` | `PropositionalAxiom (φ → ψ → φ)` |
| Abbrev definition bodies | `def release := Formula.neg (...)` | `def release := ¬(...)` |

### UNSAFE / Must Not Replace
| Pattern | Reason |
|---------|--------|
| Pattern match arms: `\| .imp φ ψ =>` | Lean syntax requirement |
| `congrArg₂ Formula.imp` | Function name, not notation |
| `simp only [Formula.neg, ...]` | Lemma/def name in tactic argument |
| `unfold Proposition.diamond` | Definition name in tactic argument |
| `HasImp.imp` / `HasBot.bot` in Foundations | Typeclass level, no notation |
| Files with "Do not open" comments | Notation not in scope |
| `instance : TemporalConnectives where imp := .imp` | Typeclass field assignment |
| `abbrev` definition sites | Defining the notation target itself |

### Requires Individual Judgment
| Pattern | Notes |
|---------|-------|
| Recursive function bodies alongside pattern matches | Correctness-safe but style preference |
| `complexity` function body expressions | Within nested patterns, hard to read with notation |
| `.imp .bot .bot` for `⊤` | Could use `⊤` if `Top` instance is available |

---

## Confidence Level

**High** — The analysis is based on systematic grep surveys, Lean 4 scoped notation semantics, and verification of `abbrev` transparency. The identified risks are well-understood Lean behaviors. The main uncertainty is around the `→` precedence interaction, which I rate as low risk based on Lean's type-directed disambiguation.
