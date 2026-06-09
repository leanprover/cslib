# Research Report: Fix `untl`/`snce` Argument Order Convention

**Task**: 32 — Fix untl/snce argument order across cslib to match standard literature convention (Burgess 1982)

**Date**: 2026-06-08

---

## Executive Summary

The cslib codebase defines `Formula.untl arg1 arg2` with the **semantic binding**:
- `arg1` = GUARD (holds continuously in the interval between t and s)
- `arg2` = EVENT (holds at the witness time s)

The BimodalLogic source (referenced as the correct convention) uses the **opposite binding**:
- `arg1` = EVENT (holds at the witness time s)
- `arg2` = GUARD (holds continuously in the interval)

This mismatch causes at least 6 axiom abbreviations in `Cslib/Foundations/Logic/Axioms.lean` to be provably unsound (BX12, BX12', and likely several others), and several derived operator definitions to produce wrong formulas. The fix requires changing argument order in the `truth_at` semantics, all derived operators (`some_future`, `some_past`, `next`, `prev`, `release`, `trigger`, etc.), all temporal axiom abbreviations, and axiom constructors in the proof system.

---

## Section 1: Current State — Argument Order in Each File

### 1.1 The Core Constructor (No Change Needed)

**File**: `Cslib/Foundations/Logic/Connectives.lean` (lines 52, 57)

```lean
class HasUntil (F : Type*) where
  untl : F → F → F   -- arg1 → arg2

class HasSince (F : Type*) where
  snce : F → F → F   -- arg1 → arg2
```

The typeclass defines the binary interface. **No change needed here** — the constructor signature stays the same; only the semantic meaning of the two arguments changes.

---

### 1.2 Formula Inductive Types (No Structural Change, Docstrings Change)

**File**: `Cslib/Logics/Temporal/Syntax/Formula.lean` (line 43–45)

```lean
| untl (φ₁ φ₂ : Formula Atom)   -- Current: φ₁=GUARD, φ₂=EVENT
| snce (φ₁ φ₂ : Formula Atom)   -- Current: φ₁=GUARD, φ₂=EVENT
```

**File**: `Cslib/Logics/Bimodal/Syntax/Formula.lean` (lines 41–43)

```lean
| untl (φ₁ φ₂ : Formula Atom)   -- Current: φ₁=GUARD, φ₂=EVENT
| snce (φ₁ φ₂ : Formula Atom)   -- Current: φ₁=GUARD, φ₂=EVENT
```

The constructors themselves do not change; their docstrings and all **call sites** that pass arguments in a particular role change.

---

### 1.3 The Critical Semantics Definition

**File**: `Cslib/Logics/Bimodal/Semantics/Truth.lean` (lines 64–69)

**Current** (arg1=GUARD, arg2=EVENT):
```lean
| Formula.untl φ ψ =>
    ∃ s : D, t < s ∧ truth_at M Omega τ s ψ ∧          -- ψ=arg2=EVENT at witness s
      ∀ r : D, t < r → r < s → truth_at M Omega τ r φ  -- φ=arg1=GUARD in interval
| Formula.snce φ ψ =>
    ∃ s : D, s < t ∧ truth_at M Omega τ s ψ ∧          -- ψ=arg2=EVENT at witness s
      ∀ r : D, s < r → r < t → truth_at M Omega τ r φ  -- φ=arg1=GUARD in interval
```

**Required after fix** (arg1=EVENT, arg2=GUARD — BimodalLogic convention):
```lean
| Formula.untl φ ψ =>
    ∃ s : D, t < s ∧ truth_at M Omega τ s φ ∧          -- φ=arg1=EVENT at witness s
      ∀ r : D, t < r → r < s → truth_at M Omega τ r ψ  -- ψ=arg2=GUARD in interval
| Formula.snce φ ψ =>
    ∃ s : D, s < t ∧ truth_at M Omega τ s φ ∧          -- φ=arg1=EVENT at witness s
      ∀ r : D, s < r → r < t → truth_at M Omega τ r ψ  -- ψ=arg2=GUARD in interval
```

The comment in `truth_at` also needs updating:
```
-- Current (wrong after fix):
-- Until U(φ,ψ): ∃ s > t, φ(s) ∧ ∀ r ∈ (t,s), ψ(r)

-- Correct after fix:
-- Until U(φ,ψ): ∃ s > t, ψ(s) ∧ ∀ r ∈ (t,s), φ(r)
```

Wait — actually the comment at lines 51–52 uses the infix `U(φ,ψ)` notation. After the fix, `U(φ,ψ) = untl(φ,ψ)` has φ=arg1=EVENT, ψ=arg2=GUARD. So the docstring becomes:
```
-- Until U(φ,ψ): ∃ s > t, φ(s) ∧ ∀ r ∈ (t,s), ψ(r)  [φ=event, ψ=guard]
-- Since S(φ,ψ): ∃ s < t, φ(s) ∧ ∀ r ∈ (s,t), ψ(r)  [φ=event, ψ=guard]
```

This is a **swap of φ and ψ** in both the `truth_at` body and the inline comments.

**Severity**: CRITICAL — this is the root cause. Without fixing the semantics, changing the axiom abbreviations alone would not make the axioms sound.

---

### 1.4 Derived Operators in Formula Files — Temporal

**File**: `Cslib/Logics/Temporal/Syntax/Formula.lean`

| Operator | Current Definition | Current Semantics (arg1=G, arg2=E) | Required After Fix (arg1=E, arg2=G) |
|----------|-------------------|--------------------------------------|---------------------------------------|
| `some_future φ` (F φ) | `untl(⊤, φ)` | ⊤=GUARD, φ=EVENT → ∃s>t: φ(s) ✓ | Must become `untl(φ, ⊤)`: φ=EVENT, ⊤=GUARD → ∃s>t: φ(s) ✓ |
| `some_past φ` (P φ) | `snce(⊤, φ)` | ⊤=GUARD, φ=EVENT → ∃s<t: φ(s) ✓ | Must become `snce(φ, ⊤)`: φ=EVENT, ⊤=GUARD → ∃s<t: φ(s) ✓ |
| `next φ` (X φ) | `untl(⊥, φ)` | ⊥=GUARD, φ=EVENT → ∃s>t: φ(s) ∧ ∀r∈(t,s): ⊥ → φ holds at next moment | Must become `untl(φ, ⊥)` |
| `prev φ` (Y φ) | `snce(⊥, φ)` | ⊥=GUARD, φ=EVENT | Must become `snce(φ, ⊥)` |
| `release(φ, ψ)` R | `neg(untl(neg φ, neg ψ))` | neg φ=GUARD, neg ψ=EVENT | Must become `neg(untl(neg ψ, neg φ))` |
| `trigger(φ, ψ)` T | `neg(snce(neg φ, neg ψ))` | neg φ=GUARD, neg ψ=EVENT | Must become `neg(snce(neg ψ, neg φ))` |
| `weak_until(φ, ψ)` W | `or(untl(φ, ψ), all_future φ)` | φ=GUARD, ψ=EVENT | Stays `or(untl(φ, ψ), all_future φ)` — but untl args semantics flip |
| `strong_release(φ, ψ)` M | `untl(ψ, and(ψ, φ))` | ψ=GUARD, and(ψ,φ)=EVENT | Must become `untl(and(ψ,φ), ψ)` |
| `strong_trigger(φ, ψ)` ST | `snce(ψ, and(ψ, φ))` | ψ=GUARD, and(ψ,φ)=EVENT | Must become `snce(and(ψ,φ), ψ)` |

**Line references for Temporal/Syntax/Formula.lean**:
- `some_future`: line 63–64 → change `untl .top φ` to `untl φ .top`
- `some_past`: line 71–72 → change `snce .top φ` to `snce φ .top`
- `next`: line 366 → change `untl .bot φ` to `untl φ .bot`
- `prev`: line 370 → change `snce .bot φ` to `snce φ .bot`
- `release`: line 391–392 → swap neg args
- `trigger`: line 395–396 → swap neg args
- `weak_until`: line 399–400 → no change to `untl φ ψ` call itself (args already in place; semantics changes)
- `weak_since`: line 403–404 → same
- `strong_release`: line 407–408 → swap args
- `strong_trigger`: line 411–412 → swap args

**Complexity function** (lines 311–334): Several pattern-match arms recognize derived operators by their structure. After the fix, these patterns need to be updated:

```lean
-- Current G(φ) recognition pattern (line 312):
| .imp (.untl (.imp .bot .bot) (.imp φ .bot)) .bot  -- untl(⊤, ¬φ) = all_future structure

-- After fix (some_future ¬φ = untl(¬φ, ⊤)):
| .imp (.untl (.imp φ .bot) (.imp .bot .bot)) .bot  -- untl(¬φ, ⊤) = new all_future structure
```

Similarly:
- H(φ) pattern: lines 313–314
- R(φ,ψ) pattern: lines 315–317
- T(φ,ψ) pattern: lines 318–320
- next(φ): line 323–324 → `untl .bot φ` becomes `untl φ .bot`
- F(φ): lines 325–326 → `untl (imp .bot .bot) φ` becomes `untl φ (imp .bot .bot)`
- P(φ): lines 330–332 → similarly

---

### 1.5 Derived Operators in Formula Files — Bimodal

**File**: `Cslib/Logics/Bimodal/Syntax/Formula.lean`

Same changes as temporal for `some_future`, `some_past`. Lines 65–66 and 73–74.

---

### 1.6 Axiom Abbreviations — `Cslib/Foundations/Logic/Axioms.lean`

This is where the unsoundness lives. The axioms are defined in terms of `HasUntil.untl` calls. After switching semantics to arg1=EVENT, arg2=GUARD, each axiom must be re-checked.

#### Analysis of Each Temporal Axiom

The following uses notation: `U(a,b) = untl(a,b)`. After the fix, semantics: `U(a,b)` at t = ∃s>t: a(s) ∧ ∀r∈(t,s): b(r).

**BX1 `SerialFuture`** (line 111–113):
- Current: `⊤ → untl(⊤, ⊤)` = ⊤ → ∃s>t: ⊤(s) ∧ ∀r: ⊤(r) ✓ (trivially true — fine either way)
- After fix (if we keep `F⊤ = untl(⊤,⊤)`): still trivially valid
- **Change needed**: `F(⊤) = untl(⊤, ⊤)` stays the same but `some_future` definition changes, so if the axiom uses `some_future` notation it auto-updates; the raw abbreviation needs checking.

Looking at line 113: `HasImp.imp top (HasUntil.untl top top)` — both args are ⊤, so it's symmetric; no change needed here.

**BX1' `SerialPast`** (line 117–119): Similarly symmetric. **No change needed**.

**BX2G `LeftMonoUntilG`** (lines 124–129):
- Current code: `G(φ→χ) → (untl(ψ,φ) → untl(ψ,χ))`
- G(φ→χ) = `¬(untl(⊤, ¬(φ→χ)))` with current semantics: ∀s>t: (φ→χ)(s)
- `untl(ψ,φ)`: ψ=GUARD, φ=EVENT → event goes from φ to χ
- **Docstring says**: "Guard monotonicity" — changing the EVENT (second arg) is actually EVENT monotonicity!
- The docstring `G(φ→χ) → (ψ U φ → ψ U χ)` with current convention (arg1=G, arg2=E): ψ U φ has ψ=GUARD, φ=EVENT, χ=EVENT → this is EVENT monotonicity, NOT guard monotonicity. **The naming/labeling is inverted.**
- After fix (arg1=E, arg2=G): `untl(ψ,φ)` has ψ=EVENT, φ=GUARD. Changing the first arg (EVENT) from ψ to... wait, the formula changes the second arg (φ→χ in position arg2). So after fix, `untl(ψ,φ)→untl(ψ,χ)` changes the GUARD from φ to χ. This IS "guard monotonicity" ✓

**Verdict**: The code at lines 127–129 (`untl(ψ,φ)→untl(ψ,χ)`) keeps the same structure, but the SEMANTICS changes meaning because G(φ→χ) also changes meaning. Need to verify soundness after the flip.

With new semantics: `untl(ψ,φ) = ∃s>t: ψ(s) ∧ ∀r∈(t,s): φ(r)`. G(φ→χ) = ∀s>t: (φ→χ)(s). So G(φ→χ) means ∀s>t: (φ(s)→χ(s)), i.e., φ→χ pointwise. If ∃s>t: ψ(s) ∧ ∀r∈(t,s): φ(r), then by G(φ→χ) applied to each r, ∀r∈(t,s): χ(r). So ∃s>t: ψ(s) ∧ ∀r∈(t,s): χ(r) = `untl(ψ,χ)` ✓ **VALID** with new convention.

But G(φ→χ) in the new convention encodes as `¬(untl(¬(φ→χ), ⊤))` with new `some_future(f) = untl(f,⊤)`. That is: G_new(φ→χ) = `¬F_new(¬(φ→χ)) = ¬untl(¬(φ→χ), ⊤)`. The current code uses `HasUntil.untl top (neg (HasImp.imp φ χ))` = `untl(⊤, ¬(φ→χ))`. This is the OLD `F(¬(φ→χ))` = OLD G's negation body. After fixing `some_future` to use `untl(f, ⊤)`, the new G body = `untl(¬(φ→χ), ⊤)`. So the `G_imp` local def in `LeftMonoUntilG` needs to swap to `HasUntil.untl (neg (HasImp.imp φ χ)) top`. **CHANGE NEEDED** in line 127.

**BX2G overall**: change `G_imp` local expression, keep `untl(ψ,φ) → untl(ψ,χ)` structure.

**BX2H `LeftMonoSinceH`** (lines 134–139): Symmetric. Similarly change `H_imp` local expression.

**BX3 `RightMonoUntil`** (lines 144–149):
- Current: `G(φ→ψ) → (untl(φ,χ) → untl(ψ,χ))` where arg1=GUARD changes
- After fix: arg1 becomes EVENT. So `untl(φ,χ)→untl(ψ,χ)` changes the EVENT from φ to ψ, while χ stays as GUARD.
- G(φ→ψ) means at all future times φ→ψ pointwise.
- New semantics: `untl(φ,χ) = ∃s>t: φ(s) ∧ ∀r∈(t,s): χ(r)`. If G(φ→ψ) ∧ untl(φ,χ): ∃s>t: φ(s) ∧ ∀r: χ(r). Then ψ(s) holds (by G at s), so `untl(ψ,χ)` = ∃s>t: ψ(s) ∧ ∀r: χ(r) ✓ **VALID**.
- But G(φ→ψ) local expression needs changing (same as BX2G).
- **CHANGE NEEDED**: swap G_imp construction at line 147.

**BX3' `RightMonoSince`** (lines 154–159): Symmetric change needed.

**BX4 `ConnectFuture`** (lines 163–168): `φ → G(P(φ))`
- P(φ) = `snce(⊤, φ)` currently. After fix: P(φ) = `snce(φ, ⊤)`.
- G(...) involves `untl(⊤, ...)` currently. After fix: `untl(..., ⊤)`.
- Line 166: `P_φ := snce top φ` → must become `snce φ top`
- Line 167: `G_P_φ := imp (untl top (neg P_φ)) bot` → must become `imp (untl (neg P_φ) top) bot`
- **CHANGE NEEDED** at lines 166–167.

**BX4' `ConnectPast`** (lines 172–177): Similar.
- Line 175: `F_φ := untl top φ` → must become `untl φ top`
- Line 176: `H_F_φ := imp (snce top (neg F_φ)) bot` → must become `imp (snce (neg F_φ) top) bot`

**BX13 `EnrichmentUntil`** (lines 182–186):
- Current: `p ∧ (ψ U φ) → (ψ ∧ S(p, φ)) U φ`
- `untl(ψ, φ)`: current arg1=GUARD=ψ, arg2=EVENT=φ
- `snce(p, φ)`: current arg1=GUARD=p, arg2=EVENT=φ
- After fix: `untl(ψ,φ)` has ψ=EVENT, φ=GUARD; `snce(p,φ)` has p=EVENT, φ=GUARD
- The intended Burgess BX13 enrichment axiom: `p ∧ (ψ U φ) → (ψ ∧ S(p,φ)) U φ` where in standard notation ψ U φ = ψ holds until φ.
- After the convention change, `untl(ψ,φ)` = "ψ eventually holds (EVENT=ψ), with φ as guard" — this reads as "ψ occurs with φ guarding" which would be written `ψ U φ` in standard notation where ψ=event is second arg... but we flipped it. This axiom formula needs careful re-examination against the literature.

**For the purpose of this research**: the code-level change is clear — swap argument positions in untl/snce calls to reflect the new convention. The detailed semantic verification of each BX axiom against Burgess 1982 is implementation-level work.

**BX13' `EnrichmentSince`** (lines 190–194): Symmetric.

**BX5 `SelfAccumUntil`** (lines 198–202): `U(ψ,φ) → U(ψ, φ ∧ U(ψ,φ))`
- All three `untl(ψ,φ)` calls need argument positions checked.

**BX5' `SelfAccumSince`** (lines 206–210): Symmetric.

**BX6 `AbsorbUntil`** (lines 214–218): `U(φ ∧ U(ψ,φ), φ) → U(ψ,φ)`
- Nested untl calls.

**BX6' `AbsorbSince`** (lines 222–226): Symmetric.

**BX7 `LinearUntil`** (lines 230–237): Complex with many untl calls.

**BX7' `LinearSince`** (lines 241–248): Symmetric.

**BX10 `UntilF`** (lines 253–255): `U(ψ,φ) → F(ψ)`
- Current: `untl(ψ,φ) → untl(⊤,ψ)` where ψ=GUARD in untl(ψ,φ) and ψ=EVENT in F(ψ)=untl(⊤,ψ)
- After fix: `untl(ψ,φ)` has ψ=EVENT. F(ψ) = `untl(ψ,⊤)` has ψ=EVENT. So `untl(ψ,φ) → untl(ψ,⊤)`.
- Current code: `HasImp.imp (HasUntil.untl ψ φ) (HasUntil.untl top ψ)`
- After fix: `HasImp.imp (HasUntil.untl ψ φ) (HasUntil.untl ψ top)` — change second untl from `(⊤,ψ)` to `(ψ,⊤)`
- **Soundness check**: `untl(ψ,φ)` = ∃s>t: ψ(s) ∧ ∀r∈(t,s): φ(r). So ψ holds at some future s. F(ψ) = `untl(ψ,⊤)` = ∃s>t: ψ(s) ∧ ∀r∈(t,s): ⊤ = ∃s>t: ψ(s) ✓ **VALID**.

**BX10' `SinceP`** (lines 260–262): Symmetric.

**BX11 `TempLinearity`** (lines 266–275): Uses `F'(x) = untl top x`. After fix: `F'(x) = untl x top`.

**BX11' `TempLinearityPast`** (lines 279–288): Uses `P'(x) = snce top x`. After fix: `P'(x) = snce x top`.

**BX12 `FUntilEquiv`** (lines 293–295): `F(φ) → U(φ, ⊤)`
- Current: `untl(⊤, φ) → untl(φ, ⊤)`
- With current semantics: F(φ)=∃s>t:φ(s), and `untl(φ,⊤)` = ∃s>t: (∀r∈(t,s): φ(r)) — says φ holds continuously for a while. This is **NOT** implied by Fφ. **UNSOUND** in current form.
- After fix: `F(φ) = untl(φ,⊤)` = ∃s>t: φ(s). `U(φ,⊤) = untl(φ,⊤)` = same. So BX12 becomes F(φ)→F(φ) — a tautology. But in the code, the expression changes from `untl(⊤,φ)→untl(φ,⊤)` to `untl(φ,⊤)→untl(φ,⊤)`.
- **Change**: line 295: `HasImp.imp (HasUntil.untl top φ) (HasUntil.untl φ top)` → `HasImp.imp (HasUntil.untl φ top) (HasUntil.untl φ top)` — trivially sound.

**Note**: If BX12 becomes trivially `F(φ)→F(φ)`, it may no longer be an interesting axiom. This should be verified against Burgess to determine if the intended statement is different.

**BX12' `PSinceEquiv`** (lines 299–301): Symmetric. Same analysis.

---

### 1.7 Axiom Constructors — `Cslib/Logics/Temporal/ProofSystem/Axioms.lean`

The proof system axioms use `Formula.untl` and `Formula.snce` directly. Each constructor needs the same changes as the abbreviations above, because they reference the same derived operators (`some_future`, `some_past`, `all_future`, `all_past`, `and`, etc.).

**Lines needing changes**:

| Constructor | Line | Current Form | Issue |
|-------------|------|-------------|-------|
| `serial_future` | 89 | `top.imp (some_future top)` | `some_future` definition changes |
| `serial_past` | 93 | `top.imp (some_past top)` | `some_past` definition changes |
| `left_mono_until_G` | 97–98 | `untl ψ φ`, `untl ψ χ` | Arg semantics change |
| `left_mono_since_H` | 102–103 | `snce ψ φ`, `snce ψ χ` | Arg semantics change |
| `right_mono_until` | 107–108 | `untl φ χ`, `untl ψ χ` | Arg semantics change |
| `right_mono_since` | 112–113 | `snce φ χ`, `snce ψ χ` | Arg semantics change |
| `connect_future` | 116–117 | `some_past`, `all_future` | Derived ops change |
| `connect_past` | 120–121 | `some_future`, `all_past` | Derived ops change |
| `enrichment_until` | 125–127 | `untl ψ φ`, `snce p φ`, `untl ... φ` | Multiple untl/snce |
| `enrichment_since` | 131–133 | `snce ψ φ`, `untl p φ`, `snce ... φ` | Multiple |
| `self_accum_until` | 137–139 | `untl ψ φ`, nested | Arg positions |
| `self_accum_since` | 143–145 | `snce ψ φ`, nested | Arg positions |
| `absorb_until` | 149–150 | `untl (and φ (untl ψ φ)) φ`, `untl ψ φ` | Multiple |
| `absorb_since` | 154–155 | `snce (and φ (snce ψ φ)) φ`, `snce ψ φ` | Multiple |
| `linear_until` | 159–165 | Multiple `untl` calls | All need checking |
| `linear_since` | 169–175 | Multiple `snce` calls | All need checking |
| `until_F` | 178–179 | `untl ψ φ`, `some_future ψ` | `some_future` changes |
| `since_P` | 182–183 | `snce ψ φ`, `some_past ψ` | `some_past` changes |
| `temp_linearity` | 187–191 | `some_future` calls | All via derived op |
| `temp_linearity_past` | 195–199 | `some_past` calls | All via derived op |
| `F_until_equiv` | 202–203 | `some_future φ`, `untl φ top` | Both change |
| `P_since_equiv` | 206–207 | `some_past φ`, `snce φ top` | Both change |

---

### 1.8 Proof System Typeclass — `Cslib/Foundations/Logic/ProofSystem.lean`

**TemporalNecessitation** (lines 75–92): The internal expressions for G(φ) and H(φ) use untl/snce:

```lean
-- Current G(φ) encoding (line 82–84):
HasImp.imp
  (HasUntil.untl (HasImp.imp (HasBot.bot : F) HasBot.bot)  -- ⊤ = arg1 (currently GUARD)
    (HasImp.imp φ HasBot.bot))                               -- ¬φ = arg2 (currently EVENT)
  HasBot.bot

-- After fix (arg1=EVENT, arg2=GUARD):
HasImp.imp
  (HasUntil.untl (HasImp.imp φ HasBot.bot)                   -- ¬φ = arg1 = EVENT
    (HasImp.imp (HasBot.bot : F) HasBot.bot))                 -- ⊤ = arg2 = GUARD
  HasBot.bot
```

This means `F(¬φ) = untl(¬φ, ⊤)` after fix. G(φ) = ¬F(¬φ) = ¬untl(¬φ, ⊤) ✓

**Lines 82–84 and 90–92**: Both the `tempNec` and `tempNecPast` expressions need swapping.

---

### 1.9 Derived Theorems — `Cslib/Logics/Temporal/Theorems/TemporalDerived.lean`

This file already acknowledges the convention discrepancy in its comment (lines 15–17):
```
In cslib, `untl φ₁ φ₂` = `φ₁ U φ₂` with `φ₁` as GUARD and `φ₂` as EVENT.
This differs from BimodalLogic where `untl(event, guard)`.
```

After the fix, this comment becomes moot and should be deleted/updated.

**Internal abbreviations** (lines 39–42):
```lean
private abbrev someFuture (φ : F) : F := HasUntil.untl top' φ  -- Must become: untl φ top'
private abbrev somePast (φ : F) : F := HasSince.snce top' φ     -- Must become: snce φ top'
```

All uses of `HasAxiomLeftMonoUntilG.leftMonoUntilG` and `HasAxiomLeftMonoSinceH.leftMonoSinceH` in this file reference the axiom by its name, not by raw `untl` calls, so they don't need structural changes — BUT the axiom abbreviations they reference will change, so the proofs need re-verification.

The `F_mono` and `P_mono` theorems (lines 95–107) pass explicit arguments to the axiom typeclasses:
```lean
-- F_mono line 99:
HasAxiomLeftMonoUntilG.leftMonoUntilG (S := S) (φ := φ) (χ := ψ) (ψ := top')
-- After fix: the ψ := top' argument still works — top' remains the outer untl's guard
```

The theorems themselves may still compile but their proofs need verification after the convention change.

---

### 1.10 Embedding — `Cslib/Logics/Bimodal/Embedding/TemporalEmbedding.lean`

This file simply maps constructors to constructors (lines 32–33, 57–65):
```lean
| .untl φ₁ φ₂ => .untl (φ₁.toBimodal) (φ₂.toBimodal)
| .snce φ₁ φ₂ => .snce (φ₁.toBimodal) (φ₂.toBimodal)
```

Since both Temporal and Bimodal will switch conventions simultaneously, this preserves-by-position embedding remains correct. **No change needed** in the embedding itself.

---

### 1.11 Subformulas — `Cslib/Logics/Temporal/Syntax/Subformulas.lean`

The subformula definitions simply recurse on both children without distinguishing roles:
```lean
| φ@(.untl ψ χ) => φ :: (subformulas ψ ++ subformulas χ)
| φ@(.snce ψ χ) => φ :: (subformulas ψ ++ subformulas χ)
```

**No change needed** here — subformula closure is symmetric.

The docstring lemmas at lines 168–214 name things "left" and "right" which are structural, not semantic. **Docstrings should be updated** to use "event" and "guard" labels but the Lean code is structurally unchanged.

---

## Section 2: Summary of the Correct Convention

**Burgess 1982 / BimodalLogic convention** (target):
```
Formula.untl event guard
Formula.snce event guard
```

Semantics: `truth_at(untl event guard)` at t = `∃ s > t, event(s) ∧ ∀ r ∈ (t,s), guard(r)`

Infix `φ U ψ = Formula.untl φ ψ` → **φ is the EVENT** (holds at witness), **ψ is the GUARD** (holds in between).

Note on standard notation: In standard temporal logic literature, `φ U ψ` is typically read as "φ holds UNTIL ψ holds" where φ=guard and ψ=event. The BimodalLogic convention reverses this for the constructor but likely preserves the math by adjusting `some_future`:
- Standard: `F(ψ) = ⊤ U ψ` with ψ=event in second position → `some_future ψ = untl ⊤ ψ` (current cslib)
- BimodalLogic: `F(ψ) = ψ U ⊤` with ψ=event in first position → `some_future ψ = untl ψ ⊤` (target)

**The math is equivalent; only the constructor's argument position convention differs.**

---

## Section 3: Complete File-by-File Change List

### Priority 1 — Semantics Root Fix

| File | Lines | Change |
|------|-------|--------|
| `Cslib/Logics/Bimodal/Semantics/Truth.lean` | 51–52 | Update docstring comment |
| `Cslib/Logics/Bimodal/Semantics/Truth.lean` | 64–66 | Swap φ and ψ in `untl` branch: `truth_at τ s φ` → `truth_at τ s ψ`... wait, FLIP: currently ψ=arg2=EVENT; after fix arg1=EVENT. So swap to make φ=arg1 be the event. Change `truth_at τ s ψ` to `truth_at τ s φ` and `truth_at τ r φ` to `truth_at τ r ψ`. |
| `Cslib/Logics/Bimodal/Semantics/Truth.lean` | 67–69 | Same swap in `snce` branch. |

### Priority 2 — Derived Operator Definitions (both formula files)

| File | Lines | Change |
|------|-------|--------|
| `Cslib/Logics/Temporal/Syntax/Formula.lean` | 63–64 | `untl .top φ` → `untl φ .top` |
| `Cslib/Logics/Temporal/Syntax/Formula.lean` | 71–72 | `snce .top φ` → `snce φ .top` |
| `Cslib/Logics/Temporal/Syntax/Formula.lean` | 366 | `untl .bot φ` → `untl φ .bot` |
| `Cslib/Logics/Temporal/Syntax/Formula.lean` | 370 | `snce .bot φ` → `snce φ .bot` |
| `Cslib/Logics/Temporal/Syntax/Formula.lean` | 391–392 | `neg(untl(neg φ, neg ψ))` → `neg(untl(neg ψ, neg φ))` |
| `Cslib/Logics/Temporal/Syntax/Formula.lean` | 395–396 | `neg(snce(neg φ, neg ψ))` → `neg(snce(neg ψ, neg φ))` |
| `Cslib/Logics/Temporal/Syntax/Formula.lean` | 407–408 | `untl ψ (and ψ φ)` → `untl (and ψ φ) ψ` |
| `Cslib/Logics/Temporal/Syntax/Formula.lean` | 411–412 | `snce ψ (and ψ φ)` → `snce (and ψ φ) ψ` |
| `Cslib/Logics/Temporal/Syntax/Formula.lean` | 311–334 | Update all complexity pattern matching arms |
| `Cslib/Logics/Bimodal/Syntax/Formula.lean` | 65–66 | `untl .top φ` → `untl φ .top` |
| `Cslib/Logics/Bimodal/Syntax/Formula.lean` | 73–74 | `snce .top φ` → `snce φ .top` |

### Priority 3 — Axiom Abbreviations

| File | Lines | Change Description |
|------|-------|-------------------|
| `Cslib/Foundations/Logic/Axioms.lean` | 127 | `G_imp`: swap `untl top (neg ...)` → `untl (neg ...) top` |
| `Cslib/Foundations/Logic/Axioms.lean` | 129 | `untl ψ φ`, `untl ψ χ` — check after semantics change |
| `Cslib/Foundations/Logic/Axioms.lean` | 137 | `H_imp`: swap similarly |
| `Cslib/Foundations/Logic/Axioms.lean` | 139 | `snce ψ φ`, `snce ψ χ` — check |
| `Cslib/Foundations/Logic/Axioms.lean` | 147 | `G_imp` swap |
| `Cslib/Foundations/Logic/Axioms.lean` | 149 | `untl φ χ`, `untl ψ χ` — check |
| `Cslib/Foundations/Logic/Axioms.lean` | 157 | `H_imp` swap |
| `Cslib/Foundations/Logic/Axioms.lean` | 159 | `snce φ χ`, `snce ψ χ` — check |
| `Cslib/Foundations/Logic/Axioms.lean` | 166–167 | P_φ and G_P_φ: `snce top φ` → `snce φ top`; `untl top (neg P_φ)` → `untl (neg P_φ) top` |
| `Cslib/Foundations/Logic/Axioms.lean` | 175–176 | F_φ and H_F_φ: `untl top φ` → `untl φ top`; `snce top (neg F_φ)` → `snce (neg F_φ) top` |
| `Cslib/Foundations/Logic/Axioms.lean` | 185–186 | EnrichmentUntil: `untl ψ φ`, `snce p φ` — check all |
| `Cslib/Foundations/Logic/Axioms.lean` | 193–194 | EnrichmentSince: `snce ψ φ`, `untl p φ` — check all |
| `Cslib/Foundations/Logic/Axioms.lean` | 201–202 | SelfAccumUntil: all `untl ψ φ` calls |
| `Cslib/Foundations/Logic/Axioms.lean` | 209–210 | SelfAccumSince: all `snce ψ φ` calls |
| `Cslib/Foundations/Logic/Axioms.lean` | 217–218 | AbsorbUntil: nested `untl` |
| `Cslib/Foundations/Logic/Axioms.lean` | 225–226 | AbsorbSince: nested `snce` |
| `Cslib/Foundations/Logic/Axioms.lean` | 234–237 | LinearUntil: multiple `untl` |
| `Cslib/Foundations/Logic/Axioms.lean` | 245–248 | LinearSince: multiple `snce` |
| `Cslib/Foundations/Logic/Axioms.lean` | 255 | UntilF: `untl top ψ` → `untl ψ top` |
| `Cslib/Foundations/Logic/Axioms.lean` | 262 | SinceP: `snce top ψ` → `snce ψ top` |
| `Cslib/Foundations/Logic/Axioms.lean` | 271 | TempLinearity `F'`: `untl top x` → `untl x top` |
| `Cslib/Foundations/Logic/Axioms.lean` | 284 | TempLinearityPast `P'`: `snce top x` → `snce x top` |
| `Cslib/Foundations/Logic/Axioms.lean` | 295 | FUntilEquiv: `untl top φ` → `untl φ top` (first conjunct becomes same as F(φ)) |
| `Cslib/Foundations/Logic/Axioms.lean` | 301 | PSinceEquiv: `snce top φ` → `snce φ top` |
| `Cslib/Foundations/Logic/Axioms.lean` | 316 | ModalFuture G_φ: `untl top neg_φ` → `untl neg_φ top` |

### Priority 4 — Proof System Typeclass

| File | Lines | Change |
|------|-------|--------|
| `Cslib/Foundations/Logic/ProofSystem.lean` | 82–84 | `tempNec`: swap `untl(⊤, ¬φ)` → `untl(¬φ, ⊤)` |
| `Cslib/Foundations/Logic/ProofSystem.lean` | 90–92 | `tempNecPast`: swap `snce(⊤, ¬φ)` → `snce(¬φ, ⊤)` |

### Priority 5 — Proof System Axiom Constructors

| File | Lines | Change |
|------|-------|--------|
| `Cslib/Logics/Temporal/ProofSystem/Axioms.lean` | 97–98 | `left_mono_until_G`: uses `Formula.untl ψ φ` — check after derived ops update |
| `Cslib/Logics/Temporal/ProofSystem/Axioms.lean` | 102–103 | `left_mono_since_H` |
| `Cslib/Logics/Temporal/ProofSystem/Axioms.lean` | 107–108 | `right_mono_until` |
| `Cslib/Logics/Temporal/ProofSystem/Axioms.lean` | 112–113 | `right_mono_since` |
| `Cslib/Logics/Temporal/ProofSystem/Axioms.lean` | 116–117 | `connect_future`: uses `some_past.all_future` (via derived ops) |
| `Cslib/Logics/Temporal/ProofSystem/Axioms.lean` | 120–121 | `connect_past` |
| `Cslib/Logics/Temporal/ProofSystem/Axioms.lean` | 125–127 | `enrichment_until` |
| `Cslib/Logics/Temporal/ProofSystem/Axioms.lean` | 131–133 | `enrichment_since` |
| `Cslib/Logics/Temporal/ProofSystem/Axioms.lean` | 137–139 | `self_accum_until` |
| `Cslib/Logics/Temporal/ProofSystem/Axioms.lean` | 143–145 | `self_accum_since` |
| `Cslib/Logics/Temporal/ProofSystem/Axioms.lean` | 149–150 | `absorb_until` |
| `Cslib/Logics/Temporal/ProofSystem/Axioms.lean` | 154–155 | `absorb_since` |
| `Cslib/Logics/Temporal/ProofSystem/Axioms.lean` | 159–165 | `linear_until` |
| `Cslib/Logics/Temporal/ProofSystem/Axioms.lean` | 169–175 | `linear_since` |
| `Cslib/Logics/Temporal/ProofSystem/Axioms.lean` | 178–179 | `until_F` |
| `Cslib/Logics/Temporal/ProofSystem/Axioms.lean` | 182–183 | `since_P` |
| `Cslib/Logics/Temporal/ProofSystem/Axioms.lean` | 202–203 | `F_until_equiv` |
| `Cslib/Logics/Temporal/ProofSystem/Axioms.lean` | 206–207 | `P_since_equiv` |

### Priority 6 — Derived Theorems (re-verification)

| File | Lines | Change |
|------|-------|--------|
| `Cslib/Logics/Temporal/Theorems/TemporalDerived.lean` | 15–17 | Delete/update convention note |
| `Cslib/Logics/Temporal/Theorems/TemporalDerived.lean` | 39 | `someFuture`: `untl top' φ` → `untl φ top'` |
| `Cslib/Logics/Temporal/Theorems/TemporalDerived.lean` | 41 | `somePast`: `snce top' φ` → `snce φ top'` |
| `Cslib/Logics/Temporal/Theorems/TemporalDerived.lean` | 88–90 | Update `F_mono` comment (was "guard position") |
| `Cslib/Logics/Temporal/Theorems/TemporalDerived.lean` | 99 | `leftMonoUntilG` with `ψ := top'` may still work but verify |
| `Cslib/Logics/Temporal/Theorems/TemporalDerived.lean` | 141–150 | G_distribution — verify BX2G argument passing |

### No Change Needed

| File | Reason |
|------|--------|
| `Cslib/Foundations/Logic/Connectives.lean` | Typeclass interface only |
| `Cslib/Logics/Temporal/Syntax/Subformulas.lean` | Structurally symmetric (no semantic role distinction) |
| `Cslib/Logics/Bimodal/Embedding/TemporalEmbedding.lean` | Position-preserving structural map; both sides change simultaneously |
| `Cslib/Logics/Temporal/Syntax/Formula.lean` (constructor decls, BEq, Encodable) | Structural recursion only |

---

## Section 4: Risk Areas and Dependencies

### Risk 1 — Complexity Function Pattern Matching (HIGH)

The `complexity` function in `Cslib/Logics/Temporal/Syntax/Formula.lean` (lines 308–334) pattern-matches on the deep structure of derived operators (G, H, R, T, etc.) to assign lower complexity. These patterns embed the old argument order:

```lean
| .imp (.untl (.imp .bot .bot) (.imp φ .bot)) .bot  -- old G(φ) = ¬F(¬φ) = ¬untl(⊤, ¬φ)
```

After the convention change, `G(φ) = ¬untl(¬φ, ⊤)` so the pattern must become:
```lean
| .imp (.untl (.imp φ .bot) (.imp .bot .bot)) .bot  -- new G(φ) = ¬untl(¬φ, ⊤)
```

Failure to update these patterns means the complexity function will fall through to the generic `untl` case for G, H, R, T — giving incorrect (too high) complexity values. This may not break proofs but will break decidability/finiteness arguments.

### Risk 2 — Proof Validity in TemporalDerived (MEDIUM)

The proofs in `TemporalDerived.lean` were written under the old convention. After the fix, the axiom abbreviations change meaning. The proofs using `leftMonoUntilG` with specific argument instantiations (like `ψ := top'`) may become incorrect because the axiom now says something different.

**Specifically**: `F_mono` (line 95–99) claims `G(φ→ψ) → (Fφ → Fψ)` and uses BX2G with `ψ := top'`. After the fix, F(φ) = `untl(φ, ⊤)` and BX2G becomes `G(φ→χ) → (untl(ψ,φ) → untl(ψ,χ))`. With ψ=⊤: BX2G = `G(φ→χ) → (untl(⊤,φ) → untl(⊤,χ))`. But new `F(φ) = untl(φ,⊤)` NOT `untl(⊤,φ)`. So `F_mono` proof would need to use the RIGHT axiom.

This is a significant re-derivation: the existing TemporalDerived proofs are likely mostly invalid after the convention change and need to be re-examined.

### Risk 3 — BX12/BX12' Becoming Trivial (LOW severity for soundness, HIGH for intent)

After the fix, BX12 (`F(φ) → U(φ,⊤)`) becomes `untl(φ,⊤) → untl(φ,⊤)` — trivially true. The Burgess 1982 BX12 likely has meaningful content. The implementer should check Burgess to ensure the axiom is being correctly encoded, not just trivially satisfied.

### Risk 4 — Internal Consistency of BX5, BX6, BX7 (HIGH)

These axioms have nested `untl`/`snce` calls where both the event and guard positions appear. After the convention change, all nested calls need consistent treatment. The enrichment axioms (BX13, BX13') are particularly complex.

### Risk 5 — Theorem Proofs Reference Abbreviations That Change (MEDIUM)

The `Cslib/Logics/Temporal/ProofSystem/Axioms.lean` constructors reference `Formula.untl` with specific arguments. If they use derived abbreviations (`some_future`, `all_future`, etc.) they will auto-update when those abbreviations change. But any direct `untl`/`snce` calls need manual inspection.

---

## Section 5: Implementation Order Recommendation

1. **First**: Fix `Truth.lean` semantics (swap φ/ψ in untl/snce branches)
2. **Second**: Fix derived operators in both `Formula.lean` files (`some_future`, `some_past`, `next`, `prev`, `release`, `trigger`, `strong_release`, `strong_trigger`) and complexity patterns
3. **Third**: Fix axiom abbreviations in `Axioms.lean` (all temporal section)
4. **Fourth**: Fix `ProofSystem.lean` temporal necessitation expressions
5. **Fifth**: Fix axiom constructors in `ProofSystem/Axioms.lean`
6. **Sixth**: Run `lake build` and fix any resulting type errors
7. **Seventh**: Re-verify proofs in `TemporalDerived.lean`

The changes in steps 2–5 cascade: derived operator changes propagate to axiom abbreviations which propagate to axiom constructors. The Lean compiler will catch type errors but NOT semantic errors (a formula with swapped args still type-checks).

---

## Appendix: Files Confirmed to NOT Reference untl/snce

Searched all Lean files in the project. The following directories/patterns were checked and contain no `untl`/`snce` references:
- `Cslib/Logics/Modal/` (modal logic only)
- `Cslib/Foundations/Logic/InferenceSystem.lean`
- `Cslib/Foundations/Logic/Theorems/` (propositional theorems)
- Any test or example files
