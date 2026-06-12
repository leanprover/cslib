/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Init
public import Cslib.Foundations.Logic.Connectives
public import Mathlib.Logic.Encodable.Basic
public import Mathlib.Logic.Denumerable
public import Mathlib.Data.Finset.Basic

/-! # Temporal Logic Formula

This module defines the formula type for temporal logic with primitives
`{atom, bot, imp, untl, snce}`. The `untl` (until) and `snce` (since) operators
are the basic temporal modalities from which all other temporal operators
(globally, eventually, etc.) are derived.

## Derived Temporal Operators

The derived operators use the Burgess convention: in `untl event guard` and `snce event guard`,
the first argument is the **event** (holds at the witness point) and the second is the **guard**
(holds at all intermediate points). This matches the abstract typeclass expansion in `Axioms.lean`.

- `someFuture φ` (F φ): `φ U ⊤` — φ holds at some future point (Burgess: `untl φ ⊤`)
- `allFuture φ` (G φ): `¬F ¬φ` — φ holds at all future points
- `somePast φ` (P φ): `φ S ⊤` — φ held at some past point (Burgess: `snce φ ⊤`)
- `allPast φ` (H φ): `¬P ¬φ` — φ held at all past points

## References

* [H. Kamp, *Tense Logic and the Theory of Linear Order*][Kamp1968]
* [D. Gabbay et al., *On the Temporal Analysis of Fairness*][GabbayPnueliShelahStavi1980]
-/

@[expose] public section

namespace Cslib.Logic.Temporal

/-- Temporal logic formula type. Primitives: atoms, falsum, implication, until, and since. -/
inductive Formula (Atom : Type u) : Type u where
  /-- Atomic proposition. -/
  | atom (p : Atom)
  /-- Falsum / bottom. -/
  | bot
  /-- Implication. -/
  | imp (φ₁ φ₂ : Formula Atom)
  /-- Until temporal operator: φ₁ U φ₂. -/
  | untl (φ₁ φ₂ : Formula Atom)
  /-- Since temporal operator: φ₁ S φ₂. -/
  | snce (φ₁ φ₂ : Formula Atom)
deriving DecidableEq, BEq

/-- Negation: ¬φ := φ → ⊥ -/
abbrev Formula.neg (φ : Formula Atom) : Formula Atom := .imp φ .bot

/-- Verum / top: ⊤ := ⊥ → ⊥ -/
abbrev Formula.top : Formula Atom := .imp .bot .bot

/-- Disjunction: φ₁ ∨ φ₂ := ¬φ₁ → φ₂ -/
abbrev Formula.or (φ₁ φ₂ : Formula Atom) : Formula Atom :=
  .imp (.imp φ₁ .bot) φ₂

/-- Conjunction: φ₁ ∧ φ₂ := ¬(φ₁ → ¬φ₂) -/
abbrev Formula.and (φ₁ φ₂ : Formula Atom) : Formula Atom :=
  .imp (.imp φ₁ (.imp φ₂ .bot)) .bot

/-- Biconditional: φ₁ ↔ φ₂ := (φ₁ → φ₂) ∧ (φ₂ → φ₁) -/
abbrev Formula.iff (φ₁ φ₂ : Formula Atom) : Formula Atom :=
  (φ₁.imp φ₂).and (φ₂.imp φ₁)

/-- Some future (eventually): F φ := φ U ⊤.
    Note: uses Burgess convention where `untl event guard` — φ is the event (holds at witness),
    ⊤ is the trivial guard. Equivalent to standard LTL `F φ = ⊤ U φ` semantically. -/
abbrev Formula.someFuture (φ : Formula Atom) : Formula Atom :=
  .untl φ .top

/-- All future (globally): G φ := ¬F ¬φ -/
abbrev Formula.allFuture (φ : Formula Atom) : Formula Atom :=
  .neg (.someFuture (.neg φ))

/-- Some past: P φ := φ S ⊤.
    Note: uses Burgess convention where `snce event guard` — φ is the event (holds at witness),
    ⊤ is the trivial guard. Equivalent to standard LTL `P φ = ⊤ S φ` semantically. -/
abbrev Formula.somePast (φ : Formula Atom) : Formula Atom :=
  .snce φ .top

/-- All past (historically): H φ := ¬P ¬φ -/
abbrev Formula.allPast (φ : Formula Atom) : Formula Atom :=
  .neg (.somePast (.neg φ))

@[inherit_doc] scoped prefix:40 "¬" => Formula.neg
@[inherit_doc] scoped infix:36 " ∧ " => Formula.and
@[inherit_doc] scoped infix:35 " ∨ " => Formula.or
@[inherit_doc] scoped infix:30 " → " => Formula.imp
@[inherit_doc] scoped infix:30 " ↔ " => Formula.iff
@[inherit_doc] scoped infix:40 " U " => Formula.untl
@[inherit_doc] scoped infix:40 " S " => Formula.snce
@[inherit_doc] scoped prefix:40 "𝐅" => Formula.someFuture
@[inherit_doc] scoped prefix:40 "𝐆" => Formula.allFuture
@[inherit_doc] scoped prefix:40 "𝐏" => Formula.somePast
@[inherit_doc] scoped prefix:40 "𝐇" => Formula.allPast

/-- Register `Temporal.Formula` as an instance of `TemporalConnectives`. -/
instance : TemporalConnectives (Formula Atom) where
  bot := .bot
  imp := .imp
  untl := .untl
  snce := .snce

instance : Bot (Formula Atom) := ⟨.bot⟩
instance : Top (Formula Atom) := ⟨.top⟩

end Cslib.Logic.Temporal

@[expose] public section

/-! ## Structural Properties and Derived Operators

Extensions to `Temporal.Formula` providing:
- Countable, Infinite, Denumerable instances
- BEq reflexivity and lawfulness
- Complexity measure
- Temporal depth and implication count
- Additional derived temporal operators
- Swap temporal duality transformation
- Atom collection function
- Positive hypothesis predicate
-/

namespace Cslib.Logic.Temporal

/-! ### Countable, Infinite, Denumerable Instances -/

section Countability

variable {Atom : Type*}

/-- `Formula.atom` is injective. -/
theorem Formula.atom_injective : Function.Injective (Formula.atom (Atom := Atom)) := by
  intro a b h
  injection h

namespace Formula

/-- Encode a formula into a natural number using Cantor pairing.
    Used to establish countability of formulas. -/
noncomputable def encodeNat [Encodable Atom] : Formula Atom → ℕ
  | .atom a => Nat.pair 0 (Encodable.encode a)
  | .bot => Nat.pair 1 0
  | .imp φ ψ => Nat.pair 2 (Nat.pair φ.encodeNat ψ.encodeNat)
  | .untl φ ψ => Nat.pair 3 (Nat.pair φ.encodeNat ψ.encodeNat)
  | .snce φ ψ => Nat.pair 4 (Nat.pair φ.encodeNat ψ.encodeNat)

theorem nat_pair_inj {a b c d : ℕ} (h : Nat.pair a b = Nat.pair c d) :
    a = c ∧ b = d := by
  have := congr_arg Nat.unpair h
  simp only [Nat.unpair_pair] at this
  exact Prod.mk.inj this

/-- The encoding is injective. -/
theorem encodeNat_injective [Encodable Atom] :
    Function.Injective (encodeNat (Atom := Atom)) := by
  intro φ ψ h
  induction φ generalizing ψ with
  | atom a =>
    cases ψ with
    | atom b =>
      have ⟨_, h2⟩ := nat_pair_inj h
      exact congrArg Formula.atom (Encodable.encode_injective h2)
    | bot => exact absurd (nat_pair_inj h).1 (by decide)
    | imp _ _ => exact absurd (nat_pair_inj h).1 (by decide)
    | untl _ _ => exact absurd (nat_pair_inj h).1 (by decide)
    | snce _ _ => exact absurd (nat_pair_inj h).1 (by decide)
  | bot =>
    cases ψ with
    | bot => rfl
    | atom _ => exact absurd (nat_pair_inj h).1 (by decide)
    | imp _ _ => exact absurd (nat_pair_inj h).1 (by decide)
    | untl _ _ => exact absurd (nat_pair_inj h).1 (by decide)
    | snce _ _ => exact absurd (nat_pair_inj h).1 (by decide)
  | imp a b iha ihb =>
    cases ψ with
    | imp c d =>
      have ⟨_, h2⟩ := nat_pair_inj h
      have ⟨h3, h4⟩ := nat_pair_inj h2
      exact congrArg₂ Formula.imp (iha h3) (ihb h4)
    | atom _ => exact absurd (nat_pair_inj h).1 (by decide)
    | bot => exact absurd (nat_pair_inj h).1 (by decide)
    | untl _ _ => exact absurd (nat_pair_inj h).1 (by decide)
    | snce _ _ => exact absurd (nat_pair_inj h).1 (by decide)
  | untl a b iha ihb =>
    cases ψ with
    | untl c d =>
      have ⟨_, h2⟩ := nat_pair_inj h
      have ⟨h3, h4⟩ := nat_pair_inj h2
      exact congrArg₂ Formula.untl (iha h3) (ihb h4)
    | atom _ => exact absurd (nat_pair_inj h).1 (by decide)
    | bot => exact absurd (nat_pair_inj h).1 (by decide)
    | imp _ _ => exact absurd (nat_pair_inj h).1 (by decide)
    | snce _ _ => exact absurd (nat_pair_inj h).1 (by decide)
  | snce a b iha ihb =>
    cases ψ with
    | snce c d =>
      have ⟨_, h2⟩ := nat_pair_inj h
      have ⟨h3, h4⟩ := nat_pair_inj h2
      exact congrArg₂ Formula.snce (iha h3) (ihb h4)
    | atom _ => exact absurd (nat_pair_inj h).1 (by decide)
    | bot => exact absurd (nat_pair_inj h).1 (by decide)
    | imp _ _ => exact absurd (nat_pair_inj h).1 (by decide)
    | untl _ _ => exact absurd (nat_pair_inj h).1 (by decide)

end Formula

/-- Formula is countable when Atom is countable. -/
instance [Countable Atom] : Countable (Formula Atom) := by
  have : Encodable Atom := Encodable.ofCountable Atom
  exact Countable.mk ⟨Formula.encodeNat, Formula.encodeNat_injective⟩

/-- Formula is infinite when Atom is infinite (via injection from Atom). -/
instance [Infinite Atom] : Infinite (Formula Atom) :=
  Infinite.of_injective Formula.atom Formula.atom_injective

/-- Formula is denumerable when Atom is both countable and infinite. -/
noncomputable instance [Countable Atom] [Infinite Atom] :
    Denumerable (Formula Atom) :=
  Classical.choice (nonempty_denumerable (Formula Atom))

end Countability

/-! ### BEq Reflexivity and Lawfulness -/

section BEqLaws

variable {Atom : Type*} [BEq Atom]

namespace Formula

/-- Helper: BEq on imp reduces to component BEq. -/
theorem beq_imp_eq (a b c d : Formula Atom) :
    (imp a b == imp c d) = ((a == c) && (b == d)) := rfl

/-- Helper: BEq on untl reduces to component BEq. -/
theorem beq_untl_eq (a b c d : Formula Atom) :
    (untl a b == untl c d) = ((a == c) && (b == d)) := rfl

/-- Helper: BEq on snce reduces to component BEq. -/
theorem beq_snce_eq (a b c d : Formula Atom) :
    (snce a b == snce c d) = ((a == c) && (b == d)) := rfl

/-- BEq on Formula is reflexive. -/
theorem beq_refl [ReflBEq Atom] (φ : Formula Atom) : (φ == φ) = true := by
  induction φ with
  | atom p => exact @beq_self_eq_true Atom _ _ p
  | bot => rfl
  | imp a b iha ihb => rw [beq_imp_eq, iha, ihb]; rfl
  | untl a b iha ihb => rw [beq_untl_eq, iha, ihb]; rfl
  | snce a b iha ihb => rw [beq_snce_eq, iha, ihb]; rfl

/-- BEq on Formula is sound: if `φ == ψ = true` then `φ = ψ`. -/
theorem eq_of_beq [LawfulBEq Atom] {φ ψ : Formula Atom}
    (h : (φ == ψ) = true) : φ = ψ := by
  induction φ generalizing ψ with
  | atom p =>
    match ψ with
    | atom q =>
      have heq : (atom p == atom q) = (p == q) := rfl
      rw [heq] at h; exact congrArg atom (beq_iff_eq.mp h)
    | bot | imp _ _ | untl _ _ | snce _ _ => exact nomatch h
  | bot =>
    match ψ with
    | bot => rfl
    | atom _ | imp _ _ | untl _ _ | snce _ _ => exact nomatch h
  | imp a b iha ihb =>
    match ψ with
    | imp c d =>
      have heq : (imp a b == imp c d) = ((a == c) && (b == d)) := rfl
      rw [heq] at h; simp only [Bool.and_eq_true] at h
      exact congrArg₂ imp (iha h.1) (ihb h.2)
    | atom _ | bot | untl _ _ | snce _ _ => exact nomatch h
  | untl a b iha ihb =>
    match ψ with
    | untl c d =>
      have heq : (untl a b == untl c d) = ((a == c) && (b == d)) := rfl
      rw [heq] at h; simp only [Bool.and_eq_true] at h
      exact congrArg₂ untl (iha h.1) (ihb h.2)
    | atom _ | bot | imp _ _ | snce _ _ => exact nomatch h
  | snce a b iha ihb =>
    match ψ with
    | snce c d =>
      have heq : (snce a b == snce c d) = ((a == c) && (b == d)) := rfl
      rw [heq] at h; simp only [Bool.and_eq_true] at h
      exact congrArg₂ snce (iha h.1) (ihb h.2)
    | atom _ | bot | imp _ _ | untl _ _ => exact nomatch h

end Formula

instance [ReflBEq Atom] : ReflBEq (Formula Atom) where
  rfl := Formula.beq_refl _

instance [LawfulBEq Atom] : LawfulBEq (Formula Atom) where
  eq_of_beq := Formula.eq_of_beq
  rfl := Formula.beq_refl _

end BEqLaws

/-! ### Complexity Measure -/

namespace Formula

variable {Atom : Type*}

/--
Structural complexity of a formula (number of connectives + 1).

Pattern-aware cases for derived temporal operators (Burgess convention: `untl event guard`):
- `F(φ) = φ U ⊤` → treated as overhead 1, not 4
- `P(φ) = φ S ⊤` → treated as overhead 1, not 4
- `G(φ) = ¬F(¬φ)` → treated as overhead 1, not 8
- `H(φ) = ¬P(¬φ)` → treated as overhead 1, not 8
- `next(φ) = ⊥ U φ` → treated as overhead 1
- `prev(φ) = ⊥ S φ` → treated as overhead 1
- `R(φ, ψ) = ¬(¬ψ U ¬φ)` → treated as overhead 1
- `T(φ, ψ) = ¬(¬ψ S ¬φ)` → treated as overhead 1
-/
def complexity : Formula Atom → Nat
  | .atom _ => 1
  | .bot => 1
  -- G(φ) = imp (untl (imp φ bot) (imp bot bot)) bot  [¬(¬φ U ⊤) in Burgess]
  | .imp (.untl (.imp φ .bot) (.imp .bot .bot)) .bot => 1 + complexity φ
  -- H(φ) = imp (snce (imp φ bot) (imp bot bot)) bot  [¬(¬φ S ⊤) in Burgess]
  | .imp (.snce (.imp φ .bot) (.imp .bot .bot)) .bot => 1 + complexity φ
  -- R(φ, ψ) = release = imp (untl (imp ψ bot) (imp φ bot)) bot  [¬(¬ψ_event U ¬φ_guard)]
  | .imp (.untl (.imp ψ .bot) (.imp φ .bot)) .bot =>
    1 + complexity φ + complexity ψ
  -- T(φ, ψ) = trigger = imp (snce (imp ψ bot) (imp φ bot)) bot  [¬(¬ψ_event S ¬φ_guard)]
  | .imp (.snce (.imp ψ .bot) (.imp φ .bot)) .bot =>
    1 + complexity φ + complexity ψ
  -- generic imp
  | .imp φ ψ => 1 + complexity φ + complexity ψ
  -- F(φ) = untl φ (imp bot bot)  [φ U ⊤ in Burgess]
  | .untl φ (.imp .bot .bot) => 1 + complexity φ
  -- next(φ) = untl φ bot  [φ U ⊥ in Burgess: guard ⊥ impossible, forces immediate step]
  | .untl φ .bot => 1 + complexity φ
  -- generic untl
  | .untl φ ψ => 1 + complexity φ + complexity ψ
  -- P(φ) = snce φ (imp bot bot)  [φ S ⊤ in Burgess]
  | .snce φ (.imp .bot .bot) => 1 + complexity φ
  -- prev(φ) = snce φ bot  [φ S ⊥ in Burgess: guard ⊥ impossible, forces immediate step]
  | .snce φ .bot => 1 + complexity φ
  -- generic snce
  | .snce φ ψ => 1 + complexity φ + complexity ψ

/-! ### Temporal Depth -/

/--
Temporal depth: nesting level of temporal operators.

Computes the maximum nesting depth of temporal operators (U, S) in a formula.
-/
def temporalDepth : Formula Atom → Nat
  | .atom _ => 0
  | .bot => 0
  | .imp φ ψ => max φ.temporalDepth ψ.temporalDepth
  | .untl φ ψ => 1 + max φ.temporalDepth ψ.temporalDepth
  | .snce φ ψ => 1 + max φ.temporalDepth ψ.temporalDepth

/--
Count implication operators in a formula.

Useful for heuristic scoring in proof search.
-/
def countImplications : Formula Atom → Nat
  | .atom _ => 0
  | .bot => 0
  | .imp φ ψ => 1 + φ.countImplications + ψ.countImplications
  | .untl φ ψ => φ.countImplications + ψ.countImplications
  | .snce φ ψ => φ.countImplications + ψ.countImplications

/-! ### Additional Derived Temporal Operators -/

/-- Next-step operator: X(φ) = φ U ⊥.
    X(φ) at t means φ holds at t+1. Uses Burgess convention: φ is the event,
    ⊥ is the guard (impossible), forcing the witness to be immediately next. -/
def next (φ : Formula Atom) : Formula Atom := .untl φ .bot

/-- Previous-step operator: Y(φ) = φ S ⊥.
    Y(φ) at t means φ holds at t-1. Uses Burgess convention: φ is the event,
    ⊥ is the guard (impossible), forcing the witness to be immediately previous. -/
def prev (φ : Formula Atom) : Formula Atom := .snce φ .bot

/-- Derived reflexive future operator: G'φ := φ ∧ Gφ. -/
def weakFuture (φ : Formula Atom) : Formula Atom :=
  φ ∧ 𝐆φ

/-- Derived reflexive past operator: H'φ := φ ∧ Hφ. -/
def weakPast (φ : Formula Atom) : Formula Atom :=
  φ ∧ 𝐇φ

/-- Temporal 'always' operator (△φ): Hφ ∧ φ ∧ Gφ.
    φ holds at all times (past, present, and future). -/
def always (φ : Formula Atom) : Formula Atom :=
  𝐇φ ∧ (φ ∧ 𝐆φ)

/-- Temporal 'sometimes' operator (▽φ): ¬△¬φ.
    φ holds at some time (past, present, or future). -/
def sometimes (φ : Formula Atom) : Formula Atom :=
  ¬(always (¬φ))

/-- Release operator R(φ, ψ) := ¬(¬φ U ¬ψ). Dual of Until.
    In Burgess convention: `untl (neg ψ) (neg φ)` where ¬ψ is the event and ¬φ is the guard,
    corresponding to `¬φ U ¬ψ` in standard LTL notation. -/
def release (φ ψ : Formula Atom) : Formula Atom :=
  ¬((¬ψ) U (¬φ))

/-- Trigger operator T(φ, ψ) := ¬(¬φ S ¬ψ). Dual of Since (past analog of Release).
    In Burgess convention: `snce (neg ψ) (neg φ)` where ¬ψ is the event and ¬φ is the guard,
    corresponding to `¬φ S ¬ψ` in standard LTL notation. -/
def trigger (φ ψ : Formula Atom) : Formula Atom :=
  ¬((¬ψ) S (¬φ))

/-- Weak Until operator W(φ, ψ) := (φ U ψ) ∨ G(φ). Until without the liveness requirement. -/
def weakUntil (φ ψ : Formula Atom) : Formula Atom :=
  (φ U ψ) ∨ 𝐆φ

/-- Weak Since operator WS(φ, ψ) := (φ S ψ) ∨ H(φ). Since without the liveness requirement. -/
def weakSince (φ ψ : Formula Atom) : Formula Atom :=
  (φ S ψ) ∨ 𝐇φ

/-- Strong Release operator M(φ, ψ) := ψ U (ψ ∧ φ). Dual of weak until.
    In Burgess convention: `untl (and ψ φ) ψ` where ψ∧φ is the event and ψ is the guard. -/
def strongRelease (φ ψ : Formula Atom) : Formula Atom :=
  (ψ ∧ φ) U ψ

/-- Strong Trigger operator ST(φ, ψ) := ψ S (ψ ∧ φ). Past dual of strong release.
    In Burgess convention: `snce (and ψ φ) ψ` where ψ∧φ is the event and ψ is the guard. -/
def strongTrigger (φ ψ : Formula Atom) : Formula Atom :=
  (ψ ∧ φ) S ψ

/-- Notation for temporal 'always' operator using upward triangle. -/
scoped prefix:80 "△" => Formula.always

/-- Notation for temporal 'sometimes' operator using downward triangle. -/
scoped prefix:80 "▽" => Formula.sometimes

/-! ### Swap Temporal Duality -/

/--
Swap temporal operators (past ↔ future) in a formula.

This transformation is used in the temporal duality inference rule (TD):
if `⊢ φ` then `⊢ swapTemporal φ`.
-/
def swapTemporal : Formula Atom → Formula Atom
  | .atom s => .atom s
  | .bot => .bot
  | .imp φ ψ => .imp (swapTemporal φ) (swapTemporal ψ)
  | .untl φ ψ => .snce (swapTemporal φ) (swapTemporal ψ)
  | .snce φ ψ => .untl (swapTemporal φ) (swapTemporal ψ)

/-- swapTemporal is an involution (applying it twice gives identity). -/
theorem swapTemporal_involution (φ : Formula Atom) :
    φ.swapTemporal.swapTemporal = φ := by
  induction φ with
  | atom _ => rfl
  | bot => rfl
  | imp _ _ ihp ihq => simp only [swapTemporal, ihp, ihq]
  | untl _ _ ih1 ih2 => simp only [swapTemporal, ih1, ih2]
  | snce _ _ ih1 ih2 => simp only [swapTemporal, ih1, ih2]

/-- swapTemporal distributes over negation: swap(¬φ) = ¬(swap φ). -/
theorem swapTemporal_neg (φ : Formula Atom) :
    (Formula.neg φ).swapTemporal = Formula.neg φ.swapTemporal := by
  simp only [Formula.neg, swapTemporal]

/-- swapTemporal exchanges someFuture and somePast: swap(Fφ) = P(swap φ). -/
@[simp]
theorem swapTemporal_someFuture (φ : Formula Atom) :
    (Formula.someFuture φ).swapTemporal = Formula.somePast φ.swapTemporal := by
  simp only [Formula.somePast, Formula.top, swapTemporal]

/-- swapTemporal exchanges somePast and someFuture: swap(Pφ) = F(swap φ). -/
@[simp]
theorem swapTemporal_somePast (φ : Formula Atom) :
    (Formula.somePast φ).swapTemporal = Formula.someFuture φ.swapTemporal := by
  simp only [Formula.someFuture, Formula.top, swapTemporal]

/-- swapTemporal exchanges allFuture and allPast: swap(Gφ) = H(swap φ). -/
@[simp]
theorem swapTemporal_allFuture (φ : Formula Atom) :
    (Formula.allFuture φ).swapTemporal = Formula.allPast φ.swapTemporal := by
  simp only [Formula.allPast, swapTemporal]

/-- swapTemporal exchanges allPast and allFuture: swap(Hφ) = G(swap φ). -/
@[simp]
theorem swapTemporal_allPast (φ : Formula Atom) :
    (Formula.allPast φ).swapTemporal = Formula.allFuture φ.swapTemporal := by
  simp only [Formula.allFuture, swapTemporal]

/-- swapTemporal distributes over next/prev: swap(X(φ)) = Y(swap(φ)). -/
theorem swapTemporal_next (φ : Formula Atom) :
    (next φ).swapTemporal = prev φ.swapTemporal := by
  simp [next, prev, swapTemporal]

/-- swapTemporal distributes over prev/next: swap(Y(φ)) = X(swap(φ)). -/
theorem swapTemporal_prev (φ : Formula Atom) :
    (prev φ).swapTemporal = next φ.swapTemporal := by
  simp [prev, next, swapTemporal]

/-- swapTemporal distributes over strongRelease: swap(M(φ,ψ)) = ST(swap φ, swap ψ). -/
theorem swapTemporal_strongRelease (φ ψ : Formula Atom) :
    (strongRelease φ ψ).swapTemporal =
      strongTrigger φ.swapTemporal ψ.swapTemporal := by
  simp [strongRelease, strongTrigger, Formula.and, swapTemporal]

/-- swapTemporal distributes over strongTrigger: swap(ST(φ,ψ)) = M(swap φ, swap ψ). -/
theorem swapTemporal_strongTrigger (φ ψ : Formula Atom) :
    (strongTrigger φ ψ).swapTemporal =
      strongRelease φ.swapTemporal ψ.swapTemporal := by
  simp [strongRelease, strongTrigger, Formula.and, swapTemporal]

/-! ### Positive Hypothesis Predicate -/

/--
Whether a formula requires the single-family/single-time hypotheses.
All non-imp formulas need these for propagation.
-/
def needsPositiveHypotheses : Formula Atom → Bool
  | .imp _ _ => false
  | _ => true

@[simp] lemma needsPositiveHypotheses_atom (s : Atom) :
    (Formula.atom s).needsPositiveHypotheses = true := rfl

@[simp] lemma needsPositiveHypotheses_bot :
    (Formula.bot : Formula Atom).needsPositiveHypotheses = true := rfl

@[simp] lemma needsPositiveHypotheses_untl (p q : Formula Atom) :
    (Formula.untl p q).needsPositiveHypotheses = true := rfl

@[simp] lemma needsPositiveHypotheses_snce (p q : Formula Atom) :
    (Formula.snce p q).needsPositiveHypotheses = true := rfl

@[simp] lemma needsPositiveHypotheses_imp (p q : Formula Atom) :
    (Formula.imp p q).needsPositiveHypotheses = false := rfl

/-! ### Propositional Atoms -/

section Atoms

variable [DecidableEq Atom]

/-- The set of propositional atoms appearing in a formula. -/
def atoms : Formula Atom → Finset Atom
  | .atom s => {s}
  | .bot => ∅
  | .imp φ ψ => atoms φ ∪ atoms ψ
  | .untl φ ψ => atoms φ ∪ atoms ψ
  | .snce φ ψ => atoms φ ∪ atoms ψ

/-- swapTemporal preserves atoms: swapping past/future does not change which atoms appear. -/
theorem atoms_swapTemporal (φ : Formula Atom) :
    atoms (swapTemporal φ) = atoms φ := by
  induction φ with
  | atom _ => rfl
  | bot => rfl
  | imp _ _ ih1 ih2 => simp only [swapTemporal, atoms]; rw [ih1, ih2]
  | untl _ _ ih1 ih2 => simp only [swapTemporal, atoms]; rw [ih1, ih2]
  | snce _ _ ih1 ih2 => simp only [swapTemporal, atoms]; rw [ih1, ih2]

end Atoms

end Formula

end Cslib.Logic.Temporal

end
