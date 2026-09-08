/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Foundations.Data.OmegaSequence.Defs
public import Cslib.Logics.Modal.Unary.Basic

/-! # Linear Temporal Logic

This module presents Linear Temporal Logic (LTL) as an instantiation of the general modal-logic
framework.

The semantic object underlying LTL is an `ωSequence State`. The modal worlds are positions in the
sequence, together with an auxiliary anchor used to express intervals. Atomic propositions are
interpreted on the actual state occurring at the current position of the sequence.

The modal signature contains three unary operators:

* `next`, which moves to the immediately following position;
* `seek`, which chooses a position in the future and records the current position as an anchor;
* `between`, which ranges over the positions between the anchor and the current position.

The standard LTL operators are then derived. In particular,

`φ U ψ = d⟨seek⟩(ψ ∧ d[between]φ)`.

Thus, at position `n`, `φ U ψ` holds exactly when there is a `k ≥ n` where `ψ` holds and `φ` holds
at every position `j` with `n ≤ j < k`.

`Proposition.IsLTL` identifies the standard LTL fragment inside the modal syntax. Raw uses of
`between` can observe the anchor, whereas formulas in this fragment cannot
(`Satisfies.anchor_iff`). All satisfaction judgements use the generic modal semantics.

For ordinary use, write `⇓LTL[m,n ⊨ φ]` to evaluate `φ` at position `n`, or `⇓LTL[m ⊨ φ]`
to evaluate it at the start of the sequence. These are abbreviations for modal judgements with
an internal anchor fixed to zero. The `Satisfies.at_*` lemmas expose the usual temporal semantics
using only sequence positions. Boolean connectives use the generic modal lemmas directly.
-/

@[expose] public section

namespace Cslib.Logic.Modal.LTL

open PFunctor
open scoped Proposition Satisfies InferenceSystem

universe u v

variable {State : Type u} {Atom : Type v}

/-! ## Signature -/

/-- Primitive modal operators used to present LTL. -/
inductive Operator where
  | next
  | seek
  | between

/-- The modal signature used to present LTL. All primitive operators are unary. -/
abbrev τLTL : PFunctor := PFunctor.mkUnary Operator

/-- LTL propositions are modal propositions over `τLTL`. -/
abbrev Proposition (Atom : Type v) := Modal.Proposition τLTL Atom

/-! ## Temporal frame -/

/-- A temporal position with an auxiliary anchor.

`now` is the position at which propositions are evaluated. `anchor` is semantic bookkeeping used by
`until` to remember the beginning of an interval.
-/
structure Point where
  /-- Current position in the sequence. -/
  now : ℕ
  /-- Beginning of the interval selected by `seek`. -/
  anchor : ℕ

/-- The accessibility relation associated with each primitive LTL operator.

At a point `(n, a)`:

* `next` reaches exactly `(n + 1, a)`;
* `seek` reaches any `(k, n)` with `n ≤ k`;
* from `(k, n)`, `between` reaches exactly the points `(j, n)` with `n ≤ j < k`.
-/
def relation : Operator → Point → Point → Prop
  | .next, p, q =>
      q = ⟨p.now + 1, p.anchor⟩
  | .seek, p, q =>
      ∃ k, p.now ≤ k ∧ q = ⟨k, p.now⟩
  | .between, p, q =>
      ∃ j, p.anchor ≤ j ∧ j < p.now ∧ q = ⟨j, p.anchor⟩

/-- The canonical frame for LTL. -/
def Frame.ltl : Frame Point τLTL :=
  Frame.ofRelations relation

@[simp, scoped grind _=_, modal _=_]
theorem Frame.ltl_diagonal_iff (op : Operator) (p q : Point) :
    Frame.ltl.diagonal op p q ↔ relation op p q := by
  rfl

/-! ## Models over traces -/

/-- Builds the LTL model induced by an infinite trace and a valuation on its states.

The auxiliary anchor is invisible to atomic propositions: atoms are evaluated only on the state
`t p.now` occurring at the current position.
-/
def Model.ofωSequence (t : ωSequence State) (v : State → Atom → Prop) :
    Model Point τLTL Atom where
  toFrame := Frame.ltl
  v p a := v (t p.now) a

@[simp, scoped grind =, modal =]
theorem Model.ofωSequence_diagonal_iff
    (t : ωSequence State) (v : State → Atom → Prop)
    (op : Operator) (p q : Point) :
    (Model.ofωSequence t v).toFrame.diagonal op p q ↔ relation op p q := by
  rfl

@[scoped grind =, modal =]
theorem Satisfies.ofωSequence_atom_iff
    (t : ωSequence State) (v : State → Atom → Prop)
    (n a : ℕ) (p : Atom) :
    ⇓Modal[Model.ofωSequence t v,⟨n, a⟩ ⊨ p] ↔ v (t n) p := by
  rfl

/-- Atomic propositions can be taken directly to be predicates on states. -/
abbrev StateAtom (State : Type u) := State → Prop

/-- The canonical LTL model when atoms are predicates on states. -/
def Model.ofTracePredicates (t : ωSequence State) :
    Model Point τLTL (StateAtom State) :=
  Model.ofωSequence t (fun s P => P s)

@[scoped grind =, modal =]
theorem Satisfies.ofTracePredicates_atom_iff
    (t : ωSequence State) (n a : ℕ) (P : StateAtom State) :
    ⇓Modal[Model.ofTracePredicates t,⟨n, a⟩ ⊨ P] ↔ P (t n) := by
  rfl

/-- A modal judgement at a sequence position, with the auxiliary anchor hidden.

For standard LTL formulas the choice of anchor is immaterial (`Satisfies.at_iff`).
-/
abbrev judgementAt (m : Model Point τLTL Atom) (n : ℕ) (φ : Proposition Atom) :
    Modal.Judgement Point τLTL Atom :=
  Modal.Judgement.mk m ⟨n, 0⟩ φ

/-- Evaluate an LTL formula at a sequence position, using the modal inference system. -/
scoped notation "LTL[" m "," n " ⊨ " φ "]" => judgementAt m n φ

/-- Evaluate an LTL formula at the start of a sequence. -/
scoped notation "LTL[" m " ⊨ " φ "]" => judgementAt m 0 φ

/-! ## Temporal operators -/

/-- Next: `φ` holds at the immediately following position. -/
abbrev Proposition.next (φ : Proposition Atom) : Proposition Atom :=
  d⟨Operator.next⟩φ

/-- Until: `ψ` holds at some future position, and `φ` holds at every position before it starting
from the current one. -/
abbrev Proposition.until (φ ψ : Proposition Atom) : Proposition Atom :=
  d⟨Operator.seek⟩(ψ ∧ d[Operator.between]φ)

/-- Eventually: `φ` holds at some position at or after the current one. -/
abbrev Proposition.eventually (φ : Proposition Atom) : Proposition Atom :=
  Proposition.until ⊤ φ

/-- Always: `φ` holds at every position at or after the current one. -/
abbrev Proposition.always (φ : Proposition Atom) : Proposition Atom :=
  ¬Proposition.eventually (¬φ)

/-- Release, dual to until. -/
abbrev Proposition.release (φ ψ : Proposition Atom) : Proposition Atom :=
  ¬Proposition.until (¬φ) (¬ψ)

/-! ## Semantics of the primitive temporal modalities -/

@[scoped grind =, modal =]
theorem Satisfies.next_iff
    (t : ωSequence State) (v : State → Atom → Prop)
    (n a : ℕ) (φ : Proposition Atom) :
    ⇓Modal[Model.ofωSequence t v,⟨n, a⟩ ⊨ φ.next] ↔
      ⇓Modal[Model.ofωSequence t v,⟨n + 1, a⟩ ⊨ φ] := by
  change
    ⇓Modal[Model.ofωSequence t v,⟨n, a⟩ ⊨ d⟨Operator.next⟩φ] ↔
      ⇓Modal[Model.ofωSequence t v,⟨n + 1, a⟩ ⊨ φ]
  rw [Cslib.Logic.Modal.Satisfies.dynDiamond_iff_exists]
  constructor
  · rintro ⟨q, hr, hφ⟩
    have hq := (Model.ofωSequence_diagonal_iff t v .next ⟨n, a⟩ q).mp hr
    change q = ⟨n + 1, a⟩ at hq
    subst q
    exact hφ
  · intro hφ
    refine ⟨⟨n + 1, a⟩, ?_, hφ⟩
    apply (Model.ofωSequence_diagonal_iff t v .next ⟨n, a⟩ ⟨n + 1, a⟩).mpr
    rfl

@[scoped grind =, modal =]
theorem Satisfies.seek_iff
    (t : ωSequence State) (v : State → Atom → Prop)
    (n a : ℕ) (φ : Proposition Atom) :
    ⇓Modal[Model.ofωSequence t v,⟨n, a⟩ ⊨ d⟨Operator.seek⟩φ] ↔
      ∃ k, n ≤ k ∧ ⇓Modal[Model.ofωSequence t v,⟨k, n⟩ ⊨ φ] := by
  rw [Cslib.Logic.Modal.Satisfies.dynDiamond_iff_exists]
  constructor
  · rintro ⟨q, hr, hφ⟩
    have hq := (Model.ofωSequence_diagonal_iff t v .seek ⟨n, a⟩ q).mp hr
    change ∃ k, n ≤ k ∧ q = ⟨k, n⟩ at hq
    rcases hq with ⟨k, hnk, rfl⟩
    exact ⟨k, hnk, hφ⟩
  · rintro ⟨k, hnk, hφ⟩
    refine ⟨⟨k, n⟩, ?_, hφ⟩
    apply (Model.ofωSequence_diagonal_iff t v .seek ⟨n, a⟩ ⟨k, n⟩).mpr
    exact ⟨k, hnk, rfl⟩

@[scoped grind =, modal =]
theorem Satisfies.between_iff
    (t : ωSequence State) (v : State → Atom → Prop)
    (k n : ℕ) (φ : Proposition Atom) :
    ⇓Modal[Model.ofωSequence t v,⟨k, n⟩ ⊨ d[Operator.between]φ] ↔
      ∀ j, n ≤ j → j < k → ⇓Modal[Model.ofωSequence t v,⟨j, n⟩ ⊨ φ] := by
  rw [Cslib.Logic.Modal.Satisfies.dynBox_iff_forall]
  constructor
  · intro h j hnj hjk
    apply h ⟨j, n⟩
    apply (Model.ofωSequence_diagonal_iff t v .between ⟨k, n⟩ ⟨j, n⟩).mpr
    exact ⟨j, hnj, hjk, rfl⟩
  · intro h q hr
    have hq := (Model.ofωSequence_diagonal_iff t v .between ⟨k, n⟩ q).mp hr
    change ∃ j, n ≤ j ∧ j < k ∧ q = ⟨j, n⟩ at hq
    rcases hq with ⟨j, hnj, hjk, rfl⟩
    exact h j hnj hjk

/-! ## Semantics of the standard LTL operators -/

@[scoped grind =, modal =]
theorem Satisfies.until_iff
    (t : ωSequence State) (v : State → Atom → Prop)
    (n a : ℕ) (φ ψ : Proposition Atom) :
    ⇓Modal[Model.ofωSequence t v,⟨n, a⟩ ⊨ φ.until ψ] ↔
      ∃ k, n ≤ k ∧
        ⇓Modal[Model.ofωSequence t v,⟨k, n⟩ ⊨ ψ] ∧
        ∀ j, n ≤ j → j < k → ⇓Modal[Model.ofωSequence t v,⟨j, n⟩ ⊨ φ] := by
  change
    ⇓Modal[Model.ofωSequence t v,⟨n, a⟩ ⊨
      d⟨Operator.seek⟩(ψ ∧ d[Operator.between]φ)] ↔ _
  rw [Satisfies.seek_iff]
  constructor
  · rintro ⟨k, hnk, hk⟩
    rw [Cslib.Logic.Modal.Satisfies.and_iff_and] at hk
    rcases hk with ⟨hψ, hbetween⟩
    rw [Satisfies.between_iff] at hbetween
    exact ⟨k, hnk, hψ, hbetween⟩
  · rintro ⟨k, hnk, hψ, hφ⟩
    refine ⟨k, hnk, ?_⟩
    rw [Cslib.Logic.Modal.Satisfies.and_iff_and, Satisfies.between_iff]
    exact ⟨hψ, hφ⟩

@[scoped grind =, modal =]
theorem Satisfies.eventually_iff
    (t : ωSequence State) (v : State → Atom → Prop)
    (n a : ℕ) (φ : Proposition Atom) :
    ⇓Modal[Model.ofωSequence t v,⟨n, a⟩ ⊨ φ.eventually] ↔
      ∃ k, n ≤ k ∧ ⇓Modal[Model.ofωSequence t v,⟨k, n⟩ ⊨ φ] := by
  change ⇓Modal[Model.ofωSequence t v,⟨n, a⟩ ⊨ (⊤ : Proposition Atom).until φ] ↔ _
  rw [Satisfies.until_iff]
  constructor
  · rintro ⟨k, hnk, hφ, _⟩
    exact ⟨k, hnk, hφ⟩
  · rintro ⟨k, hnk, hφ⟩
    refine ⟨k, hnk, hφ, ?_⟩
    intro j _ _
    exact Cslib.Logic.Modal.Satisfies.true

@[scoped grind =, modal =]
theorem Satisfies.always_iff
    (t : ωSequence State) (v : State → Atom → Prop)
    (n a : ℕ) (φ : Proposition Atom) :
    ⇓Modal[Model.ofωSequence t v,⟨n, a⟩ ⊨ φ.always] ↔
      ∀ k, n ≤ k → ⇓Modal[Model.ofωSequence t v,⟨k, n⟩ ⊨ φ] := by
  change
    ⇓Modal[Model.ofωSequence t v,⟨n, a⟩ ⊨ ¬(¬φ).eventually] ↔ _
  rw [Cslib.Logic.Modal.Satisfies.not_iff_not, Satisfies.eventually_iff]
  constructor
  · intro h k hnk
    by_contra hk
    apply h
    refine ⟨k, hnk, ?_⟩
    exact Cslib.Logic.Modal.Satisfies.not_iff_not.mpr hk
  · intro h hex
    rcases hex with ⟨k, hnk, hk⟩
    exact Cslib.Logic.Modal.Satisfies.not_iff_not.mp hk (h k hnk)

/-- Release holds when every future position either satisfies `ψ` or is preceded by a
position satisfying `φ`. The position satisfying `φ` must itself satisfy `ψ`. -/
@[scoped grind =, modal =]
theorem Satisfies.release_iff
    (t : ωSequence State) (v : State → Atom → Prop)
    (n a : ℕ) (φ ψ : Proposition Atom) :
    ⇓Modal[Model.ofωSequence t v,⟨n, a⟩ ⊨ φ.release ψ] ↔
      ∀ k, n ≤ k →
        ⇓Modal[Model.ofωSequence t v,⟨k, n⟩ ⊨ ψ] ∨
        ∃ j, n ≤ j ∧ j < k ∧ ⇓Modal[Model.ofωSequence t v,⟨j, n⟩ ⊨ φ] := by
  change ⇓Modal[Model.ofωSequence t v,⟨n, a⟩ ⊨ ¬(¬φ).until (¬ψ)] ↔ _
  simp only [Modal.Satisfies.not_iff_not, Satisfies.until_iff]
  push Not
  simp only [or_iff_not_imp_left]

/-! ## The standard LTL fragment

This predicate restricts the existing modal propositions; it does not introduce another syntax.
Its constructors also provide an induction principle for standard LTL formulas.
-/

/-- The fragment generated by atoms, Boolean connectives, next, and until. -/
inductive Proposition.IsLTL : Proposition Atom → Prop where
  /-- An atomic proposition is an LTL formula. -/
  | atom (p : Atom) : IsLTL (.atom p)
  /-- Falsity is an LTL formula. -/
  | false : IsLTL ⊥
  /-- LTL is closed under negation. -/
  | not {φ} : IsLTL φ → IsLTL (¬φ)
  /-- LTL is closed under disjunction. -/
  | or {φ ψ} : IsLTL φ → IsLTL ψ → IsLTL (φ ∨ ψ)
  /-- LTL is closed under next. -/
  | next {φ} : IsLTL φ → IsLTL φ.next
  /-- LTL is closed under until. -/
  | until {φ ψ} : IsLTL φ → IsLTL ψ → IsLTL (φ.until ψ)

namespace Proposition.IsLTL

/-- Truth belongs to the LTL fragment. -/
theorem true : IsLTL (⊤ : Proposition Atom) := .not .false

/-- The LTL fragment is closed under conjunction. -/
theorem and {φ ψ : Proposition Atom} (hφ : IsLTL φ) (hψ : IsLTL ψ) :
    IsLTL (φ ∧ ψ) := .not (.or (.not hφ) (.not hψ))

/-- The LTL fragment is closed under implication. -/
theorem imp {φ ψ : Proposition Atom} (hφ : IsLTL φ) (hψ : IsLTL ψ) :
    IsLTL (φ → ψ) := .or (.not hφ) hψ

/-- The LTL fragment is closed under bi-implication. -/
theorem iff {φ ψ : Proposition Atom} (hφ : IsLTL φ) (hψ : IsLTL ψ) :
    IsLTL (φ ↔ ψ) := (hφ.imp hψ).and (hψ.imp hφ)

/-- The LTL fragment is closed under eventually. -/
theorem eventually {φ : Proposition Atom} (hφ : IsLTL φ) :
    IsLTL φ.eventually := .until .true hφ

/-- The LTL fragment is closed under always. -/
theorem always {φ : Proposition Atom} (hφ : IsLTL φ) :
    IsLTL φ.always := hφ.not.eventually.not

/-- The LTL fragment is closed under release. -/
theorem release {φ ψ : Proposition Atom} (hφ : IsLTL φ) (hψ : IsLTL ψ) :
    IsLTL (φ.release ψ) := (hφ.not.until hψ.not).not

end Proposition.IsLTL

/-- Standard LTL formulas cannot observe the auxiliary anchor, including under nested untils. -/
theorem Satisfies.anchor_iff
    (t : ωSequence State) (v : State → Atom → Prop)
    {φ : Proposition Atom} (hφ : φ.IsLTL) (n a b : ℕ) :
    ⇓Modal[Model.ofωSequence t v,⟨n, a⟩ ⊨ φ] ↔
      ⇓Modal[Model.ofωSequence t v,⟨n, b⟩ ⊨ φ] := by
  induction hφ generalizing n a b with
  | atom => rfl
  | false => rfl
  | not _ ih => simp only [Modal.Satisfies.not_iff_not, ih n a b]
  | or _ _ ihφ ihψ => simp only [Modal.Satisfies.or_iff_or, ihφ n a b, ihψ n a b]
  | next _ ih => simpa only [Satisfies.next_iff] using ih (n + 1) a b
  | «until» => rw [Satisfies.until_iff, Satisfies.until_iff]

/-- Standard until semantics with a fixed anchor for all subformulas. -/
theorem Satisfies.until_iff_of_isLTL
    (t : ωSequence State) (v : State → Atom → Prop)
    (n a : ℕ) {φ ψ : Proposition Atom} (hφ : φ.IsLTL) (hψ : ψ.IsLTL) :
    ⇓Modal[Model.ofωSequence t v,⟨n, a⟩ ⊨ φ.until ψ] ↔
      ∃ k, n ≤ k ∧
        ⇓Modal[Model.ofωSequence t v,⟨k, a⟩ ⊨ ψ] ∧
        ∀ j, n ≤ j → j < k → ⇓Modal[Model.ofωSequence t v,⟨j, a⟩ ⊨ φ] := by
  simp only [Satisfies.until_iff, Satisfies.anchor_iff t v hφ _ n a,
    Satisfies.anchor_iff t v hψ _ n a]

/-- Standard eventually semantics with a fixed anchor. -/
theorem Satisfies.eventually_iff_of_isLTL
    (t : ωSequence State) (v : State → Atom → Prop)
    (n a : ℕ) {φ : Proposition Atom} (hφ : φ.IsLTL) :
    ⇓Modal[Model.ofωSequence t v,⟨n, a⟩ ⊨ φ.eventually] ↔
      ∃ k, n ≤ k ∧ ⇓Modal[Model.ofωSequence t v,⟨k, a⟩ ⊨ φ] := by
  simp only [Satisfies.eventually_iff, Satisfies.anchor_iff t v hφ _ n a]

/-- Standard always semantics with a fixed anchor. -/
theorem Satisfies.always_iff_of_isLTL
    (t : ωSequence State) (v : State → Atom → Prop)
    (n a : ℕ) {φ : Proposition Atom} (hφ : φ.IsLTL) :
    ⇓Modal[Model.ofωSequence t v,⟨n, a⟩ ⊨ φ.always] ↔
      ∀ k, n ≤ k → ⇓Modal[Model.ofωSequence t v,⟨k, a⟩ ⊨ φ] := by
  simp only [Satisfies.always_iff, Satisfies.anchor_iff t v hφ _ n a]

/-- Standard release semantics with a fixed anchor. -/
theorem Satisfies.release_iff_of_isLTL
    (t : ωSequence State) (v : State → Atom → Prop)
    (n a : ℕ) {φ ψ : Proposition Atom} (hφ : φ.IsLTL) (hψ : ψ.IsLTL) :
    ⇓Modal[Model.ofωSequence t v,⟨n, a⟩ ⊨ φ.release ψ] ↔
      ∀ k, n ≤ k →
        ⇓Modal[Model.ofωSequence t v,⟨k, a⟩ ⊨ ψ] ∨
        ∃ j, n ≤ j ∧ j < k ∧ ⇓Modal[Model.ofωSequence t v,⟨j, a⟩ ⊨ φ] := by
  simp only [Satisfies.release_iff, Satisfies.anchor_iff t v hφ _ n a,
    Satisfies.anchor_iff t v hψ _ n a]

/-- Unfolding strong until by one step. -/
theorem Satisfies.until_unfold
    (t : ωSequence State) (v : State → Atom → Prop)
    (n a : ℕ) {φ ψ : Proposition Atom} (hφ : φ.IsLTL) (hψ : ψ.IsLTL) :
    ⇓Modal[Model.ofωSequence t v,⟨n, a⟩ ⊨ φ.until ψ] ↔
      ⇓Modal[Model.ofωSequence t v,⟨n, a⟩ ⊨ ψ ∨ (φ ∧ (φ.until ψ).next)] := by
  simp only [Modal.Satisfies.or_iff_or, Modal.Satisfies.and_iff_and, Satisfies.next_iff,
    Satisfies.until_iff_of_isLTL t v _ a hφ hψ]
  constructor
  · rintro ⟨k, hnk, hψk, hφk⟩
    by_cases h : n = k
    · subst k
      exact Or.inl hψk
    · exact Or.inr ⟨hφk n (by omega) (by omega),
        k, by omega, hψk, fun j hj hk => hφk j (by omega) hk⟩
  · rintro (hψn | ⟨hφn, k, hnk, hψk, hφk⟩)
    · exact ⟨n, Nat.le_refl n, hψn, by omega⟩
    · refine ⟨k, by omega, hψk, fun j hj hk => ?_⟩
      by_cases h : j = n
      · simpa only [h] using hφn
      · exact hφk j (by omega) hk

/-! ## Semantics at sequence positions -/

/-- The position API agrees with evaluation at any auxiliary anchor for standard LTL formulas. -/
theorem Satisfies.at_iff
    (t : ωSequence State) (v : State → Atom → Prop)
    {φ : Proposition Atom} (hφ : φ.IsLTL) (n a : ℕ) :
    ⇓LTL[Model.ofωSequence t v,n ⊨ φ] ↔
      ⇓Modal[Model.ofωSequence t v,⟨n, a⟩ ⊨ φ] :=
  Satisfies.anchor_iff t v hφ n 0 a

/-- Atoms refer to the state at the chosen sequence position. -/
theorem Satisfies.at_atom_iff
    (t : ωSequence State) (v : State → Atom → Prop) (n : ℕ) (p : Atom) :
    ⇓LTL[Model.ofωSequence t v,n ⊨ p] ↔ v (t n) p := Iff.rfl

/-- Predicate atoms apply directly to the state at the chosen sequence position. -/
theorem Satisfies.at_predicate_iff (t : ωSequence State) (n : ℕ) (P : StateAtom State) :
    ⇓LTL[Model.ofTracePredicates t,n ⊨ P] ↔ P (t n) := Iff.rfl

/-- Next advances the sequence position by one. -/
theorem Satisfies.at_next_iff
    (t : ωSequence State) (v : State → Atom → Prop) (n : ℕ) (φ : Proposition Atom) :
    ⇓LTL[Model.ofωSequence t v,n ⊨ φ.next] ↔
      ⇓LTL[Model.ofωSequence t v,n + 1 ⊨ φ] :=
  Satisfies.next_iff t v n 0 φ

/-- Strong until has a future witness, with its left operand holding strictly before it. -/
theorem Satisfies.at_until_iff
    (t : ωSequence State) (v : State → Atom → Prop)
    (n : ℕ) {φ ψ : Proposition Atom} (hφ : φ.IsLTL) (hψ : ψ.IsLTL) :
    ⇓LTL[Model.ofωSequence t v,n ⊨ φ.until ψ] ↔
      ∃ k, n ≤ k ∧ ⇓LTL[Model.ofωSequence t v,k ⊨ ψ] ∧
        ∀ j, n ≤ j → j < k → ⇓LTL[Model.ofωSequence t v,j ⊨ φ] :=
  Satisfies.until_iff_of_isLTL t v n 0 hφ hψ

/-- Eventually holds at some position at or after the current one. -/
theorem Satisfies.at_eventually_iff
    (t : ωSequence State) (v : State → Atom → Prop)
    (n : ℕ) {φ : Proposition Atom} (hφ : φ.IsLTL) :
    ⇓LTL[Model.ofωSequence t v,n ⊨ φ.eventually] ↔
      ∃ k, n ≤ k ∧ ⇓LTL[Model.ofωSequence t v,k ⊨ φ] :=
  Satisfies.eventually_iff_of_isLTL t v n 0 hφ

/-- Always holds at every position at or after the current one. -/
theorem Satisfies.at_always_iff
    (t : ωSequence State) (v : State → Atom → Prop)
    (n : ℕ) {φ : Proposition Atom} (hφ : φ.IsLTL) :
    ⇓LTL[Model.ofωSequence t v,n ⊨ φ.always] ↔
      ∀ k, n ≤ k → ⇓LTL[Model.ofωSequence t v,k ⊨ φ] :=
  Satisfies.always_iff_of_isLTL t v n 0 hφ

/-- Release requires its right operand unless its left operand held at an earlier position. -/
theorem Satisfies.at_release_iff
    (t : ωSequence State) (v : State → Atom → Prop)
    (n : ℕ) {φ ψ : Proposition Atom} (hφ : φ.IsLTL) (hψ : ψ.IsLTL) :
    ⇓LTL[Model.ofωSequence t v,n ⊨ φ.release ψ] ↔
      ∀ k, n ≤ k → ⇓LTL[Model.ofωSequence t v,k ⊨ ψ] ∨
        ∃ j, n ≤ j ∧ j < k ∧ ⇓LTL[Model.ofωSequence t v,j ⊨ φ] :=
  Satisfies.release_iff_of_isLTL t v n 0 hφ hψ

/-- Unfold strong until without exposing the auxiliary anchor. -/
theorem Satisfies.at_until_unfold
    (t : ωSequence State) (v : State → Atom → Prop)
    (n : ℕ) {φ ψ : Proposition Atom} (hφ : φ.IsLTL) (hψ : ψ.IsLTL) :
    ⇓LTL[Model.ofωSequence t v,n ⊨ φ.until ψ] ↔
      ⇓LTL[Model.ofωSequence t v,n ⊨ ψ ∨ (φ ∧ (φ.until ψ).next)] :=
  Satisfies.until_unfold t v n 0 hφ hψ

end Cslib.Logic.Modal.LTL
