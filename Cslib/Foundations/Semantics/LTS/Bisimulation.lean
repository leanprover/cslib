/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Foundations.Data.Relation
public import Cslib.Foundations.Semantics.LTS.HasTau
public import Cslib.Foundations.Semantics.LTS.Simulation
public import Cslib.Foundations.Semantics.LTS.TraceEq

@[expose] public section

/-! # Bisimulation and Bisimilarity

A bisimulation is a binary relation on the states of two `LTS`s, which establishes a tight semantic
correspondence. More specifically, if two states `s₁` and `s₂` are related by a bisimulation, then
`s₁` can mimic all transitions of `s₂` and vice versa. Furthermore, the derivatives reaches through
these transitions remain related by the bisimulation.

Bisimilarity is the largest bisimulation: given an `LTS`, it relates any two states that are related
by a bisimulation for that LTS.

Weak bisimulation (resp. bisimilarity) is the relaxed version of bisimulation (resp. bisimilarity)
whereby internal actions performed by processes can be ignored.

For an introduction to theory of bisimulation, we refer to [Sangiorgi2011].

## Main definitions

- `lts.IsBisimulation r`: the relation `r` is a bisimulation for the LTS `lts`.
- `Bisimilarity lts` is the binary relation on the states of `lts` that relates any two states
related by some bisimulation on `lts`.
- `lts.IsBisimulationUpTo r`: the relation `r` is a bisimulation up to bisimilarity (this is known
as one of the 'up to' techniques for bisimulation).

- `lts.IsWeakBisimulation r`: the relation `r` on the states of the LTS `lts` is a weak
bisimulation.
- `WeakBisimilarity lts` is the binary relation on the states of `lts` that relates any two states
related by some weak bisimulation on `lts`.
- `lts.IsSWBisimulation` is a more convenient definition for establishing weak bisimulations, which
we prove to be sound and complete.

## Notations

- `s₁ ~[lts] s₂`: the states `s₁` and `s₂` are bisimilar in the LTS `lts`.
- `s₁ ≈[lts] s₂`: the states `s₁` and `s₂` are weakly bisimilar in the LTS `lts`.

## Main statements

- `LTS.IsBisimulation.inv`: the inverse of a bisimulation is a bisimulation.
- `Bisimilarity.eqv`: bisimilarity is an equivalence relation (see `Equivalence`).
- `Bisimilarity.isBisimulation`: bisimilarity is itself a bisimulation.
- `Bisimilarity.largest_bisimulation`: bisimilarity is the largest bisimulation.
- `Bisimilarity.gfp`: the union of bisimilarity and any bisimulation is equal to bisimilarity.
- `LTS.IsBisimulationUpTo.isBisimulation`: any bisimulation up to bisimilarity is a bisimulation.
- `LTS.IsBisimulation.traceEq`: any bisimulation that relates two states implies that they are
trace equivalent (see `TraceEq`).
- `Bisimilarity.deterministic_bisim_eq_traceEq`: in a deterministic LTS, bisimilarity and trace
equivalence coincide.
- `Bisimilarity.symm_simulation`: bisimilarity can be characterized through symmetric simulations.
- `WeakBisimilarity.weakBisim_eq_swBisim`: weak bisimulation and sw-bisimulation coincide.
- `WeakBisimilarity.eqv`: weak bisimilarity is an equivalence relation.

-/

namespace Cslib.LTS

section Bisimulation

/-- A relation is a bisimulation if, whenever it relates two states,
the transitions originating from these states mimic each other and the reached
derivatives are themselves related. -/
@[scoped grind =]
def IsBisimulation (lts₁ : LTS State₁ Label) (lts₂ : LTS State₂ Label)
    (r : State₁ → State₂ → Prop) : Prop :=
  ∀ ⦃s₁ s₂⦄, r s₁ s₂ → ∀ μ, (
    (∀ s₁', lts₁.Tr s₁ μ s₁' → ∃ s₂', lts₂.Tr s₂ μ s₂' ∧ r s₁' s₂')
    ∧
    (∀ s₂', lts₂.Tr s₂ μ s₂' → ∃ s₁', lts₁.Tr s₁ μ s₁' ∧ r s₁' s₂')
  )

/-- A homogeneous bisimulation is a bisimulation where the underlying LTSs are the same. -/
abbrev IsHomBisimulation (lts : LTS State Label) := IsBisimulation lts lts

/-- Helper for following a transition by the first state in a pair of a `Bisimulation`. -/
theorem IsBisimulation.follow_fst
    (hb : IsBisimulation lts₁ lts₂ r) (hr : r s₁ s₂) (htr : lts₁.Tr s₁ μ s₁') :
    ∃ s₂', lts₂.Tr s₂ μ s₂' ∧ r s₁' s₂' :=
  (hb hr μ).1 _ htr

/-- Helper for following a transition by the second state in a pair of a `Bisimulation`. -/
theorem IsBisimulation.follow_snd
    (hb : IsBisimulation lts₁ lts₂ r) (hr : r s₁ s₂) (htr : lts₂.Tr s₂ μ s₂') :
    ∃ s₁', lts₁.Tr s₁ μ s₁' ∧ r s₁' s₂' :=
  (hb hr μ).2 _ htr

/-- Two states are bisimilar if they are related by some bisimulation. -/
@[scoped grind =]
def Bisimilarity (lts₁ : LTS State₁ Label) (lts₂ : LTS State₂ Label) : State₁ → State₂ → Prop :=
  fun s₁ s₂ => ∃ r : State₁ → State₂ → Prop, r s₁ s₂ ∧ IsBisimulation lts₁ lts₂ r

/--
Notation for bisimilarity.

Differently from standard pen-and-paper presentations, we require the LTSs to be mentioned
explicitly.
-/
scoped notation s:max " ~[" lts₁ "," lts₂ "] " s':max => Bisimilarity lts₁ lts₂ s s'

/-- Homogeneous bisimilarity is bisimilarity where the underlying LTSs are the same. -/
abbrev HomBisimilarity (lts : LTS State Label) := Bisimilarity lts lts

/-- Notation for homogeneous bisimilarity. -/
scoped notation s:max " ~[" lts "] " s':max => HomBisimilarity lts s s'

/-- Homogeneous bisimilarity is reflexive. -/
@[scoped grind ., refl]
theorem HomBisimilarity.refl (s : State) : s ~[lts] s := by
  exists Eq
  grind

/-- The inverse of a bisimulation is a bisimulation. -/
@[scoped grind →]
theorem IsBisimulation.inv (h : IsBisimulation lts₁ lts₂ r) :
  IsBisimulation lts₂ lts₁ (flip r) := by grind [flip]

open scoped IsBisimulation in
/-- Bisimilarity is symmetric. -/
@[scoped grind →, symm]
theorem Bisimilarity.symm {s₁ s₂ : State} (h : s₁ ~[lts₁,lts₂] s₂) : s₂ ~[lts₂,lts₁] s₁ := by
  grind [flip]

/-- The composition of two bisimulations is a bisimulation. -/
@[scoped grind .]
theorem IsBisimulation.comp
    (h1 : IsBisimulation lts₁ lts₂ r1) (h2 : IsBisimulation lts₂ lts₃ r2) :
  IsBisimulation lts₁ lts₃ (Relation.Comp r1 r2) := by grind [Relation.Comp]

/-- Bisimilarity is transitive. -/
@[scoped grind →]
theorem Bisimilarity.trans
    (h1 : s₁ ~[lts₁,lts₂] s₂) (h2 : s₂ ~[lts₂,lts₃] s₃) :
  s₁ ~[lts₁,lts₃] s₃ := by
  obtain ⟨r1, _, _⟩ := h1
  obtain ⟨r2, _, _⟩ := h2
  exists Relation.Comp r1 r2
  grind [Relation.Comp]

/-- Homogeneous bisimilarity is an equivalence relation. -/
theorem HomBisimilarity.eqv :
  Equivalence (HomBisimilarity lts) := {
    refl := HomBisimilarity.refl
    symm := Bisimilarity.symm
    trans := Bisimilarity.trans
  }

instance : IsEquiv State (HomBisimilarity lts) where
  refl := HomBisimilarity.refl
  symm _ _ := Bisimilarity.symm
  trans _ _ _ := Bisimilarity.trans

/-- The union of two bisimulations is a bisimulation. -/
@[scoped grind .]
theorem IsBisimulation.sup (hrb : IsBisimulation lts₁ lts₂ r) (hsb : IsBisimulation lts₁ lts₂ s) :
  IsBisimulation lts₁ lts₂ (r ⊔ s) := by
  intro s₁ s₂ hrs μ
  cases hrs
  case inl h =>
    constructor
    · intro s₁' htr
      obtain ⟨s₂', htr', hr'⟩ := hrb.follow_fst h htr
      exists s₂'
      constructor
      · assumption
      · simp only [max, SemilatticeSup.sup]
        left
        exact hr'
    · intro s₂' htr
      obtain ⟨s₁', htr', hr'⟩ := hrb.follow_snd h htr
      exists s₁'
      constructor
      · assumption
      · simp only [max, SemilatticeSup.sup]
        left
        exact hr'
  case inr h =>
    constructor
    · intro s₁' htr
      obtain ⟨s₂', htr', hs'⟩ := hsb.follow_fst h htr
      exists s₂'
      constructor
      · assumption
      · simp only [max, SemilatticeSup.sup]
        right
        exact hs'
    · intro s₂' htr
      obtain ⟨s₁', htr', hs'⟩ := hsb.follow_snd h htr
      exists s₁'
      constructor
      · assumption
      · simp only [max, SemilatticeSup.sup]
        right
        exact hs'

/-- Bisimilarity is a bisimulation. -/
@[scoped grind .]
theorem Bisimilarity.is_bisimulation : IsBisimulation lts₁ lts₂ (Bisimilarity lts₁ lts₂) := by grind

/-- Bisimilarity is the largest bisimulation. -/
@[scoped grind →]
theorem Bisimilarity.largest_bisimulation (h : IsBisimulation lts₁ lts₂ r) :
  Subrelation r (Bisimilarity lts₁ lts₂) := by
  intro s₁ s₂ hr
  exists r

/-- The union of bisimilarity with any bisimulation is bisimilarity. -/
@[scoped grind =, simp]
theorem Bisimilarity.gfp (r : State₁ → State₂ → Prop) (h : IsBisimulation lts₁ lts₂ r) :
    (Bisimilarity lts₁ lts₂) ⊔ r = Bisimilarity lts₁ lts₂ := by
  funext s₁ s₂
  simp only [max, SemilatticeSup.sup]
  grind

/-- `calc` support for bisimilarity. -/
instance : Trans (Bisimilarity lts₁ lts₂) (Bisimilarity lts₂ lts₃) (Bisimilarity lts₁ lts₃) where
  trans := Bisimilarity.trans

section Order

/-! ## Order properties -/

instance : Max {r // IsBisimulation lts₁ lts₂ r} where
  max r s := ⟨r.1 ⊔ s.1, IsBisimulation.sup r.2 s.2⟩

/-- Bisimulations equipped with union form a join-semilattice. -/
instance : SemilatticeSup {r // IsBisimulation lts₁ lts₂ r} where
  sup r s := r ⊔ s
  le_sup_left r s := by
    simp only [LE.le]
    intro s₁ s₂ hr
    simp only [max, SemilatticeSup.sup]
    left
    exact hr
  le_sup_right r s := by
    simp only [LE.le]
    intro s₁ s₂ hs
    simp only [max, SemilatticeSup.sup]
    right
    exact hs
  sup_le r s t := by
    intro h1 h2
    simp only [LE.le, max, SemilatticeSup.sup]
    intro s₁ s₂ h
    cases h
    case inl h =>
      apply h1 _ _ h
    case inr h =>
      apply h2 _ _ h

/-- The empty (heterogeneous) relation is a bisimulation. -/
@[scoped grind .]
theorem IsBisimulation.bot : IsBisimulation lts₁ lts₂ Relation.emptyHRelation := by
  intro s₁ s₂ hr
  cases hr

instance : Bot {r // IsBisimulation lts₁ lts₂ r} :=
  ⟨Relation.emptyHRelation, IsBisimulation.bot⟩

instance : Top {r // IsBisimulation lts₁ lts₂ r} :=
  ⟨Bisimilarity lts₁ lts₂, Bisimilarity.is_bisimulation⟩

/-- In the inclusion order on bisimulations:

- The empty relation is the bottom element.
- Bisimilarity is the top element.
-/
instance : BoundedOrder {r // IsBisimulation lts₁ lts₂ r} where
  top := ⊤
  bot := ⊥
  le_top r := by
    intro s₁ s₂
    simp only [LE.le, Top.top]
    grind
  bot_le r := by
    intro s₁ s₂
    simp only [LE.le]
    intro hr
    cases hr

end Order

/-! ## Bisimulation up-to -/

/-- Lifts a relation `r` to homogeneous bisimilarities on its types. -/
def UpToHomBisimilarity (lts₁ : LTS State₁ Label) (lts₂ : LTS State₂ Label)
    (r : State₁ → State₂ → Prop) : State₁ → State₂ → Prop :=
  Relation.Comp (HomBisimilarity lts₁) (Relation.Comp r (HomBisimilarity lts₂))

/-- A relation `r` is a bisimulation up to homogeneous bisimilarity if, whenever it relates two
states in an lts, the transitions originating from these states mimic each other and the reached
derivatives are themselves related by `r` up to bisimilarity. -/
@[scoped grind]
def IsBisimulationUpTo (lts₁ : LTS State₁ Label) (lts₂ : LTS State₂ Label)
    (r : State₁ → State₂ → Prop) : Prop :=
  ∀ ⦃s₁ s₂⦄, r s₁ s₂ → ∀ μ, (
    (∀ s₁', lts₁.Tr s₁ μ s₁' → ∃ s₂', lts₂.Tr s₂ μ s₂' ∧
      (UpToHomBisimilarity lts₁ lts₂ r) s₁' s₂')
    ∧
    (∀ s₂', lts₂.Tr s₂ μ s₂' → ∃ s₁', lts₁.Tr s₁ μ s₁' ∧
      (UpToHomBisimilarity lts₁ lts₂ r) s₁' s₂')
  )

/-- Any bisimulation up to bisimilarity is a bisimulation. -/
@[scoped grind →]
theorem IsBisimulationUpTo.is_bisimulation (h : IsBisimulationUpTo lts₁ lts₂ r) :
  IsBisimulation lts₁ lts₂ (UpToHomBisimilarity lts₁ lts₂ r) := by
  intro s₁ s₂ hr μ
  rcases hr with ⟨s₁b, hr1b, s₂b, hrb, hr2b⟩
  obtain ⟨r1, hr1, hr1b⟩ := hr1b
  obtain ⟨r2, hr2, hr2b⟩ := hr2b
  constructor
  case left =>
    intro s₁' htr1
    obtain ⟨s₁b', hs₁b'tr, hs₁b'r⟩ := (hr1b hr1 μ).1 s₁' htr1
    obtain ⟨s₂b', hs₂b'tr, hs₂b'r⟩ := (h hrb μ).1 s₁b' hs₁b'tr
    obtain ⟨s₂', hs₂btr, hs₂br⟩ := (hr2b hr2 μ).1 _ hs₂b'tr
    exists s₂'
    constructor
    case left =>
      exact hs₂btr
    case right =>
      obtain ⟨smid1, hsmidb, smid2, hsmidr, hsmidrb⟩ := hs₂b'r
      constructor
      constructor
      · apply Bisimilarity.trans (Bisimilarity.largest_bisimulation hr1b hs₁b'r)
          hsmidb
      · exists smid2
        constructor
        · exact hsmidr
        · apply Bisimilarity.trans hsmidrb
          apply Bisimilarity.largest_bisimulation hr2b hs₂br
  case right =>
    intro s₂' htr2
    obtain ⟨s₂b', hs₂b'tr, hs₂b'r⟩ := (hr2b hr2 μ).2 s₂' htr2
    obtain ⟨s₁b', hs₁b'tr, hs₁b'r⟩ := (h hrb μ).2 s₂b' hs₂b'tr
    obtain ⟨s₁', hs₁btr, hs₁br⟩ := (hr1b hr1 μ).2 _ hs₁b'tr
    exists s₁'
    constructor
    case left =>
      exact hs₁btr
    case right =>
      obtain ⟨smid1, hsmidb, smid2, hsmidr, hsmidrb⟩ := hs₁b'r
      constructor
      constructor
      · apply Bisimilarity.trans (Bisimilarity.largest_bisimulation hr1b _) hsmidb
        · exact hs₁br
      · exists smid2
        constructor
        · exact hsmidr
        · apply Bisimilarity.trans hsmidrb
          apply Bisimilarity.largest_bisimulation hr2b _
          exact hs₂b'r

/-- If two states are related by a bisimulation, they can mimic each other's multi-step
transitions. -/
theorem IsBisimulation.bisim_trace
    (hb : IsBisimulation lts₁ lts₂ r) (hr : r s₁ s₂) :
    ∀ μs s₁', lts₁.MTr s₁ μs s₁' → ∃ s₂', lts₂.MTr s₂ μs s₂' ∧ r s₁' s₂' := by
  intro μs
  induction μs generalizing s₁ s₂
  case nil =>
    intro s₁' hmtr1
    exists s₂
    cases hmtr1
    constructor
    constructor
    exact hr
  case cons μ μs' ih =>
    intro s₁' hmtr1
    cases hmtr1
    case stepL s₁'' htr hmtr =>
      specialize hb hr μ
      have hf := hb.1 s₁'' htr
      obtain ⟨s₂'', htr2, hb2⟩ := hf
      specialize ih hb2 s₁' hmtr
      obtain ⟨s₂', hmtr2, hr'⟩ := ih
      exists s₂'
      constructor
      case left =>
        constructor
        · exact htr2
        · exact hmtr2
      case right =>
        exact hr'

/-! ## Relation to trace equivalence -/

/-- Any bisimulation implies trace equivalence. -/
@[scoped grind =>]
theorem IsBisimulation.traceEq
    (hb : IsBisimulation lts₁ lts₂ r) (hr : r s₁ s₂) :
    s₁ ~tr[lts₁,lts₂] s₂ := by
  funext μs
  simp only [eq_iff_iff]
  constructor
  case mp =>
    intro h
    obtain ⟨s₁', h⟩ := h
    obtain ⟨s₂', hmtr⟩ := IsBisimulation.bisim_trace hb hr μs s₁' h
    exists s₂'
    exact hmtr.1
  case mpr =>
    intro h
    obtain ⟨s₂', h⟩ := h
    obtain ⟨s₁', hmtr⟩ := IsBisimulation.bisim_trace hb.inv hr μs s₂' h
    exists s₁'
    exact hmtr.1

/-- Bisimilarity is included in trace equivalence. -/
@[scoped grind .]
theorem Bisimilarity.le_traceEq : Bisimilarity lts₁ lts₂ ≤ TraceEq lts₁ lts₂ := by
  intro s₁ s₂ h
  obtain ⟨r, hr, hb⟩ := h
  apply hb.traceEq hr

/- One of the standard motivating examples for bisimulation: `1` and `5` are trace equivalent, but
not bisimilar. -/
private inductive BisimMotTr : ℕ → Char → ℕ → Prop where
-- First process, `1`
| one2two : BisimMotTr 1 'a' 2
| two2three : BisimMotTr 2 'b' 3
| two2four : BisimMotTr 2 'c' 4
-- Second process, `5`
| five2six : BisimMotTr 5 'a' 6
| six2seven : BisimMotTr 6 'b' 7
| five2eight : BisimMotTr 5 'a' 8
| eight2nine : BisimMotTr 8 'c' 9

/-- In general, trace equivalence is not a bisimulation (extra conditions are needed, see for
example `Bisimulation.deterministic_trace_eq_is_bisim`). -/
theorem IsBisimulation.traceEq_not_bisim :
    ∃ (State : Type) (Label : Type) (lts : LTS State Label),
      ¬(IsHomBisimulation lts (HomTraceEq lts)) := by
  exists ℕ
  exists Char
  let lts := LTS.mk BisimMotTr
  exists lts
  intro h
  -- specialize h 1 5
  have htreq : (1 ~tr[lts] 5) := by
    simp [TraceEq]
    have htraces₁ : lts.traces 1 = {[], ['a'], ['a', 'b'], ['a', 'c']} := by
      apply Set.ext_iff.2
      intro μs
      apply Iff.intro
      case mp =>
        intro h1
        obtain ⟨s', htr⟩ := h1
        cases htr
        case refl =>
          simp
        case stepL μ sb μs' htr hmtr =>
          cases htr
          cases hmtr
          case one2two.stepL μ sb μs' htr hmtr =>
            cases htr <;> cases hmtr <;>
            simp only [↓Char.isValue, Set.mem_insert_iff, reduceCtorEq, List.cons.injEq,
              List.cons_ne_self, and_false, Set.mem_singleton_iff, Char.reduceEq, and_true,
              or_false, or_true] <;>
            contradiction
          simp
      case mpr =>
        intro h1
        cases h1
        case inl h1 =>
          simp only [h1]
          exists 1
          constructor
        case inr h1 =>
          cases h1
          case inl h1 =>
            simp only [h1]
            exists 2
            apply MTr.single; constructor
          case inr h1 =>
            cases h1
            case inl h1 =>
              simp only [h1]
              exists 3
              constructor
              · apply BisimMotTr.one2two
              · apply MTr.single
                apply BisimMotTr.two2three
            case inr h1 =>
              cases h1
              exists 4
              constructor
              · apply BisimMotTr.one2two
              · apply MTr.single
                apply BisimMotTr.two2four
    have htraces₂ : lts.traces 5 = {[], ['a'], ['a', 'b'], ['a', 'c']} := by
      apply Set.ext_iff.2
      intro μs
      apply Iff.intro
      case mp =>
        intro h1
        obtain ⟨s', htr⟩ := h1
        cases htr
        case refl =>
          simp
        case stepL μ sb μs' htr hmtr =>
          cases htr
          case five2six =>
            cases hmtr
            case refl =>
              simp
            case stepL μ sb μs' htr hmtr =>
              cases htr
              cases hmtr
              case refl => simp
              case stepL μ sb μs' htr hmtr =>
                cases htr
          case five2eight =>
            cases hmtr
            case refl =>
              simp
            case stepL μ sb μs' htr hmtr =>
              cases htr
              cases hmtr
              case refl => right; right; simp
              case stepL μ sb μs' htr hmtr =>
                cases htr
      case mpr =>
        intro h1
        cases h1
        case inl h1 =>
          simp only [h1]
          exists 5
          constructor
        case inr h1 =>
          cases h1
          case inl h1 =>
            simp only [h1]
            exists 6
            apply MTr.single; constructor
          case inr h1 =>
            cases h1
            case inl h1 =>
              simp only [h1]
              exists 7
              constructor
              · apply BisimMotTr.five2six
              · apply MTr.single
                apply BisimMotTr.six2seven
            case inr h1 =>
              cases h1
              exists 9
              constructor
              · apply BisimMotTr.five2eight
              · apply MTr.single;
                apply BisimMotTr.eight2nine
    simp [htraces₁, htraces₂]
  specialize h htreq
  specialize h 'a'
  obtain ⟨h1, h2⟩ := h
  specialize h1 2 (by constructor)
  obtain ⟨s₂', htr5, cih⟩ := h1
  cases htr5
  case five2six =>
    simp [TraceEq] at cih
    have htraces₂ : lts.traces 2 = {[], ['b'], ['c']} := by
      apply Set.ext_iff.2
      intro μs
      apply Iff.intro
      case mp =>
        intro h
        obtain ⟨s', htr⟩ := h
        cases htr
        case refl => simp
        case stepL μ sb μs' htr hmtr =>
          cases htr
          case two2three =>
            cases hmtr
            case stepL μ sb μs' htr hmtr => cases htr
            simp
          case two2four =>
            cases hmtr
            case refl => simp
            case stepL μ sb μs' htr hmtr =>
              cases htr
      case mpr =>
        intro h
        cases h
        case inl h =>
          exists 2
          simp [h]
          constructor
        case inr h =>
          cases h
          case inl h =>
            exists 3; simp [h]; constructor; constructor; constructor
          case inr h =>
            exists 4
            simp at h
            simp [h]
            constructor; constructor; constructor
    have htraces6 : lts.traces 6 = {[], ['b']} := by
      apply Set.ext_iff.2
      intro μs
      apply Iff.intro
      case mp =>
        intro h
        obtain ⟨s', htr⟩ := h
        cases htr
        case refl => simp
        case stepL μ sb μs' htr hmtr =>
          cases htr
          cases hmtr
          case stepL μ sb μs' htr hmtr => cases htr
          simp
      case mpr =>
        intro h
        cases h
        case inl h =>
          exists 6
          simp [h]
          constructor
        case inr h =>
          exists 7
          simp at h
          simp [h]
          constructor; constructor; constructor
    grind
  case five2eight =>
    simp only [TraceEq] at cih
    have htraces₂ : lts.traces 2 = {[], ['b'], ['c']} := by
      apply Set.ext_iff.2
      intro μs
      apply Iff.intro
      case mp =>
        intro h
        obtain ⟨s', htr⟩ := h
        cases htr
        case refl => simp
        case stepL μ sb μs' htr hmtr =>
          cases htr
          case two2three =>
            cases hmtr
            case stepL μ sb μs' htr hmtr => cases htr
            simp
          case two2four =>
            cases hmtr
            case refl => simp
            case stepL μ sb μs' htr hmtr =>
              cases htr
      case mpr =>
        intro h
        cases h
        case inl h =>
          exists 2
          simp [h]
          constructor
        case inr h =>
          cases h
          case inl h =>
            exists 3; simp [h]; constructor; constructor; constructor
          case inr h =>
            exists 4
            simp at h
            simp [h]
            constructor; constructor; constructor
    have htraces8 : lts.traces 8 = {[], ['c']} := by
      apply Set.ext_iff.2
      intro μs
      apply Iff.intro
      case mp =>
        intro h
        obtain ⟨s', htr⟩ := h
        cases htr
        case refl => simp
        case stepL μ sb μs' htr hmtr =>
          cases htr
          cases hmtr
          case stepL μ sb μs' htr hmtr => cases htr
          simp
      case mpr =>
        intro h
        cases h
        case inl h =>
          exists 8
          simp [h]
          constructor
        case inr h =>
          exists 9
          simp at h
          simp [h]
          repeat constructor
    rw [htraces₂, htraces8] at cih
    apply Set.ext_iff.1 at cih
    specialize cih ['b']
    obtain ⟨cih1, cih2⟩ := cih
    have cih1h : ['b'] ∈ @insert
      (List Char) (Set (List Char)) Set.instInsert [] {['b'], ['c']} := by
      simp
    specialize cih1 cih1h
    simp at cih1

/-- In general, bisimilarity and trace equivalence are distinct. -/
theorem Bisimilarity.bisimilarity_neq_traceEq :
    ∃ (State : Type) (Label : Type) (lts : LTS State Label),
      HomBisimilarity lts ≠ HomTraceEq lts := by
  obtain ⟨State, Label, lts, h⟩ := IsBisimulation.traceEq_not_bisim
  exists State; exists Label; exists lts
  intro heq
  have hb := Bisimilarity.is_bisimulation (lts₁ := lts) (lts₂ := lts)
  simp only [HomBisimilarity] at heq
  rw [heq] at hb
  contradiction

/-- In any deterministic LTS, trace equivalence is a bisimulation. -/
theorem IsBisimulation.deterministic_traceEq_isBisimulation
    {lts₁ : LTS State₁ Label} {lts₂ : LTS State₂ Label}
    [lts₁.Deterministic] [lts₂.Deterministic] :
    (IsBisimulation lts₁ lts₂ (TraceEq lts₁ lts₂)) := by
  simp only [IsBisimulation]
  intro s₁ s₂ hteq μ
  constructor
  case left =>
    apply TraceEq.deterministic_isSimulation s₁ s₂ hteq
  case right =>
    intro s₂' htr
    apply TraceEq.symm at hteq
    have h := TraceEq.deterministic_isSimulation s₂ s₁ hteq μ s₂' htr
    obtain ⟨s₁', h⟩ := h
    exists s₁'
    constructor
    case left =>
      exact h.1
    case right =>
      apply h.2.symm

/-- In deterministic LTSs, trace equivalence implies bisimilarity. -/
theorem Bisimilarity.deterministic_traceEq_bisim {lts₁ : LTS State₁ Label} {lts₂ : LTS State₂ Label}
    [lts₁.Deterministic] [lts₂.Deterministic] (h : s₁ ~tr[lts₁,lts₂] s₂) :
    (s₁ ~[lts₁,lts₂] s₂) := by
  exists TraceEq lts₁ lts₂
  constructor
  case left =>
    exact h
  case right =>
    apply IsBisimulation.deterministic_traceEq_isBisimulation

/-- In deterministic LTSs, bisimilarity and trace equivalence coincide. -/
theorem Bisimilarity.deterministic_bisim_eq_traceEq
    {lts₁ : LTS State₁ Label} {lts₂ : LTS State₂ Label}
    [lts₁.Deterministic] [lts₂.Deterministic] : Bisimilarity lts₁ lts₂ = TraceEq lts₁ lts₂ := by
  funext s₁ s₂
  simp only [eq_iff_iff]
  constructor
  case mp =>
    apply Bisimilarity.le_traceEq
  case mpr =>
    apply Bisimilarity.deterministic_traceEq_bisim

/-! ## Relation to simulation -/

/-- Any bisimulation is also a simulation. -/
theorem IsBisimulation.isSimulation : IsBisimulation lts₁ lts₂ r → IsSimulation lts₁ lts₂ r := by
  grind [IsSimulation]

/-- A relation is a bisimulation iff both it and its inverse are simulations. -/
theorem IsBisimulation.isSimulation_iff :
    IsBisimulation lts₁ lts₂ r ↔ (IsSimulation lts₁ lts₂ r ∧ IsSimulation lts₂ lts₁ (flip r)) := by
  have _ (s₁ s₂) : r s₁ s₂ → flip r s₂ s₁ := id
  grind [IsSimulation, flip]

/-- Homogeneous bisimilarity can also be characterized through symmetric simulations. -/
theorem HomBisimilarity.symm_simulation :
  HomBisimilarity lts =
    fun s₁ s₂ => ∃ r, r s₁ s₂ ∧ Std.Symm r ∧ IsHomSimulation lts r := by
  funext s₁ s₂
  apply Iff.eq
  apply Iff.intro
  · intro h
    have bisim : HomBisimilarity lts s₁ s₂ ∧ Std.Symm (HomBisimilarity lts)
        ∧ IsHomSimulation lts (HomBisimilarity lts) := by
      grind [Std.Symm, Bisimilarity.symm, IsBisimulation.isSimulation]
    grind
  · intro ⟨r, hr, hsymm, hsim⟩
    have : r = (flip r) := by
      grind [flip, Std.Symm]
    have : IsHomBisimulation lts r := by
      grind [IsBisimulation.isSimulation_iff]
    grind

end Bisimulation

section WeakBisimulation

/-! ## Weak bisimulation and weak bisimilarity -/

/-- A weak bisimulation is similar to a `Bisimulation`, but allows for the related processes to do
internal work. Technically, this is defined as a `Bisimulation` on the saturation of the LTSs. -/
def IsWeakBisimulation [HasTau Label] (lts₁ : LTS State₁ Label) (lts₂ : LTS State₂ Label)
    (r : State₁ → State₂ → Prop) :=
  IsBisimulation (lts₁.saturate) (lts₂.saturate) r

/-- A homogeneous bisimulation is a bisimulation where the underlying LTSs are the same. -/
abbrev IsHomWeakBisimulation [HasTau Label] (lts : LTS State Label) := IsWeakBisimulation lts lts

/-- Two states are weakly bisimilar if they are related by some weak bisimulation. -/
def WeakBisimilarity [HasTau Label] (lts₁ : LTS State₁ Label) (lts₂ : LTS State₂ Label) :
    State₁ → State₂ → Prop :=
  fun s₁ s₂ =>
    ∃ r : State₁ → State₂ → Prop, r s₁ s₂ ∧ IsWeakBisimulation lts₁ lts₂ r

/-- Notation for weak bisimilarity. -/
scoped notation s:max " ≈[" lts₁ "," lts₂ "] " s':max => WeakBisimilarity lts₁ lts₂ s s'

/-- Homogeneous bisimilarity is bisimilarity where the underlying LTSs are the same. -/
abbrev HomWeakBisimilarity [HasTau Label] (lts : LTS State Label) := WeakBisimilarity lts lts

/-- Notation for homogeneous bisimilarity. -/
scoped notation s:max " ≈[" lts "] " s':max => HomWeakBisimilarity lts s s'

/-- An `SWBisimulation` is a more convenient definition of weak bisimulation, because the challenge
is a single transition. We prove later that this technique is sound, following a strategy inspired
by [Sangiorgi2011]. -/
def IsSWBisimulation [HasTau Label] (lts₁ : LTS State₁ Label) (lts₂ : LTS State₂ Label)
    (r : State₁ → State₂ → Prop) : Prop :=
  ∀ ⦃s₁ s₂⦄, r s₁ s₂ → ∀ μ, (
    (∀ s₁', lts₁.Tr s₁ μ s₁' → ∃ s₂', lts₂.STr s₂ μ s₂' ∧ r s₁' s₂')
    ∧
    (∀ s₂', lts₂.Tr s₂ μ s₂' → ∃ s₁', lts₁.STr s₁ μ s₁' ∧ r s₁' s₂')
  )

/-- Utility theorem for 'following' internal transitions using an `SWBisimulation`
(first component). -/
theorem IsSWBisimulation.follow_internal_fst
    [HasTau Label] {lts₁ : LTS State₁ Label} {lts₂ : LTS State₂ Label}
    (hswb : IsSWBisimulation lts₁ lts₂ r) (hr : r s₁ s₂) (hstr : lts₁.τSTr s₁ s₁') :
    ∃ s₂', lts₂.τSTr s₂ s₂' ∧ r s₁' s₂' := by
  induction hstr
  case refl =>
    exists s₂
    constructor; constructor
    exact hr
  case tail sb hrsb htrsb ih1 ih2 =>
    obtain ⟨sb2, htrsb2, hrb⟩ := ih2
    have h := (hswb hrb HasTau.τ).left _ ih1
    obtain ⟨sb2', htrsb2', hrb'⟩ := h
    exists sb2'
    constructor
    · simp only [sTr_τSTr] at htrsb htrsb2'
      exact Relation.ReflTransGen.trans htrsb2 htrsb2'
    · exact hrb'

/-- Utility theorem for 'following' internal transitions using an `SWBisimulation`
(second component). -/
theorem IsSWBisimulation.follow_internal_snd
    [HasTau Label] {lts₁ : LTS State₁ Label} {lts₂ : LTS State₂ Label}
    (hswb : IsSWBisimulation lts₁ lts₂ r) (hr : r s₁ s₂) (hstr : lts₂.τSTr s₂ s₂') :
    ∃ s₁', lts₁.τSTr s₁ s₁' ∧ r s₁' s₂' := by
  induction hstr
  case refl =>
    exists s₁
    constructor; constructor
    exact hr
  case tail sb hrsb htrsb ih1 ih2 =>
    obtain ⟨sb2, htrsb2, hrb⟩ := ih2
    have h := (hswb hrb HasTau.τ).right _ ih1
    obtain ⟨sb2', htrsb2', hrb'⟩ := h
    exists sb2'
    constructor
    · simp only [sTr_τSTr] at htrsb htrsb2'
      exact Relation.ReflTransGen.trans htrsb2 htrsb2'
    · exact hrb'

/-- We can now prove that any relation is a `WeakBisimulation` iff it is an `SWBisimulation`.
This formalises lemma 4.2.10 in [Sangiorgi2011]. -/
theorem isWeakBisimulation_iff_isSWBisimulation
    [HasTau Label] {lts₁ : LTS State₁ Label} {lts₂ : LTS State₂ Label} :
    IsWeakBisimulation lts₁ lts₂ r ↔ IsSWBisimulation lts₁ lts₂ r := by
  apply Iff.intro
  case mp =>
    intro h s₁ s₂ hr μ
    apply And.intro
    case left =>
      intro s₁' htr
      specialize h hr μ
      have h' := h.1 s₁' (STr.single lts₁ htr)
      obtain ⟨s₂', htr2, hr2⟩ := h'
      exists s₂'
    case right =>
      intro s₂' htr
      specialize h hr μ
      have h' := h.2 s₂' (STr.single lts₂ htr)
      obtain ⟨s₁', htr1, hr1⟩ := h'
      exists s₁'
  case mpr =>
    intro h s₁ s₂ hr μ
    apply And.intro
    case left =>
      intro s₁' hstr
      cases hstr
      case refl =>
        exists s₂
        constructor; constructor
        exact hr
      case tr sb sb' hstr1 htr hstr2 =>
        rw [←sTr_τSTr] at hstr1 hstr2
        simp only [sTr_τSTr] at hstr1 hstr2
        obtain ⟨sb1, hstr1b, hrb⟩ := IsSWBisimulation.follow_internal_fst h hr hstr1
        obtain ⟨sb2', hstr1b', hrb'⟩ := (h hrb μ).left _ htr
        obtain ⟨s₁', hstr1', hrb2⟩ := IsSWBisimulation.follow_internal_fst h hrb' hstr2
        rw [←sTr_τSTr] at hstr1' hstr1b
        exists s₁'
        constructor
        · exact STr.comp lts₂ hstr1b hstr1b' hstr1'
        · exact hrb2
    case right =>
      intro s₂' hstr
      cases hstr
      case refl =>
        exists s₁
        constructor; constructor
        exact hr
      case tr sb sb' hstr1 htr hstr2 =>
        rw [←sTr_τSTr] at hstr1 hstr2
        simp only [sTr_τSTr] at hstr1 hstr2
        obtain ⟨sb1, hstr1b, hrb⟩ := IsSWBisimulation.follow_internal_snd h hr hstr1
        obtain ⟨sb2', hstr1b', hrb'⟩ := (h hrb μ).right _ htr
        obtain ⟨s₁', hstr1', hrb2⟩ := IsSWBisimulation.follow_internal_snd h hrb' hstr2
        rw [←sTr_τSTr] at hstr1' hstr1b
        exists s₁'
        constructor
        · exact STr.comp lts₁ hstr1b hstr1b' hstr1'
        · exact hrb2

theorem IsWeakBisimulation.isSwBisimulation
    [HasTau Label] {lts₁ : LTS State₁ Label} {lts₂ : LTS State₂ Label} {r : State₁ → State₂ → Prop}
    (h : IsWeakBisimulation lts₁ lts₂ r) :
  IsSWBisimulation lts₁ lts₂ r := isWeakBisimulation_iff_isSWBisimulation.1 h

theorem IsSWBisimulation.isWeakBisimulation
    [HasTau Label] {lts₁ : LTS State₁ Label} {lts₂ : LTS State₂ Label} {r : State₁ → State₂ → Prop}
    (h : IsSWBisimulation lts₁ lts₂ r) :
  IsWeakBisimulation lts₁ lts₂ r := isWeakBisimulation_iff_isSWBisimulation.2 h

/-- Weak bisimilarity can also be characterized through sw-bisimulations. -/
@[scoped grind =]
theorem WeakBisimilarity.weakBisim_eq_swBisim [HasTau Label]
    (lts₁ : LTS State₁ Label) (lts₂ : LTS State₂ Label) :
    WeakBisimilarity lts₁ lts₂ =
      fun s₁ s₂ => ∃ r : State₁ → State₂ → Prop, r s₁ s₂ ∧ IsSWBisimulation lts₁ lts₂ r := by
  grind [WeakBisimilarity, isWeakBisimulation_iff_isSWBisimulation.1,
    isWeakBisimulation_iff_isSWBisimulation.2]

/-- Homogeneous weak bisimilarity is reflexive. -/
theorem HomWeakBisimilarity.refl [HasTau Label] {lts : LTS State Label} (s : State) :
    s ≈[lts] s := by
  simp only [HomWeakBisimilarity]
  rw [WeakBisimilarity.weakBisim_eq_swBisim lts lts]
  exists Eq
  grind [IsSWBisimulation, STr.single]

/-- The inverse of a weak bisimulation is a weak bisimulation. -/
theorem IsWeakBisimulation.inv [HasTau Label]
    {lts₁ : LTS State₁ Label} {lts₂ : LTS State₂ Label}
    (r : State₁ → State₂ → Prop) (h : IsWeakBisimulation lts₁ lts₂ r) :
    IsWeakBisimulation lts₂ lts₁ (flip r) := by
  grind [IsWeakBisimulation.isSwBisimulation, IsSWBisimulation,
    flip, IsSWBisimulation.isWeakBisimulation]

/-- Weak bisimilarity is symmetric. -/
theorem WeakBisimilarity.symm [HasTau Label] {lts₁ : LTS State₁ Label} {lts₂ : LTS State₂ Label}
    (h : s₁ ≈[lts₁,lts₂] s₂) : s₂ ≈[lts₂,lts₁] s₁ := by
  obtain ⟨r, hr, hrh⟩ := h
  exists (flip r)
  grind [IsWeakBisimulation.inv, flip]

/-- The composition of two weak bisimulations is a weak bisimulation. -/
theorem IsWeakBisimulation.comp
    [HasTau Label] {lts₁ : LTS State₁ Label} {lts₂ : LTS State₂ Label} {lts₃ : LTS State₃ Label}
    (h1 : IsWeakBisimulation lts₁ lts₂ r1) (h2 : IsWeakBisimulation lts₂ lts₃ r2) :
    IsWeakBisimulation lts₁ lts₃ (Relation.Comp r1 r2) := by
  simp_all only [IsWeakBisimulation]
  exact h1.comp h2

/-- The composition of two sw-bisimulations is an sw-bisimulation. -/
theorem IsSWBisimulation.comp
    [HasTau Label] {lts₁ : LTS State₁ Label} {lts₂ : LTS State₂ Label} {lts₃ : LTS State₃ Label}
    (h1 : IsSWBisimulation lts₁ lts₂ r1) (h2 : IsSWBisimulation lts₂ lts₃ r2) :
    IsSWBisimulation lts₁ lts₃ (Relation.Comp r1 r2) := by
  simp_all only [isWeakBisimulation_iff_isSWBisimulation.symm]
  apply IsWeakBisimulation.comp h1 h2

/-- Weak bisimilarity is transitive. -/
theorem WeakBisimilarity.trans [HasTau Label]
    {lts₁ : LTS State₁ Label} {lts₂ : LTS State₂ Label} {lts₃ : LTS State₃ Label}
    (h1 : s₁ ≈[lts₁,lts₂] s₂) (h2 : s₂ ≈[lts₂,lts₃] s₃) : s₁ ≈[lts₁,lts₃] s₃ := by
  obtain ⟨r1, hr1, hr1b⟩ := h1
  obtain ⟨r2, hr2, hr2b⟩ := h2
  exists Relation.Comp r1 r2
  constructor
  case left =>
    exists s₂
  case right =>
    apply IsWeakBisimulation.comp hr1b hr2b

/-- Homogeneous weak bisimilarity is an equivalence relation. -/
theorem HomWeakBisimilarity.eqv [HasTau Label] {lts : LTS State Label} :
    Equivalence (HomWeakBisimilarity lts) where
  refl := HomWeakBisimilarity.refl
  symm := WeakBisimilarity.symm
  trans := WeakBisimilarity.trans

end WeakBisimulation

end Cslib.LTS
