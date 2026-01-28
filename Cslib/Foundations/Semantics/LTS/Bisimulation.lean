/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Foundations.Data.Relation
public import Cslib.Foundations.Semantics.LTS.Simulation
public import Cslib.Foundations.Semantics.LTS.TraceEq

@[expose] public section

/-! # Bisimulation and Bisimilarity

A bisimulation is a binary relation on the states of an `LTS`, which establishes a tight semantic
correspondence. More specifically, if two states `s1` and `s2` are related by a bisimulation, then
`s1` can mimic all transitions of `s2` and vice versa. Furthermore, the derivatives reaches through
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

- `s1 ~[lts] s2`: the states `s1` and `s2` are bisimilar in the LTS `lts`.
- `s1 ≈[lts] s2`: the states `s1` and `s2` are weakly bisimilar in the LTS `lts`.

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

namespace Cslib

universe u v

section Bisimulation

variable {State : Type u} {Label : Type v} {lts : LTS State Label}

/-- A relation is a bisimulation if, whenever it relates two states in an lts,
the transitions originating from these states mimic each other and the reached
derivatives are themselves related. -/
@[scoped grind =]
def LTS.IsBisimulation (lts : LTS State Label) (r : State → State → Prop) : Prop :=
  ∀ ⦃s1 s2⦄, r s1 s2 → ∀ μ, (
    (∀ s1', lts.Tr s1 μ s1' → ∃ s2', lts.Tr s2 μ s2' ∧ r s1' s2')
    ∧
    (∀ s2', lts.Tr s2 μ s2' → ∃ s1', lts.Tr s1 μ s1' ∧ r s1' s2')
  )

/-- Helper for following a transition by the first state in a pair of a `Bisimulation`. -/
theorem LTS.IsBisimulation.follow_fst
  (hb : lts.IsBisimulation r) (hr : r s1 s2) (htr : lts.Tr s1 μ s1') :
  ∃ s2', lts.Tr s2 μ s2' ∧ r s1' s2' :=
  (hb hr μ).1 _ htr

/-- Helper for following a transition by the second state in a pair of a `Bisimulation`. -/
theorem LTS.IsBisimulation.follow_snd
  (hb : lts.IsBisimulation r) (hr : r s1 s2) (htr : lts.Tr s2 μ s2') :
  ∃ s1', lts.Tr s1 μ s1' ∧ r s1' s2' :=
  (hb hr μ).2 _ htr

/-- Two states are bisimilar if they are related by some bisimulation. -/
@[scoped grind =]
def Bisimilarity (lts : LTS State Label) : State → State → Prop :=
  fun s1 s2 => ∃ r : State → State → Prop, r s1 s2 ∧ lts.IsBisimulation r

/--
Notation for bisimilarity.

Differently from standard pen-and-paper presentations, we require the lts to be mentioned
explicitly.
-/
notation s:max " ~[" lts "] " s':max => Bisimilarity lts s s'

open LTS in
/-- Bisimilarity is reflexive. -/
@[scoped grind ., refl]
theorem Bisimilarity.refl (s : State) : s ~[lts] s := by
  exists Eq
  grind

/-- The inverse of a bisimulation is a bisimulation. -/
@[scoped grind →]
theorem LTS.IsBisimulation.inv (h : lts.IsBisimulation r) :
  lts.IsBisimulation (flip r) := by grind [flip]

open scoped LTS.IsBisimulation in
/-- Bisimilarity is symmetric. -/
@[scoped grind →, symm]
theorem Bisimilarity.symm {s1 s2 : State} (h : s1 ~[lts] s2) : s2 ~[lts] s1 := by
  grind [flip]

/-- The composition of two bisimulations is a bisimulation. -/
@[scoped grind .]
theorem LTS.IsBisimulation.comp
  (h1 : lts.IsBisimulation r1) (h2 : lts.IsBisimulation r2) :
  lts.IsBisimulation (Relation.Comp r1 r2) := by grind [Relation.Comp]

open LTS in
/-- Bisimilarity is transitive. -/
@[scoped grind →]
theorem Bisimilarity.trans
  (h1 : s1 ~[lts] s2) (h2 : s2 ~[lts] s3) :
  s1 ~[lts] s3 := by
  obtain ⟨r1, _, _⟩ := h1
  obtain ⟨r2, _, _⟩ := h2
  exists Relation.Comp r1 r2
  grind [Relation.Comp]

/-- Bisimilarity is an equivalence relation. -/
theorem Bisimilarity.eqv :
  Equivalence (Bisimilarity lts) := {
    refl := Bisimilarity.refl
    symm := Bisimilarity.symm
    trans := Bisimilarity.trans
  }

instance : IsEquiv State (Bisimilarity lts) where
  refl := Bisimilarity.refl
  symm _ _ := Bisimilarity.symm
  trans _ _ _ := Bisimilarity.trans

/-- The union of two bisimulations is a bisimulation. -/
@[scoped grind .]
theorem Bisimulation.union (hrb : lts.IsBisimulation r) (hsb : lts.IsBisimulation s) :
  lts.IsBisimulation (r ⊔ s) := by
  intro s1 s2 hrs μ
  cases hrs
  case inl h =>
    constructor
    · intro s1' htr
      obtain ⟨s2', htr', hr'⟩ := hrb.follow_fst h htr
      exists s2'
      constructor
      · assumption
      · simp only [max, SemilatticeSup.sup]
        left
        exact hr'
    · intro s2' htr
      obtain ⟨s1', htr', hr'⟩ := hrb.follow_snd h htr
      exists s1'
      constructor
      · assumption
      · simp only [max, SemilatticeSup.sup]
        left
        exact hr'
  case inr h =>
    constructor
    · intro s1' htr
      obtain ⟨s2', htr', hs'⟩ := hsb.follow_fst h htr
      exists s2'
      constructor
      · assumption
      · simp only [max, SemilatticeSup.sup]
        right
        exact hs'
    · intro s2' htr
      obtain ⟨s1', htr', hs'⟩ := hsb.follow_snd h htr
      exists s1'
      constructor
      · assumption
      · simp only [max, SemilatticeSup.sup]
        right
        exact hs'

open LTS in
/-- Bisimilarity is a bisimulation. -/
@[scoped grind .]
theorem Bisimilarity.is_bisimulation : lts.IsBisimulation (Bisimilarity lts) := by grind

/-- Bisimilarity is the largest bisimulation. -/
@[scoped grind →]
theorem Bisimilarity.largest_bisimulation (h : lts.IsBisimulation r) :
  Subrelation r (Bisimilarity lts) := by
  intro s1 s2 hr
  exists r

/-- The union of bisimilarity with any bisimulation is bisimilarity. -/
@[scoped grind =, simp]
theorem Bisimilarity.gfp (r : State → State → Prop) (h : lts.IsBisimulation r) :
  (Bisimilarity lts) ⊔ r = Bisimilarity lts := by
  funext s1 s2
  simp only [max, SemilatticeSup.sup, eq_iff_iff, or_iff_left_iff_imp]
  apply Bisimilarity.largest_bisimulation h

/-- `calc` support for bisimilarity. -/
instance : Trans (Bisimilarity lts) (Bisimilarity lts) (Bisimilarity lts) where
  trans := Bisimilarity.trans

section Order

/-! ## Order properties -/

instance : Max {r // lts.IsBisimulation r} where
  max r s := ⟨r.1 ⊔ s.1, Bisimulation.union r.2 s.2⟩

/-- Bisimulations equipped with union form a join-semilattice. -/
instance : SemilatticeSup {r // lts.IsBisimulation r} where
  sup r s := r ⊔ s
  le_sup_left r s := by
    simp only [LE.le]
    intro s1 s2 hr
    simp only [max, SemilatticeSup.sup]
    left
    exact hr
  le_sup_right r s := by
    simp only [LE.le]
    intro s1 s2 hs
    simp only [max, SemilatticeSup.sup]
    right
    exact hs
  sup_le r s t := by
    intro h1 h2
    simp only [LE.le, max, SemilatticeSup.sup]
    intro s1 s2 h
    cases h
    case inl h =>
      apply h1 _ _ h
    case inr h =>
      apply h2 _ _ h

/-- The empty relation is a bisimulation. -/
@[scoped grind .]
theorem Bisimulation.emptyRelation_bisimulation : lts.IsBisimulation emptyRelation := by
  intro s1 s2 hr
  cases hr

/-- In the inclusion order on bisimulations:

- The empty relation is the bottom element.
- Bisimilarity is the top element.
-/
instance : BoundedOrder {r // lts.IsBisimulation r} where
  top := ⟨Bisimilarity lts, Bisimilarity.is_bisimulation⟩
  bot := ⟨emptyRelation, Bisimulation.emptyRelation_bisimulation⟩
  le_top r := by
    intro s1 s2
    simp only [LE.le]
    apply Bisimilarity.largest_bisimulation r.2
  bot_le r := by
    intro s1 s2
    simp only [LE.le]
    intro hr
    cases hr

end Order

/-! ## Bisimulation up-to -/

/-- A relation `r` is a bisimulation up to bisimilarity if, whenever it relates two
states in an lts, the transitions originating from these states mimic each other and the reached
derivatives are themselves related by `r` up to bisimilarity. -/
@[scoped grind]
def LTS.IsBisimulationUpTo (lts : LTS State Label) (r : State → State → Prop) : Prop :=
  ∀ ⦃s1 s2⦄, r s1 s2 → ∀ μ, (
    (∀ s1', lts.Tr s1 μ s1' → ∃ s2', lts.Tr s2 μ s2' ∧ Relation.UpTo r (Bisimilarity lts) s1' s2')
    ∧
    (∀ s2', lts.Tr s2 μ s2' → ∃ s1', lts.Tr s1 μ s1' ∧ Relation.UpTo r (Bisimilarity lts) s1' s2')
  )

/-- Any bisimulation up to bisimilarity is a bisimulation. -/
@[scoped grind →]
theorem LTS.IsBisimulationUpTo.isBisimulation (h : lts.IsBisimulationUpTo r) :
  lts.IsBisimulation (Relation.UpTo r (Bisimilarity lts)) := by
  intro s1 s2 hr μ
  rcases hr with ⟨s1b, hr1b, s2b, hrb, hr2b⟩
  obtain ⟨r1, hr1, hr1b⟩ := hr1b
  obtain ⟨r2, hr2, hr2b⟩ := hr2b
  constructor
  case left =>
    intro s1' htr1
    obtain ⟨s1b', hs1b'tr, hs1b'r⟩ := (hr1b hr1 μ).1 s1' htr1
    obtain ⟨s2b', hs2b'tr, hs2b'r⟩ := (h hrb μ).1 s1b' hs1b'tr
    obtain ⟨s2', hs2btr, hs2br⟩ := (hr2b hr2 μ).1 _ hs2b'tr
    exists s2'
    constructor
    case left =>
      exact hs2btr
    case right =>
      obtain ⟨smid1, hsmidb, smid2, hsmidr, hsmidrb⟩ := hs2b'r
      constructor
      constructor
      · apply Bisimilarity.trans (Bisimilarity.largest_bisimulation hr1b hs1b'r)
          hsmidb
      · exists smid2
        constructor
        · exact hsmidr
        · apply Bisimilarity.trans hsmidrb
          apply Bisimilarity.largest_bisimulation hr2b hs2br
  case right =>
    intro s2' htr2
    obtain ⟨s2b', hs2b'tr, hs2b'r⟩ := (hr2b hr2 μ).2 s2' htr2
    obtain ⟨s1b', hs1b'tr, hs1b'r⟩ := (h hrb μ).2 s2b' hs2b'tr
    obtain ⟨s1', hs1btr, hs1br⟩ := (hr1b hr1 μ).2 _ hs1b'tr
    exists s1'
    constructor
    case left =>
      exact hs1btr
    case right =>
      obtain ⟨smid1, hsmidb, smid2, hsmidr, hsmidrb⟩ := hs1b'r
      constructor
      constructor
      · apply Bisimilarity.trans (Bisimilarity.largest_bisimulation hr1b _) hsmidb
        · exact hs1br
      · exists smid2
        constructor
        · exact hsmidr
        · apply Bisimilarity.trans hsmidrb
          apply Bisimilarity.largest_bisimulation hr2b _
          exact hs2b'r

/-- If two states are related by a bisimulation, they can mimic each other's multi-step
transitions. -/
theorem Bisimulation.bisim_trace
  (hb : lts.IsBisimulation r) (hr : r s1 s2) :
  ∀ μs s1', lts.MTr s1 μs s1' → ∃ s2', lts.MTr s2 μs s2' ∧ r s1' s2' := by
  intro μs
  induction μs generalizing s1 s2
  case nil =>
    intro s1' hmtr1
    exists s2
    cases hmtr1
    constructor
    constructor
    exact hr
  case cons μ μs' ih =>
    intro s1' hmtr1
    cases hmtr1
    case stepL s1'' htr hmtr =>
      specialize hb hr μ
      have hf := hb.1 s1'' htr
      obtain ⟨s2'', htr2, hb2⟩ := hf
      specialize ih hb2 s1' hmtr
      obtain ⟨s2', hmtr2, hr'⟩ := ih
      exists s2'
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
theorem LTS.IsBisimulation.traceEq
  (hb : lts.IsBisimulation r) (hr : r s1 s2) :
  s1 ~tr[lts] s2 := by
  funext μs
  simp only [eq_iff_iff]
  constructor
  case mp =>
    intro h
    obtain ⟨s1', h⟩ := h
    obtain ⟨s2', hmtr⟩ := Bisimulation.bisim_trace hb hr μs s1' h
    exists s2'
    exact hmtr.1
  case mpr =>
    intro h
    obtain ⟨s2', h⟩ := h
    obtain ⟨s1', hmtr⟩ := Bisimulation.bisim_trace hb.inv hr μs s2' h
    exists s1'
    exact hmtr.1

/-- Bisimilarity is included in trace equivalence. -/
@[scoped grind .]
theorem Bisimilarity.le_traceEq : Bisimilarity lts ≤ TraceEq lts := by
  intro s1 s2 h
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
theorem Bisimulation.traceEq_not_bisim :
  ∃ (State : Type) (Label : Type) (lts : LTS State Label), ¬(lts.IsBisimulation (TraceEq lts)) := by
  exists ℕ
  exists Char
  let lts := LTS.mk BisimMotTr
  exists lts
  intro h
  -- specialize h 1 5
  have htreq : (1 ~tr[lts] 5) := by
    simp [TraceEq]
    have htraces1 : lts.traces 1 = {[], ['a'], ['a', 'b'], ['a', 'c']} := by
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
            apply LTS.MTr.single; constructor
          case inr h1 =>
            cases h1
            case inl h1 =>
              simp only [h1]
              exists 3
              constructor
              · apply BisimMotTr.one2two
              · apply LTS.MTr.single
                apply BisimMotTr.two2three
            case inr h1 =>
              cases h1
              exists 4
              constructor
              · apply BisimMotTr.one2two
              · apply LTS.MTr.single
                apply BisimMotTr.two2four
    have htraces2 : lts.traces 5 = {[], ['a'], ['a', 'b'], ['a', 'c']} := by
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
            apply LTS.MTr.single; constructor
          case inr h1 =>
            cases h1
            case inl h1 =>
              simp only [h1]
              exists 7
              constructor
              · apply BisimMotTr.five2six
              · apply LTS.MTr.single
                apply BisimMotTr.six2seven
            case inr h1 =>
              cases h1
              exists 9
              constructor
              · apply BisimMotTr.five2eight
              · apply LTS.MTr.single;
                apply BisimMotTr.eight2nine
    simp [htraces1, htraces2]
  specialize h htreq
  specialize h 'a'
  obtain ⟨h1, h2⟩ := h
  specialize h1 2 (by constructor)
  obtain ⟨s2', htr5, cih⟩ := h1
  cases htr5
  case five2six =>
    simp [TraceEq] at cih
    have htraces2 : lts.traces 2 = {[], ['b'], ['c']} := by
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
    have htraces2 : lts.traces 2 = {[], ['b'], ['c']} := by
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
    rw [htraces2, htraces8] at cih
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
  ∃ (State : Type) (Label : Type) (lts : LTS State Label), Bisimilarity lts ≠ TraceEq lts := by
  obtain ⟨State, Label, lts, h⟩ := Bisimulation.traceEq_not_bisim
  exists State; exists Label; exists lts
  intro heq
  have hb := Bisimilarity.is_bisimulation (lts := lts)
  rw [heq] at hb
  contradiction

/-- In any deterministic LTS, trace equivalence is a bisimulation. -/
theorem Bisimulation.deterministic_traceEq_is_bisim
    [lts.Deterministic] :
    (lts.IsBisimulation (TraceEq lts)) := by
  simp only [LTS.IsBisimulation]
  intro s1 s2 hteq μ
  constructor
  case left =>
    apply TraceEq.deterministic_sim lts s1 s2 hteq
  case right =>
    intro s2' htr
    apply TraceEq.symm at hteq
    have h := TraceEq.deterministic_sim lts s2 s1 hteq μ s2' htr
    obtain ⟨s1', h⟩ := h
    exists s1'
    constructor
    case left =>
      exact h.1
    case right =>
      apply h.2.symm

/-- In any deterministic LTS, trace equivalence implies bisimilarity. -/
theorem Bisimilarity.deterministic_traceEq_bisim
    [lts.Deterministic] (h : s1 ~tr[lts] s2) :
    (s1 ~[lts] s2) := by
  exists TraceEq lts
  constructor
  case left =>
    exact h
  case right =>
    apply Bisimulation.deterministic_traceEq_is_bisim

/-- In any deterministic LTS, bisimilarity and trace equivalence coincide. -/
theorem Bisimilarity.deterministic_bisim_eq_traceEq [lts.Deterministic] :
    Bisimilarity lts = TraceEq lts := by
  funext s1 s2
  simp only [eq_iff_iff]
  constructor
  case mp =>
    apply Bisimilarity.le_traceEq
  case mpr =>
    apply Bisimilarity.deterministic_traceEq_bisim

/-! ## Relation to simulation -/

open LTS in
/-- Any bisimulation is also a simulation. -/
theorem Bisimulation.is_simulation {lts : LTS State Label} {r : State → State → Prop} :
  lts.IsBisimulation r → Simulation lts r := by
  grind [Simulation]

open LTS in
/-- A relation is a bisimulation iff both it and its inverse are simulations. -/
theorem Bisimulation.simulation_iff {lts : LTS State Label} {r : State → State → Prop} :
    lts.IsBisimulation r ↔ (Simulation lts r ∧ Simulation lts (flip r)) := by
  have _ (s1 s2) : r s1 s2 → flip r s2 s1 := id
  grind [Simulation, flip]

open LTS in
/-- Bisimilarity can also be characterized through symmetric simulations. -/
theorem Bisimilarity.symm_simulation {lts : LTS State Label} :
  Bisimilarity lts =
    fun s1 s2 => ∃ r, r s1 s2 ∧ Std.Symm r ∧ Simulation lts r := by
  funext s1 s2
  apply Iff.eq
  apply Iff.intro
  · intro h
    have bisim : Bisimilarity lts s1 s2 ∧ Std.Symm (Bisimilarity lts)
        ∧ Simulation lts (Bisimilarity lts) := by
      grind [Std.Symm, Bisimilarity.symm, Bisimulation.is_simulation]
    grind
  · intro ⟨r, hr, hsymm, hsim⟩
    have : r = (flip r) := by
      grind [flip, Std.Symm]
    have : lts.IsBisimulation r := by
      grind [Bisimulation.simulation_iff]
    grind

end Bisimulation

section WeakBisimulation

/-! ## Weak bisimulation and weak bisimilarity -/

/-- A weak bisimulation is similar to a `Bisimulation`, but allows for the related processes to do
internal work. Technically, this is defined as a `Bisimulation` on the saturation of the LTS. -/
def LTS.IsWeakBisimulation [HasTau Label] (lts : LTS State Label)
    (r : State → State → Prop) :=
  lts.saturate.IsBisimulation  r

/-- Two states are weakly bisimilar if they are related by some weak bisimulation. -/
def WeakBisimilarity [HasTau Label] (lts : LTS State Label) : State → State → Prop :=
  fun s1 s2 =>
    ∃ r : State → State → Prop, r s1 s2 ∧ lts.IsWeakBisimulation r

/-- Notation for weak bisimilarity. -/
notation s:max " ≈[" lts "] " s':max => WeakBisimilarity lts s s'

/-- An `SWBisimulation` is a more convenient definition of weak bisimulation, because the challenge
is a single transition. We prove later that this technique is sound, following a strategy inspired
by [Sangiorgi2011]. -/
def LTS.IsSWBisimulation [HasTau Label] (lts : LTS State Label) (r : State → State → Prop) : Prop :=
  ∀ ⦃s1 s2⦄, r s1 s2 → ∀ μ, (
    (∀ s1', lts.Tr s1 μ s1' → ∃ s2', lts.STr s2 μ s2' ∧ r s1' s2')
    ∧
    (∀ s2', lts.Tr s2 μ s2' → ∃ s1', lts.STr s1 μ s1' ∧ r s1' s2')
  )

/-- Utility theorem for 'following' internal transitions using an `SWBisimulation`
(first component, weighted version). -/
theorem SWBisimulation.follow_internal_fst_n
  [HasTau Label] {lts : LTS State Label}
  (hswb : lts.IsSWBisimulation r) (hr : r s1 s2) (hstrN : lts.STrN n s1 HasTau.τ s1') :
  ∃ s2', lts.STr s2 HasTau.τ s2' ∧ r s1' s2' := by
  cases n
  case zero =>
    cases hstrN
    exists s2
    constructor; constructor
    exact hr
  case succ n ih =>
    cases hstrN
    rename_i n1 sb sb' n2 hstrN1 htr hstrN2
    let hswb_m := hswb
    have ih1 := SWBisimulation.follow_internal_fst_n hswb hr hstrN1
    obtain ⟨sb2, hstrs2, hrsb⟩ := ih1
    have h := (hswb hrsb HasTau.τ).1 sb' htr
    obtain ⟨sb2', hstrsb2, hrsb2⟩ := h
    have ih2 := SWBisimulation.follow_internal_fst_n hswb hrsb2 hstrN2
    obtain ⟨s2', hstrs2', hrs2⟩ := ih2
    exists s2'
    constructor
    · apply LTS.STr.trans_τ lts (LTS.STr.trans_τ lts hstrs2 hstrsb2) hstrs2'
    · exact hrs2

/-- Utility theorem for 'following' internal transitions using an `SWBisimulation`
(second component, weighted version). -/
theorem SWBisimulation.follow_internal_snd_n
  [HasTau Label] {lts : LTS State Label}
  (hswb : lts.IsSWBisimulation r) (hr : r s1 s2) (hstrN : lts.STrN n s2 HasTau.τ s2') :
  ∃ s1', lts.STr s1 HasTau.τ s1' ∧ r s1' s2' := by
  cases n
  case zero =>
    cases hstrN
    exists s1
    constructor; constructor
    exact hr
  case succ n ih =>
    cases hstrN
    rename_i n1 sb sb' n2 hstrN1 htr hstrN2
    let hswb_m := hswb
    have ih1 := SWBisimulation.follow_internal_snd_n hswb hr hstrN1
    obtain ⟨sb1, hstrs1, hrsb⟩ := ih1
    have h := (hswb hrsb HasTau.τ).2 sb' htr
    obtain ⟨sb2', hstrsb2, hrsb2⟩ := h
    have ih2 := SWBisimulation.follow_internal_snd_n  hswb hrsb2 hstrN2
    obtain ⟨s2', hstrs2', hrs2⟩ := ih2
    exists s2'
    constructor
    · apply LTS.STr.trans_τ lts (LTS.STr.trans_τ lts hstrs1 hstrsb2) hstrs2'
    · exact hrs2

/-- Utility theorem for 'following' internal transitions using an `SWBisimulation`
(first component). -/
theorem SWBisimulation.follow_internal_fst
  [HasTau Label] {lts : LTS State Label}
  (hswb : lts.IsSWBisimulation r) (hr : r s1 s2) (hstr : lts.STr s1 HasTau.τ s1') :
  ∃ s2', lts.STr s2 HasTau.τ s2' ∧ r s1' s2' := by
  obtain ⟨n, hstrN⟩ := (LTS.sTr_sTrN lts).1 hstr
  apply SWBisimulation.follow_internal_fst_n hswb hr hstrN

/-- Utility theorem for 'following' internal transitions using an `SWBisimulation`
(second component). -/
theorem SWBisimulation.follow_internal_snd
  [HasTau Label] {lts : LTS State Label}
  (hswb : lts.IsSWBisimulation r) (hr : r s1 s2) (hstr : lts.STr s2 HasTau.τ s2') :
  ∃ s1', lts.STr s1 HasTau.τ s1' ∧ r s1' s2' := by
  obtain ⟨n, hstrN⟩ := (LTS.sTr_sTrN lts).1 hstr
  apply SWBisimulation.follow_internal_snd_n hswb hr hstrN

/-- We can now prove that any relation is a `WeakBisimulation` iff it is an `SWBisimulation`.
This formalises lemma 4.2.10 in [Sangiorgi2011]. -/
theorem LTS.isWeakBisimulation_iff_isSWBisimulation
  [HasTau Label] {lts : LTS State Label} :
  lts.IsWeakBisimulation r ↔ lts.IsSWBisimulation r := by
  apply Iff.intro
  case mp =>
    intro h s1 s2 hr μ
    apply And.intro
    case left =>
      intro s1' htr
      specialize h hr μ
      have h' := h.1 s1' (LTS.STr.single lts htr)
      obtain ⟨s2', htr2, hr2⟩ := h'
      exists s2'
    case right =>
      intro s2' htr
      specialize h hr μ
      have h' := h.2 s2' (LTS.STr.single lts htr)
      obtain ⟨s1', htr1, hr1⟩ := h'
      exists s1'
  case mpr =>
    intro h s1 s2 hr μ
    apply And.intro
    case left =>
      intro s1' hstr
      cases hstr
      case refl =>
        exists s2
        constructor; constructor
        exact hr
      case tr sb sb' hstr1 htr hstr2 =>
        obtain ⟨sb2, hstr2b, hrb⟩ := SWBisimulation.follow_internal_fst h hr hstr1
        obtain ⟨sb2', hstr2b', hrb'⟩ := (h hrb μ).1 _ htr
        obtain ⟨s2', hstr2', hrb2⟩ := SWBisimulation.follow_internal_fst h hrb' hstr2
        exists s2'
        constructor
        · exact LTS.STr.comp lts hstr2b hstr2b' hstr2'
        · exact hrb2
    case right =>
      intro s2' hstr
      cases hstr
      case refl =>
        exists s1
        constructor; constructor
        exact hr
      case tr sb sb' hstr1 htr hstr2 =>
        obtain ⟨sb1, hstr1b, hrb⟩ := SWBisimulation.follow_internal_snd h hr hstr1
        obtain ⟨sb2', hstr1b', hrb'⟩ := (h hrb μ).2 _ htr
        obtain ⟨s1', hstr1', hrb2⟩ := SWBisimulation.follow_internal_snd h hrb' hstr2
        exists s1'
        constructor
        · exact LTS.STr.comp lts hstr1b hstr1b' hstr1'
        · exact hrb2

theorem WeakBisimulation.toSwBisimulation
  [HasTau Label] {lts : LTS State Label} {r : State → State → Prop} (h : lts.IsWeakBisimulation r) :
    lts.IsSWBisimulation r := LTS.isWeakBisimulation_iff_isSWBisimulation.1 h

theorem SWBisimulation.toWeakBisimulation
  [HasTau Label] {lts : LTS State Label} {r : State → State → Prop} (h : lts.IsSWBisimulation r) :
    lts.IsWeakBisimulation r := LTS.isWeakBisimulation_iff_isSWBisimulation.2 h

/-- Weak bisimilarity can also be characterized through sw-bisimulations. -/
@[scoped grind =]
theorem WeakBisimilarity.weakBisim_eq_swBisim [HasTau Label] (lts : LTS State Label) :
  WeakBisimilarity lts =
    fun s1 s2 => ∃ r : State → State → Prop, r s1 s2 ∧ lts.IsSWBisimulation r := by
  grind [WeakBisimilarity, LTS.isWeakBisimulation_iff_isSWBisimulation.1,
    LTS.isWeakBisimulation_iff_isSWBisimulation.2]

/-- Weak bisimilarity is reflexive. -/
theorem WeakBisimilarity.refl [HasTau Label] (lts : LTS State Label) (s : State) :
    s ≈[lts] s := by
  rw [WeakBisimilarity.weakBisim_eq_swBisim lts]
  exists Eq
  grind [LTS.IsSWBisimulation, LTS.STr.single]

/-- The inverse of a weak bisimulation is a weak bisimulation. -/
theorem WeakBisimulation.inv [HasTau Label] (lts : LTS State Label)
  (r : State → State → Prop) (h : lts.IsWeakBisimulation r) :
  lts.IsWeakBisimulation (flip r) := by
  grind [WeakBisimulation.toSwBisimulation, LTS.IsSWBisimulation,
    flip, SWBisimulation.toWeakBisimulation]

/-- Weak bisimilarity is symmetric. -/
theorem WeakBisimilarity.symm [HasTau Label] (lts : LTS State Label) (h : s1 ≈[lts] s2) :
    s2 ≈[lts] s1 := by
  obtain ⟨r, hr, hrh⟩ := h
  exists (flip r)
  grind [WeakBisimulation.inv, flip]

/-- The composition of two weak bisimulations is a weak bisimulation. -/
theorem WeakBisimulation.comp
  [HasTau Label]
  (lts : LTS State Label)
  (r1 r2 : State → State → Prop) (h1 : lts.IsWeakBisimulation r1) (h2 : lts.IsWeakBisimulation r2) :
  lts.IsWeakBisimulation (Relation.Comp r1 r2) := by
  simp_all only [LTS.IsWeakBisimulation]
  exact h1.comp h2

/-- The composition of two sw-bisimulations is an sw-bisimulation. -/
theorem SWBisimulation.comp
  [HasTau Label]
  (lts : LTS State Label)
  (r1 r2 : State → State → Prop) (h1 : lts.IsSWBisimulation r1) (h2 : lts.IsSWBisimulation r2) :
  lts.IsSWBisimulation (Relation.Comp r1 r2) := by
  simp_all only [LTS.isWeakBisimulation_iff_isSWBisimulation.symm]
  apply WeakBisimulation.comp lts r1 r2 h1 h2

/-- Weak bisimilarity is transitive. -/
theorem WeakBisimilarity.trans [HasTau Label] {s1 s2 s3 : State}
    (lts : LTS State Label) (h1 : s1 ≈[lts] s2) (h2 : s2 ≈[lts] s3) : s1 ≈[lts] s3 := by
  obtain ⟨r1, hr1, hr1b⟩ := h1
  obtain ⟨r2, hr2, hr2b⟩ := h2
  exists Relation.Comp r1 r2
  constructor
  case left =>
    exists s2
  case right =>
    apply WeakBisimulation.comp lts r1 r2 hr1b hr2b

/-- Weak bisimilarity is an equivalence relation. -/
theorem WeakBisimilarity.eqv [HasTau Label] {lts : LTS State Label} :
  Equivalence (WeakBisimilarity lts) := {
    refl := WeakBisimilarity.refl lts
    symm := WeakBisimilarity.symm lts
    trans := WeakBisimilarity.trans lts
  }

end WeakBisimulation

end Cslib
