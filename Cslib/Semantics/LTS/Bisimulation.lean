/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Cslib.Semantics.LTS.Basic
import Cslib.Semantics.LTS.TraceEq
import Cslib.Data.Relation
import Cslib.Semantics.LTS.Simulation

/-! # Bisimulation and Bisimilarity

A bisimulation is a binary relation on the states of an `LTS`, which establishes a tight semantic
correspondence. More specifically, if two states `s1` and `s2` are related by a bisimulation, then
`s1` can mimic all transitions of `s2` and vice versa. Furthermore, the derivatives reaches through
these transitions remain related by the bisimulation.

Bisimilarity is the largest bisimulation: given an `LTS`, it relates any two states that are related
by a bisimulation for that LTS.

Weak bisimulation (resp. bisimilarity) is the relaxed version of bisimulation (resp. bisimilarity) whereby internal actions performed by processes can be ignored.

For an introduction to theory of bisimulation, we refer to [Sangiorgi2011].

## Main definitions

- `Bisimulation lts r`: the relation `r` on the states of the LTS `lts` is a bisimulation.
- `Bisimilarity lts` is the binary relation on the states of `lts` that relates any two states
related by some bisimulation on `lts`.
- `BisimulationUpTo lts r`: the relation `r` is a bisimulation up to bisimilarity (this is known as
one of the 'up to' techniques for bisimulation).

- `WeakBisimulation lts r`: the relation `r` on the states of the LTS `lts` is a weak bisimulation.
- `WeakBisimilarity lts` is the binary relation on the states of `lts` that relates any two states
related by some weak bisimulation on `lts`.
- `SWBisimulation lts` is a more convenient definition for establishing weak bisimulations, which
we prove to be sound and complete.
- `SWBisimilarity lts` is the binary relation on the states of `lts` that relates any two states
related by some sw-bisimulation on `lts`.

## Notations

- `s1 ~[lts] s2`: the states `s1` and `s2` are bisimilar in the LTS `lts`.
- `s1 ≈[lts] s2`: the states `s1` and `s2` are weakly bisimilar in the LTS `lts`.
- `s1 ≈sw[lts] s2`: the states `s1` and `s2` are sw bisimilar in the LTS `lts`.

## Main statements

- `Bisimulation.inv`: the inverse of a bisimulation is a bisimulation.
- `Bisimilarity.eqv`: bisimilarity is an equivalence relation (see `Equivalence`).
- `Bisimilarity.is_bisimulation`: bisimilarity is itself a bisimulation.
- `Bisimilarity.largest_bisimulation`: bisimilarity is the largest bisimulation.
- `Bisimilarity.gfp`: the union of bisimilarity and any bisimulation is equal to bisimilarity.
- `Bisimulation.upTo_bisimulation`: any bisimulation up to bisimilarity is a bisimulation.
- `Bisimulation.bisim_traceEq`: any bisimulation that relates two states implies that they are
trace equivalent (see `TraceEq`).
- `Bisimilarity.deterministic_bisim_eq_traceEq`: in a deterministic LTS, bisimilarity and trace
equivalence coincide.
- `WeakBisimilarity.weakBisim_eq_swBisim`: weak bisimilarity and sw-bisimilarity coincide in all LTSs.
- `WeakBisimilarity.eqv`: weak bisimilarity is an equivalence relation.
- `SWBisimilarity.eqv`: sw-bisimilarity is an equivalence relation.

-/

universe u v

section Bisimulation

variable {State : Type u} {Label : Type v} (lts : LTS State Label)

/-- A relation is a bisimulation if, whenever it relates two states in an lts,
the transitions originating from these states mimic each other and the reached
derivatives are themselves related. -/
def Bisimulation (lts : LTS State Label) (r : State → State → Prop) : Prop :=
  ∀ s1 s2, r s1 s2 → ∀ μ, (
    (∀ s1', lts.Tr s1 μ s1' → ∃ s2', lts.Tr s2 μ s2' ∧ r s1' s2')
    ∧
    (∀ s2', lts.Tr s2 μ s2' → ∃ s1', lts.Tr s1 μ s1' ∧ r s1' s2')
  )

/-- Helper for following a transition using the first component of a `Bisimulation`. -/
def Bisimulation.follow_fst {lts : LTS State Label} {r : State → State → Prop} (hb : Bisimulation lts r) (hr : r s1 s2) (μ : Label) (htr : lts.Tr s1 μ s1'):=
  (hb _ _ hr μ).1 _ htr

/-- Helper for following a transition using the second component of a `Bisimulation`. -/
def Bisimulation.follow_snd {lts : LTS State Label} {r : State → State → Prop} (hb : Bisimulation lts r) (hr : r s1 s2) (μ : Label) (htr : lts.Tr s2 μ s2'):=
  (hb _ _ hr μ).2 _ htr

/-- Two states are bisimilar if they are related by some bisimulation. -/
def Bisimilarity (lts : LTS State Label) : State → State → Prop :=
  fun s1 s2 =>
    ∃ r : State → State → Prop, r s1 s2 ∧ Bisimulation lts r

/--
Notation for bisimilarity.

Differently from standard pen-and-paper presentations, we require the lts to be mentioned
explicitly.
-/
notation s:max " ~[" lts "] " s':max => Bisimilarity lts s s'

/-- Bisimilarity is reflexive. -/
theorem Bisimilarity.refl (s : State) : s ~[lts] s := by
  exists Eq
  constructor
  case left => rfl
  case right =>
    simp only [Bisimulation]
    intro s1 s2 hr μ
    cases hr
    constructor
    case left =>
      intro s1' htr
      exists s1'
    case right =>
      intro s1' htr
      exists s1'

/-- The inverse of a bisimulation is a bisimulation. -/
theorem Bisimulation.inv (r : State → State → Prop) (h : Bisimulation lts r) :
  Bisimulation lts (Relation.inv r) := by
  simp only [Bisimulation] at h
  simp only [Bisimulation]
  intro s1 s2 hrinv μ
  constructor
  case left =>
    intro s1' htr
    specialize h s2 s1 hrinv μ
    have h' := h.2 s1' htr
    obtain ⟨ s2', h' ⟩ := h'
    exists s2'
  case right =>
    intro s2' htr
    specialize h s2 s1 hrinv μ
    have h' := h.1 s2' htr
    obtain ⟨ s1', h' ⟩ := h'
    exists s1'

/-- Bisimilarity is symmetric. -/
theorem Bisimilarity.symm {s1 s2 : State} (h : s1 ~[lts] s2) : s2 ~[lts] s1 := by
  obtain ⟨r, hr, hb⟩ := h
  exists (Relation.inv r)
  constructor
  case left =>
    exact hr
  case right =>
    apply Bisimulation.inv
    exact hb

/-- The composition of two bisimulations is a bisimulation. -/
theorem Bisimulation.comp
  (r1 r2 : State → State → Prop) (h1 : Bisimulation lts r1) (h2 : Bisimulation lts r2) :
  Bisimulation lts (Relation.Comp r1 r2) := by
  simp_all only [Bisimulation]
  intro s1 s2 hrc μ
  constructor
  case left =>
    intro s1' htr
    rcases hrc with ⟨sb, hr1, hr2⟩
    specialize h1 s1 sb hr1 μ
    specialize h2 sb s2 hr2 μ
    have h1' := h1.1 s1' htr
    obtain ⟨s1'', h1'tr, h1'⟩ := h1'
    have h2' := h2.1 s1'' h1'tr
    obtain ⟨s2'', h2'tr, h2'⟩ := h2'
    exists s2''
    constructor
    · exact h2'tr
    · exists s1''
  case right =>
    intro s2' htr
    rcases hrc with ⟨sb, hr1, hr2⟩
    specialize h1 s1 sb hr1 μ
    specialize h2 sb s2 hr2 μ
    have h2' := h2.2 s2' htr
    obtain ⟨s2'', h2'tr, h2'⟩ := h2'
    have h1' := h1.2 s2'' h2'tr
    obtain ⟨s1'', h1'tr, h1'⟩ := h1'
    exists s1''
    constructor
    · exact h1'tr
    · exists s2''

/-- Bisimilarity is transitive. -/
theorem Bisimilarity.trans
  {s1 s2 s3 : State} (h1 : s1 ~[lts] s2) (h2 : s2 ~[lts] s3) :
  s1 ~[lts] s3 := by
  obtain ⟨r1, hr1, hr1b⟩ := h1
  obtain ⟨r2, hr2, hr2b⟩ := h2
  exists Relation.Comp r1 r2
  constructor
  case left =>
    exists s2
  case right =>
    apply Bisimulation.comp lts r1 r2 hr1b hr2b

/-- Bisimilarity is an equivalence relation. -/
theorem Bisimilarity.eqv (lts : LTS State Label) :
  Equivalence (Bisimilarity lts) := {
    refl := Bisimilarity.refl lts
    symm := Bisimilarity.symm lts
    trans := Bisimilarity.trans lts
  }

/-- Bisimilarity is a bisimulation. -/
theorem Bisimilarity.is_bisimulation : Bisimulation lts (Bisimilarity lts) := by
  simp only [Bisimulation]
  intro s1 s2 h μ
  obtain ⟨r, hr, hb⟩ := h
  have hrBisim := hb
  simp [Bisimulation] at hb
  specialize hb s1 s2
  constructor
  case left =>
    intro s1' htr
    specialize hb hr μ
    obtain ⟨hb1, hb2⟩ := hb
    specialize hb1 s1' htr
    obtain ⟨s2', htr2, hr2⟩ := hb1
    exists s2'
    constructor
    case left =>
      exact htr2
    case right =>
      exists r
  case right =>
    intro s2' htr
    specialize hb hr μ
    obtain ⟨hb1, hb2⟩ := hb
    specialize hb2 s2' htr
    obtain ⟨s1', htr1, hr1⟩ := hb2
    exists s1'
    constructor
    case left =>
      exact htr1
    case right =>
      exists r

/-- Bisimilarity is the largest bisimulation. -/
theorem Bisimilarity.largest_bisimulation
  (r : State → State → Prop) (h : Bisimulation lts r) (s1 s2 : State) :
  r s1 s2 → s1 ~[lts] s2 := by
  intro hr
  exists r

/-- The union of bisimilarity with any bisimulation is bisimilarity. -/
theorem Bisimilarity.gfp (r : State → State → Prop) (h : Bisimulation lts r) :
  (Bisimilarity lts) ⊔ r = Bisimilarity lts := by
  funext s1 s2
  simp only [max, SemilatticeSup.sup, eq_iff_iff, or_iff_left_iff_imp]
  apply Bisimilarity.largest_bisimulation lts r h

/-- A relation `r` is a bisimulation up to bisimilarity if, whenever it relates two
states in an lts, the transitions originating from these states mimic each other and the reached
derivatives are themselves related by `r` up to bisimilarity. -/
def BisimulationUpTo (lts : LTS State Label) (r : State → State → Prop) : Prop :=
  ∀ s1 s2, r s1 s2 → ∀ μ, (
    (∀ s1', lts.Tr s1 μ s1' → ∃ s2', lts.Tr s2 μ s2' ∧ Relation.upTo r (Bisimilarity lts) s1' s2')
    ∧
    (∀ s2', lts.Tr s2 μ s2' → ∃ s1', lts.Tr s1 μ s1' ∧ Relation.upTo r (Bisimilarity lts) s1' s2')
  )

/-- Any bisimulation up to bisimilarity is a bisimulation. -/
theorem Bisimulation.upTo_bisimulation (r : State → State → Prop) (h : BisimulationUpTo lts r) :
  Bisimulation lts (Relation.upTo r (Bisimilarity lts)) := by
  simp [Bisimulation]
  simp [BisimulationUpTo] at h
  intro s1 s2 hr μ
  rcases hr with ⟨s1b, hr1b, s2b, hrb, hr2b⟩
  obtain ⟨r1, hr1, hr1b⟩ := hr1b
  obtain ⟨r2, hr2, hr2b⟩ := hr2b
  constructor
  case left =>
    intro s1' htr1
    obtain ⟨s1b', hs1b'tr, hs1b'r⟩ := (hr1b _ _ hr1 μ).1 s1' htr1
    obtain ⟨s2b', hs2b'tr, hs2b'r⟩ := (h s1b s2b hrb μ).1 s1b' hs1b'tr
    obtain ⟨s2', hs2btr, hs2br⟩ := (hr2b _ _ hr2 μ).1 _ hs2b'tr
    exists s2'
    constructor
    case left =>
      exact hs2btr
    case right =>
      obtain ⟨smid1, hsmidb, smid2, hsmidr, hsmidrb⟩ := hs2b'r
      constructor
      constructor
      · apply Bisimilarity.trans lts (Bisimilarity.largest_bisimulation lts r1 hr1b _ _ hs1b'r)
          hsmidb
      · exists smid2
        constructor
        · exact hsmidr
        · apply Bisimilarity.trans lts hsmidrb
          apply Bisimilarity.largest_bisimulation lts r2 hr2b s2b' s2' hs2br
  case right =>
    intro s2' htr2
    obtain ⟨s2b', hs2b'tr, hs2b'r⟩ := (hr2b _ _ hr2 μ).2 s2' htr2
    obtain ⟨s1b', hs1b'tr, hs1b'r⟩ := (h s1b s2b hrb μ).2 s2b' hs2b'tr
    obtain ⟨s1', hs1btr, hs1br⟩ := (hr1b _ _ hr1 μ).2 _ hs1b'tr
    exists s1'
    constructor
    case left =>
      exact hs1btr
    case right =>
      obtain ⟨smid1, hsmidb, smid2, hsmidr, hsmidrb⟩ := hs1b'r
      constructor
      constructor
      · apply Bisimilarity.trans lts (Bisimilarity.largest_bisimulation lts r1 hr1b _ _ _) hsmidb
        · exact hs1br
      · exists smid2
        constructor
        · exact hsmidr
        · apply Bisimilarity.trans lts hsmidrb
          apply Bisimilarity.largest_bisimulation lts r2 hr2b s2b' s2' _
          exact hs2b'r

/-- If two states are related by a bisimulation, they can mimic each other's multi-step
transitions. -/
theorem Bisimulation.bisim_trace
  (s1 s2 : State) (r : State → State → Prop) (hb : Bisimulation lts r) (hr : r s1 s2) :
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
      simp [Bisimulation] at hb
      specialize hb s1 s2 hr μ
      have hf := hb.1 s1'' htr
      obtain ⟨s2'', htr2, hb2⟩ := hf
      specialize ih s1'' s2'' hb2 s1' hmtr
      obtain ⟨s2', hmtr2, hr'⟩ := ih
      exists s2'
      constructor
      case left =>
        constructor
        · exact htr2
        · exact hmtr2
      case right =>
        exact hr'

/-! ### Relation to trace equivalence -/

/-- Any bisimulation implies trace equivalence. -/
theorem Bisimulation.bisim_traceEq
  (s1 s2 : State) (r : State → State → Prop) (hb : Bisimulation lts r) (hr : r s1 s2) :
  s1 ~tr[lts] s2 := by
  simp [TraceEq, LTS.traces, setOf]
  funext μs
  simp only [eq_iff_iff]
  constructor
  case mp =>
    intro h
    obtain ⟨s1', h⟩ := h
    obtain ⟨s2', hmtr⟩ := @Bisimulation.bisim_trace State Label lts s1 s2 r hb hr μs s1' h
    exists s2'
    exact hmtr.1
  case mpr =>
    intro h
    obtain ⟨s2', h⟩ := h
    have hinv := @Bisimulation.inv State Label lts r hb
    obtain ⟨s1', hmtr⟩ := @Bisimulation.bisim_trace State Label lts s2 s1 (Relation.inv r) hinv hr μs s2' h
    exists s1'
    exact hmtr.1

/-- Bisimilarity implies trace equivalence. -/
theorem Bisimilarity.bisim_traceEq (s1 s2 : State) (h : s1 ~[lts] s2) :
  s1 ~tr[lts] s2 := by
  obtain ⟨r, hr, hb⟩ := h
  apply Bisimulation.bisim_traceEq lts s1 s2 r hb hr

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
  ∃ (State : Type) (Label : Type) (lts : LTS State Label), ¬(Bisimulation lts (TraceEq lts)) := by
  exists ℕ
  exists Char
  let lts := LTS.mk BisimMotTr
  exists lts
  intro h
  simp [Bisimulation] at h
  specialize h 1 5
  have htreq : (1 ~tr[lts] 5) := by
    simp [TraceEq]
    have htraces1 : lts.traces 1 = {[], ['a'], ['a', 'b'], ['a', 'c']} := by
      simp [LTS.traces]
      apply Set.ext_iff.2
      intro μs
      apply Iff.intro
      case mp =>
        intro h1
        obtain ⟨s', htr⟩ := h1
        cases htr
        case intro.refl =>
          simp
        case intro.stepL μ sb μs' htr hmtr =>
          cases htr
          simp
          cases hmtr <;> simp
          case one2two.stepL μ sb μs' htr hmtr =>
            cases htr <;> cases hmtr <;> simp <;> contradiction
      case mpr =>
        intro h1
        cases h1
        case inl h1 =>
          simp [h1]
          exists 1
          constructor
        case inr h1 =>
          cases h1
          case inl h1 =>
            simp [h1]
            exists 2
            apply LTS.MTr.single; constructor
          case inr h1 =>
            cases h1
            case inl h1 =>
              simp [h1]
              exists 3
              constructor; apply BisimMotTr.one2two; apply LTS.MTr.single;
                apply BisimMotTr.two2three
            case inr h1 =>
              cases h1
              exists 4
              constructor; apply BisimMotTr.one2two; apply LTS.MTr.single;
                apply BisimMotTr.two2four
    have htraces2 : lts.traces 5 = {[], ['a'], ['a', 'b'], ['a', 'c']} := by
      simp [LTS.traces]
      apply Set.ext_iff.2
      intro μs
      apply Iff.intro
      case mp =>
        intro h1
        obtain ⟨s', htr⟩ := h1
        cases htr
        case intro.refl =>
          simp
        case intro.stepL μ sb μs' htr hmtr =>
          cases htr
          case five2six =>
            simp
            cases hmtr
            case refl =>
              simp
            case stepL μ sb μs' htr hmtr =>
              cases htr
              cases hmtr
              case refl => right; left; simp
              case stepL μ sb μs' htr hmtr =>
                cases htr
          case five2eight =>
            simp
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
          simp [h1]
          exists 5
          constructor
        case inr h1 =>
          cases h1
          case inl h1 =>
            simp [h1]
            exists 6
            apply LTS.MTr.single; constructor
          case inr h1 =>
            cases h1
            case inl h1 =>
              simp [h1]
              exists 7
              constructor; apply BisimMotTr.five2six; apply LTS.MTr.single;
                apply BisimMotTr.six2seven
            case inr h1 =>
              cases h1
              exists 9
              constructor; apply BisimMotTr.five2eight; apply LTS.MTr.single;
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
      simp [LTS.traces]
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
            cases hmtr <;> simp
            case stepL μ sb μs' htr hmtr =>
              cases htr
          case two2four =>
            cases hmtr
            case refl => simp
            case stepL μ sb μs' htr hmtr =>
              cases htr
      case mpr =>
        intro h
        cases h
        case inl h =>
          simp
          exists 2
          simp [h]
          constructor
        case inr h =>
          simp
          cases h
          case inl h =>
            exists 3; simp [h]; constructor; constructor; constructor
          case inr h =>
            exists 4
            simp at h
            simp [h]
            constructor; constructor; constructor
    have htraces6 : lts.traces 6 = {[], ['b']} := by
      simp [LTS.traces]
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
          cases hmtr <;> simp
          case stepL μ sb μs' htr hmtr =>
            cases htr
      case mpr =>
        intro h
        cases h
        case inl h =>
          simp
          exists 6
          simp [h]
          constructor
        case inr h =>
          simp
          exists 7
          simp at h
          simp [h]
          constructor; constructor; constructor
    rw [htraces2, htraces6] at cih
    apply Set.ext_iff.1 at cih
    specialize cih ['c']
    obtain ⟨cih1, cih2⟩ := cih
    have cih1h : ['c'] ∈ @insert (List Char) (Set (List Char)) Set.instInsert [] {['b'], ['c']} := by
      simp
    specialize cih1 cih1h
    simp at cih1
  case five2eight =>
    simp [TraceEq] at cih
    have htraces2 : lts.traces 2 = {[], ['b'], ['c']} := by
      simp [LTS.traces]
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
            cases hmtr <;> simp
            case stepL μ sb μs' htr hmtr =>
              cases htr
          case two2four =>
            cases hmtr
            case refl => simp
            case stepL μ sb μs' htr hmtr =>
              cases htr
      case mpr =>
        intro h
        cases h
        case inl h =>
          simp
          exists 2
          simp [h]
          constructor
        case inr h =>
          simp
          cases h
          case inl h =>
            exists 3; simp [h]; constructor; constructor; constructor
          case inr h =>
            exists 4
            simp at h
            simp [h]
            constructor; constructor; constructor
    have htraces8 : lts.traces 8 = {[], ['c']} := by
      simp [LTS.traces]
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
          cases hmtr <;> simp
          case stepL μ sb μs' htr hmtr =>
            cases htr
      case mpr =>
        intro h
        cases h
        case inl h =>
          simp
          exists 8
          simp [h]
          constructor
        case inr h =>
          simp
          exists 9
          simp at h
          simp [h]
          constructor; constructor; constructor
    rw [htraces2, htraces8] at cih
    apply Set.ext_iff.1 at cih
    specialize cih ['b']
    obtain ⟨cih1, cih2⟩ := cih
    have cih1h : ['b'] ∈ @insert (List Char) (Set (List Char)) Set.instInsert [] {['b'], ['c']} := by
      simp
    specialize cih1 cih1h
    simp at cih1

/-- In general, bisimilarity and trace equivalence are distinct. -/
theorem Bisimilarity.bisimilarity_neq_traceEq : ∃ (State : Type) (Label : Type) (lts : LTS State Label), Bisimilarity lts ≠ TraceEq lts := by
  obtain ⟨State, Label, lts, h⟩ := Bisimulation.traceEq_not_bisim
  exists State; exists Label; exists lts
  simp
  intro heq
  have hb := Bisimilarity.is_bisimulation lts
  rw [heq] at hb
  contradiction

/-- In any deterministic LTS, trace equivalence is a bisimulation. -/
theorem Bisimulation.deterministic_traceEq_is_bisim
  (lts : LTS State Label) (hdet : lts.Deterministic) :
  (Bisimulation lts (TraceEq lts)) := by
  simp only [Bisimulation]
  intro s1 s2 hteq μ
  constructor
  case left =>
    apply TraceEq.deterministic_sim lts hdet s1 s2 hteq
  case right =>
    intro s2' htr
    apply TraceEq.symm at hteq
    have h := TraceEq.deterministic_sim lts hdet s2 s1 hteq μ s2' htr
    obtain ⟨s1', h⟩ := h
    exists s1'
    constructor
    case left =>
      exact h.1
    case right =>
      apply h.2.symm

/-- In any deterministic LTS, trace equivalence implies bisimilarity. -/
theorem Bisimilarity.deterministic_traceEq_bisim
  (lts : LTS State Label) (hdet : lts.Deterministic) (s1 s2 : State) (h : s1 ~tr[lts] s2) :
  (s1 ~[lts] s2) := by
  exists TraceEq lts
  constructor
  case left =>
    exact h
  case right =>
    apply Bisimulation.deterministic_traceEq_is_bisim lts hdet

/-- In any deterministic LTS, bisimilarity and trace equivalence coincide. -/
theorem Bisimilarity.deterministic_bisim_eq_traceEq
  (lts : LTS State Label) (hdet : lts.Deterministic) :
  Bisimilarity lts = TraceEq lts := by
  funext s1 s2
  simp [eq_iff_iff]
  constructor
  case mp =>
    apply Bisimilarity.bisim_traceEq
  case mpr =>
    apply Bisimilarity.deterministic_traceEq_bisim lts hdet

/-! ### Relation to simulation -/

/-- Any bisimulation is also a simulation. -/
theorem Bisimulation.is_simulation (lts : LTS State Label) (r : State → State → Prop) : Bisimulation lts r → Simulation lts r := by
  intro h
  simp only [Bisimulation] at h
  simp only [Simulation]
  intro s1 s2 hr μ s1' htr
  specialize h s1 s2 hr μ
  rcases h with ⟨h1, h2⟩
  apply h1 s1' htr

/-- A relation is a bisimulation iff both it and its inverse are simulations. -/
theorem Bisimulation.simulation_iff (lts : LTS State Label) (r : State → State → Prop) : Bisimulation lts r ↔ (Simulation lts r ∧ Simulation lts (Relation.inv r)) := by
  constructor
  intro h
  simp only [Simulation]
  case mp =>
    constructor
    case left =>
      intro s1 s2 hr μ s1' htr
      specialize h s1 s2 hr μ
      rcases h with ⟨h1, h2⟩
      specialize h1 _ htr
      obtain ⟨s2', h1⟩ := h1
      exists s2'
    case right =>
      simp only [Relation.inv, flip]
      intro s2 s1 hr μ s2' htr
      simp only [Bisimulation] at h
      specialize h s1 s2 hr μ
      obtain ⟨h1, h2⟩ := h
      specialize h2 _ htr
      apply h2
  case mpr =>
    intro hs
    obtain ⟨hs, hsinv⟩ := hs
    simp only [Bisimulation]
    intro s1 s2 hr μ
    constructor
    case left =>
      intro s1' htr
      simp only [Simulation] at hs
      apply hs _ _ hr _ _ htr
    case right =>
      intro s2' htr
      apply hsinv _ _ hr _ _ htr

end Bisimulation

section WeakBisimulation

/-! ## Weak bisimulation and weak bisimilarity -/

/-- A weak bisimulation is similar to a `Bisimulation`, but allows for the related processes to do
internal work. Technically, this is defined as a `Bisimulation` on the saturation of the LTS. -/
def WeakBisimulation [HasTau Label] (lts : LTS State Label) (r : State → State → Prop) :=
  Bisimulation (lts.saturate) r

/-- Two states are weakly bisimilar if they are related by some weak bisimulation. -/
def WeakBisimilarity [HasTau Label] (lts : LTS State Label) : State → State → Prop :=
  fun s1 s2 =>
    ∃ r : State → State → Prop, r s1 s2 ∧ WeakBisimulation lts r

/-- Notation for weak bisimilarity. -/
notation s:max " ≈[" lts "] " s':max => WeakBisimilarity lts s s'

/-- An `SWBisimulation` is a more convenient definition of weak bisimulation, because the challenge
is a single transition. We prove later that this technique is sound, following a strategy inspired
by [Sangiorgi2011]. -/
def SWBisimulation [HasTau Label] (lts : LTS State Label) (r : State → State → Prop) : Prop :=
  ∀ s1 s2, r s1 s2 → ∀ μ, (
    (∀ s1', lts.Tr s1 μ s1' → ∃ s2', lts.STr s2 μ s2' ∧ r s1' s2')
    ∧
    (∀ s2', lts.Tr s2 μ s2' → ∃ s1', lts.STr s1 μ s1' ∧ r s1' s2')
  )

/-- Two states are sw-bisimilar if they are related by some sw-bisimulation. -/
def SWBisimilarity [HasTau Label] (lts : LTS State Label) : State → State → Prop :=
  fun s1 s2 =>
    ∃ r : State → State → Prop, r s1 s2 ∧ SWBisimulation lts r

/-- Notation for swbisimilarity. -/
notation s:max " ≈sw[" lts "] " s':max => SWBisimilarity lts s s'

/-- Utility theorem for 'following' internal transitions using an `SWBisimulation`
(first component, weighted version). -/
theorem SWBisimulation.follow_internal_fst_n
  [HasTau Label] (lts : LTS State Label) (r : State → State → Prop)
  (hswb : SWBisimulation lts r) (hr : r s1 s2) (hstrN : lts.strN n s1 HasTau.τ s1') :
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
    simp [SWBisimulation] at hswb
    have ih1 := SWBisimulation.follow_internal_fst_n lts r hswb hr hstrN1
    obtain ⟨sb2, hstrs2, hrsb⟩ := ih1
    have h := (hswb sb sb2 hrsb HasTau.τ).1 sb' htr
    obtain ⟨sb2', hstrsb2, hrsb2⟩ := h
    have ih2 := SWBisimulation.follow_internal_fst_n lts r hswb hrsb2 hstrN2
    obtain ⟨s2', hstrs2', hrs2⟩ := ih2
    exists s2'
    constructor
    · apply LTS.STr.trans_τ lts (LTS.STr.trans_τ lts hstrs2 hstrsb2) hstrs2'
    · exact hrs2

/-- Utility theorem for 'following' internal transitions using an `SWBisimulation`
(second component, weighted version). -/
theorem SWBisimulation.follow_internal_snd_n
  [HasTau Label] (lts : LTS State Label) (r : State → State → Prop)
  (hswb : SWBisimulation lts r) (hr : r s1 s2) (hstrN : lts.strN n s2 HasTau.τ s2') :
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
    simp [SWBisimulation] at hswb
    have ih1 := SWBisimulation.follow_internal_snd_n lts r hswb hr hstrN1
    obtain ⟨sb1, hstrs1, hrsb⟩ := ih1
    have h := (hswb sb1 sb hrsb HasTau.τ).2 sb' htr
    obtain ⟨sb2', hstrsb2, hrsb2⟩ := h
    have ih2 := SWBisimulation.follow_internal_snd_n lts r hswb hrsb2 hstrN2
    obtain ⟨s2', hstrs2', hrs2⟩ := ih2
    exists s2'
    constructor
    · apply LTS.STr.trans_τ lts (LTS.STr.trans_τ lts hstrs1 hstrsb2) hstrs2'
    · exact hrs2

/-- Utility theorem for 'following' internal transitions using an `SWBisimulation`
(first component). -/
theorem SWBisimulation.follow_internal_fst
  [HasTau Label] (lts : LTS State Label) (r : State → State → Prop)
  (hswb : SWBisimulation lts r) (hr : r s1 s2) (hstr : lts.STr s1 HasTau.τ s1') :
  ∃ s2', lts.STr s2 HasTau.τ s2' ∧ r s1' s2' := by
  obtain ⟨n, hstrN⟩ := (LTS.str_strN lts).1 hstr
  apply SWBisimulation.follow_internal_fst_n lts r hswb hr hstrN

/-- Utility theorem for 'following' internal transitions using an `SWBisimulation`
(second component). -/
theorem SWBisimulation.follow_internal_snd
  [HasTau Label] (lts : LTS State Label) (r : State → State → Prop)
  (hswb : SWBisimulation lts r) (hr : r s1 s2) (hstr : lts.STr s2 HasTau.τ s2') :
  ∃ s1', lts.STr s1 HasTau.τ s1' ∧ r s1' s2' := by
  obtain ⟨n, hstrN⟩ := (LTS.str_strN lts).1 hstr
  apply SWBisimulation.follow_internal_snd_n lts r hswb hr hstrN

/-- We can now prove that any relation is a `WeakBisimulation` iff it is an `SWBisimulation`. This formalises lemma 4.2.10 in [Sangiorgi2011]. -/
theorem WeakBisimulation.iff_swBisimulation [HasTau Label] (lts : LTS State Label) (r : State → State → Prop) :
  WeakBisimulation lts r ↔ SWBisimulation lts r := by
  apply Iff.intro
  case mp =>
    intro h
    simp [WeakBisimulation, Bisimulation] at h
    simp [SWBisimulation]
    intro s1 s2 hr μ
    apply And.intro
    case left =>
      intro s1' htr
      specialize h s1 s2 hr μ
      have h' := h.1 s1' (LTS.STr.single lts htr)
      obtain ⟨s2', htr2, hr2⟩ := h'
      exists s2'
    case right =>
      intro s2' htr
      specialize h s1 s2 hr μ
      have h' := h.2 s2' (LTS.STr.single lts htr)
      obtain ⟨s1', htr1, hr1⟩ := h'
      exists s1'
  case mpr =>
    intro h
    simp [WeakBisimulation, Bisimulation]
    intro s1 s2 hr μ
    apply And.intro
    case left =>
      intro s1' hstr
      cases hstr
      case refl =>
        exists s2
        constructor; constructor
        exact hr
      case tr sb sb' hstr1 htr hstr2 =>
        obtain ⟨sb2, hstr2b, hrb⟩ := SWBisimulation.follow_internal_fst lts r h hr hstr1
        obtain ⟨sb2', hstr2b', hrb'⟩ := (h sb sb2 hrb μ).1 _ htr
        obtain ⟨s2', hstr2', hrb2⟩ := SWBisimulation.follow_internal_fst lts r h hrb' hstr2
        exists s2'
        constructor
        · simp [LTS.saturate]
          apply LTS.STr.comp lts hstr2b hstr2b' hstr2'
        · exact hrb2
    case right =>
      intro s2' hstr
      cases hstr
      case refl =>
        exists s1
        constructor; constructor
        exact hr
      case tr sb sb' hstr1 htr hstr2 =>
        obtain ⟨sb1, hstr1b, hrb⟩ := SWBisimulation.follow_internal_snd lts r h hr hstr1
        obtain ⟨sb2', hstr1b', hrb'⟩ := (h sb1 sb hrb μ).2 _ htr
        obtain ⟨s1', hstr1', hrb2⟩ := SWBisimulation.follow_internal_snd lts r h hrb' hstr2
        exists s1'
        constructor
        · simp [LTS.saturate]
          apply LTS.STr.comp lts hstr1b hstr1b' hstr1'
        · exact hrb2

theorem WeakBisimulation.toSwBisimulation [HasTau Label] {lts : LTS State Label} {r : State → State → Prop} (h : WeakBisimulation lts r) : SWBisimulation lts r := (WeakBisimulation.iff_swBisimulation lts r).1 h

theorem SWBisimulation.toWeakBisimulation [HasTau Label] {lts : LTS State Label} {r : State → State → Prop} (h : SWBisimulation lts r) : WeakBisimulation lts r := (WeakBisimulation.iff_swBisimulation lts r).2 h

/-- If two states are related by an `SWBisimulation`, then they are weakly bisimilar. -/
theorem WeakBisimilarity.by_swBisimulation [HasTau Label]
  (lts : LTS State Label) (r : State → State → Prop)
  (hb : SWBisimulation lts r) (hr : r s1 s2) : s1 ≈[lts] s2 := by
  exists r
  constructor; exact hr
  apply (WeakBisimulation.iff_swBisimulation lts r).2 hb

/-- Weak bisimilarity and sw-bisimilarity coincide for all LTSs. -/
theorem WeakBisimilarity.weakBisim_eq_swBisim [HasTau Label] (lts : LTS State Label) :
  WeakBisimilarity lts = SWBisimilarity lts := by
  funext s1 s2
  simp [WeakBisimilarity, SWBisimilarity]
  constructor
  case mp =>
    intro h
    obtain ⟨r, hr, hrh⟩ := h
    exists r
    constructor; exact hr
    apply (WeakBisimulation.iff_swBisimulation lts r).1 hrh
  case mpr =>
    intro h
    obtain ⟨r, hr, hrh⟩ := h
    exists r
    constructor; exact hr
    apply (WeakBisimulation.iff_swBisimulation lts r).2 hrh

/-- sw-bisimilarity is reflexive. -/
theorem SWBisimilarity.refl [HasTau Label] (lts : LTS State Label) (s : State) : s ≈sw[lts] s := by
  simp [SWBisimilarity]
  exists Eq
  constructor; rfl
  simp only [SWBisimulation]
  intro s1 s2 hr μ
  cases hr
  constructor
  case left =>
    intro s1' htr
    exists s1'
    constructor
    · apply LTS.STr.single _ htr
    · constructor
  case right =>
    intro s2' htr
    exists s2'
    constructor
    · apply LTS.STr.single _ htr
    · constructor

/-- Weak bisimilarity is reflexive. -/
theorem WeakBisimilarity.refl [HasTau Label] (lts : LTS State Label) (s : State) : s ≈[lts] s := by
  rw [WeakBisimilarity.weakBisim_eq_swBisim lts]
  apply SWBisimilarity.refl

/-- The inverse of an sw-bisimulation is an sw-bisimulation. -/
theorem SWBisimulation.inv [HasTau Label] (lts : LTS State Label)
  (r : State → State → Prop) (h : SWBisimulation lts r) :
  SWBisimulation lts (Relation.inv r) := by
  simp only [SWBisimulation] at h
  simp only [SWBisimulation]
  intro s1 s2 hrinv μ
  constructor
  case left =>
    intro s1' htr
    specialize h s2 s1 hrinv μ
    have h' := h.2 s1' htr
    obtain ⟨ s2', h' ⟩ := h'
    exists s2'
  case right =>
    intro s2' htr
    specialize h s2 s1 hrinv μ
    have h' := h.1 s2' htr
    obtain ⟨ s1', h' ⟩ := h'
    exists s1'

/-- The inverse of a weak bisimulation is a weak bisimulation. -/
theorem WeakBisimulation.inv [HasTau Label] (lts : LTS State Label)
  (r : State → State → Prop) (h : WeakBisimulation lts r) :
  WeakBisimulation lts (Relation.inv r) := by
  apply WeakBisimulation.toSwBisimulation at h
  have h' := SWBisimulation.inv lts r h
  apply SWBisimulation.toWeakBisimulation at h'
  exact h'

/-- sw-bisimilarity is symmetric. -/
theorem SWBisimilarity.symm [HasTau Label] (lts : LTS State Label) (h : s1 ≈sw[lts] s2) : s2 ≈sw[lts] s1 := by
  obtain ⟨r, hr, hrh⟩ := h
  exists (Relation.inv r)
  constructor
  case left =>
    simp only [Relation.inv, flip]
    exact hr
  case right =>
    apply SWBisimulation.inv lts r hrh

/-- Weak bisimilarity is symmetric. -/
theorem WeakBisimilarity.symm [HasTau Label] (lts : LTS State Label) (h : s1 ≈[lts] s2) : s2 ≈[lts] s1 := by
  rw [WeakBisimilarity.weakBisim_eq_swBisim]
  rw [WeakBisimilarity.weakBisim_eq_swBisim] at h
  apply SWBisimilarity.symm lts h

/-- The composition of two weak bisimulations is a weak bisimulation. -/
theorem WeakBisimulation.comp
  [HasTau Label]
  (lts : LTS State Label)
  (r1 r2 : State → State → Prop) (h1 : WeakBisimulation lts r1) (h2 : WeakBisimulation lts r2) :
  WeakBisimulation lts (Relation.Comp r1 r2) := by
  simp_all only [WeakBisimulation]
  intro s1 s2 hrc μ
  constructor
  case left =>
    intro s1' htr
    rcases hrc with ⟨sb, hr1, hr2⟩
    specialize h1 s1 sb hr1 μ
    specialize h2 sb s2 hr2 μ
    have h1' := h1.1 s1' htr
    obtain ⟨s1'', h1'tr, h1'⟩ := h1'
    have h2' := h2.1 s1'' h1'tr
    obtain ⟨s2'', h2'tr, h2'⟩ := h2'
    exists s2''
    constructor
    · exact h2'tr
    · exists s1''
  case right =>
    intro s2' htr
    rcases hrc with ⟨sb, hr1, hr2⟩
    specialize h1 s1 sb hr1 μ
    specialize h2 sb s2 hr2 μ
    have h2' := h2.2 s2' htr
    obtain ⟨s2'', h2'tr, h2'⟩ := h2'
    have h1' := h1.2 s2'' h2'tr
    obtain ⟨s1'', h1'tr, h1'⟩ := h1'
    exists s1''
    constructor
    · exact h1'tr
    · exists s2''

/-- The composition of two sw-bisimulations is an sw-bisimulation. -/
theorem SWBisimulation.comp
  [HasTau Label]
  (lts : LTS State Label)
  (r1 r2 : State → State → Prop) (h1 : SWBisimulation lts r1) (h2 : SWBisimulation lts r2) :
  SWBisimulation lts (Relation.Comp r1 r2) := by
  apply SWBisimulation.toWeakBisimulation at h1
  apply SWBisimulation.toWeakBisimulation at h2
  apply (WeakBisimulation.iff_swBisimulation lts (Relation.Comp r1 r2)).1
  apply WeakBisimulation.comp lts r1 r2 h1 h2

/-- Weak bisimilarity is transitive. -/
theorem WeakBisimilarity.trans
  [HasTau Label] {s1 s2 s3 : State} (lts : LTS State Label) (h1 : s1 ≈[lts] s2) (h2 : s2 ≈[lts] s3) :
  s1 ≈[lts] s3 := by
  obtain ⟨r1, hr1, hr1b⟩ := h1
  obtain ⟨r2, hr2, hr2b⟩ := h2
  exists Relation.Comp r1 r2
  constructor
  case left =>
    exists s2
  case right =>
    apply WeakBisimulation.comp lts r1 r2 hr1b hr2b

/-- sw-bisimilarity is transitive. -/
theorem SWBisimilarity.trans
  [HasTau Label] {s1 s2 s3 : State} (lts : LTS State Label) (h1 : s1 ≈sw[lts] s2) (h2 : s2 ≈sw[lts] s3) :
  s1 ≈sw[lts] s3 := by
  rw [← (WeakBisimilarity.weakBisim_eq_swBisim lts)] at *
  apply WeakBisimilarity.trans lts h1 h2

/-- Weak bisimilarity is an equivalence relation. -/
theorem WeakBisimilarity.eqv [HasTau Label] {lts : LTS State Label} :
  Equivalence (WeakBisimilarity lts) := {
    refl := WeakBisimilarity.refl lts
    symm := WeakBisimilarity.symm lts
    trans := WeakBisimilarity.trans lts
  }

/-- SW-bisimilarity is an equivalence relation. -/
theorem SWBisimilarity.eqv [HasTau Label] {lts : LTS State Label} :
  Equivalence (SWBisimilarity lts) := {
    refl := SWBisimilarity.refl lts
    symm := SWBisimilarity.symm lts
    trans := SWBisimilarity.trans lts
  }

end WeakBisimulation
