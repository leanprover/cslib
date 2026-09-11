/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Automata.NA.Basic
public import Cslib.Computability.Automata.TwoWayNA.Basic
public import Cslib.Foundations.Semantics.LTS.Relation

/-! # A finite acceptor for the complement of the language of a two-way automaton

For every nondeterministic two-way automaton (`TwoWayNA`) `a`, this file constructs a
nondeterministic finite acceptor (`NA.FinAcc`) that accepts exactly the words rejected by `a`
(`TwoWayNA.complToNA`, `TwoWayNA.language_complToNA`). We follow Vardi's proof, which --
unlike Shepherdson's crossing-sequence argument -- characterises non-acceptance in a way that can
be checked by a single left-to-right sweep over the input.

This result is the main ingredient in proving equivalence of two-way and one-way automata, which
can be found in `Cslib.Computability.Languages.RegularLanguages`.

## Vardi's condition of non-acceptance

Fix a `TwoWayNA` `a` and an input word `input` of length `n`. A *rejection certificate* is a family
of subsets `cert i ⊆ State`, one for every head position `i ∈ {0, …, n}`, subject to three
conditions:

1. `cert` contains every initial state at position `0` (`IsRejectionCert.start_mem`);
2. `cert` is an invariant of the transitions of `a`: if the state `c.state` is in `cert c.pos` and
  `a` can step from the configuration `c` to the configuration `c'`, then `c'.state` is in
  `cert c'.pos` (`TwoWayNA.IsStepClosed`, `IsRejectionCert.step_closed`);
3. no state in `cert n`, i.e. at the position just past the end of the input, is accepting
   (`IsRejectionCert.accept_notMem`).

Intuitively, `cert i` over-approximates the set of states in which `a` can be while its head sits at
position `i`: conditions 1 and 2 make `cert` an inductive invariant of the reachable configurations,
and condition 3 says that this invariant rules out acceptance -- being preserved by every step, it
holds at the end of every run (`LTS.mtrInv_of_trInv`). Conversely, the reachable states
(`TwoWayNA.reachable`) themselves form the least such family, so a certificate exists exactly when
`a` rejects (`TwoWayNA.not_accepts_iff_exists_isRejectionCert`).

## The finite acceptor for the complement

The point of the reformulation is locality: `TwoWayNA.isStepClosed_iff_localOK` turns condition 2
into a condition `TwoWayNA.LocalOK` relating only `cert (i - 1)`, `cert i` and `cert (i + 1)` with
the symbol at position `i`. A finite acceptor can therefore guess the certificate while scanning the
input, keeping only the last two subsets in its state. This is `TwoWayNA.complToNA`, and
`TwoWayNA.accepts_complToNA_iff` shows that it accepts exactly the words rejected by `a`.

## Implementation notes

A rejection certificate is indexed by `ℕ` rather than by `Fin (input.length + 1)`, the type of
`TwoWayNACfg.pos`: positions past the end of the input are simply left unconstrained, which avoids
casts when the certificate is compared along a run, whose configurations carry their own input.

Where a `List (Set State)` is more convenient is `TwoWayNA.exists_accepting_mTr_iff`, which is
proved by induction on the input word and prepends a subset to the certificate at each step.
`TwoWayNA.certOfList` and `TwoWayNA.certToList` translate between the two encodings, the latter
prefixing `Set.univ` for the missing position to the left of the input, mirroring
`TwoWayNA.prevSet`.

## References

* [M. Y. Vardi, *A note on the reduction of two-way automata to one-way automata*][Vardi1989]
-/

@[expose] public section

namespace List

/-- Dropping the head of a list shifts total indexing by one. -/
@[simp]
private theorem getI_tail {α : Type*} [Inhabited α] (l : List α) (i : ℕ) :
    l.tail.getI i = l.getI (i + 1) := by
  cases l <;> simp

end List

namespace Cslib.Automata

variable {State Symbol : Type*} {a : TwoWayNA State Symbol} {input : List Symbol}

namespace TwoWayNA

/-! ## Vardi's condition of non-acceptance -/

/-- Every step of `a` on `input` out of a state that `cert` attaches to the head position lands in a
state that `cert` attaches to the new head position. The conjunct on the input restricts the
invariant to the configurations that run on `input`. -/
def IsStepClosed (a : TwoWayNA State Symbol) (input : List Symbol) (cert : ℕ → Set State) : Prop :=
  (a.toCfgNA input).TrInv (fun c => c.input = input ∧ c.state ∈ cert c.pos)

/-- A family of subsets of the state set, one for every position of the input head on `input`,
which contains all initial states, is closed under the transitions of `a`, and contains no
accepting state at the position just past the end of the input. -/
structure IsRejectionCert (a : TwoWayNA State Symbol) (input : List Symbol)
    (cert : ℕ → Set State) : Prop where
  /-- Every initial state occurs at the initial head position. -/
  start_mem : ∀ s ∈ a.start, s ∈ cert 0
  /-- The family is an invariant of the transitions of `a`. -/
  step_closed : a.IsStepClosed input cert
  /-- No accepting state occurs past the end of the input. -/
  accept_notMem : ∀ s ∈ cert input.length, s ∉ a.accept

variable {cert : ℕ → Set State}

/-- If a rejection certificate for `input` exists, then `a` does not accept `input`. -/
theorem IsRejectionCert.not_accepts (hT : a.IsRejectionCert input cert) :
    ¬ Acceptor.Accepts a input := by
  rintro ⟨μs, c, ⟨hstart, hpos, hinput⟩, c', ⟨hacc, hlast⟩, hmtr⟩
  obtain ⟨hinput', hmem⟩ := LTS.mtrInv_of_trInv hT.step_closed c μs c' hmtr
    ⟨hinput, by simpa [hpos] using hT.start_mem c.state hstart⟩
  rw [hlast, Fin.val_last, hinput'] at hmem
  exact hT.accept_notMem c'.state hmem hacc

/-- The set of states that `a` can be in while its head sits at position `i` of `input`, having
started in an initial configuration. -/
def reachable (a : TwoWayNA State Symbol) (input : List Symbol) (i : ℕ) :
    Set State :=
  {q | ∃ c, c.IsInitialForInput a input ∧
      ∃ h : i < input.length + 1,
      (a.toCfgNA input).CanReach c { input := input, pos := ⟨i, h⟩, state := q } }

/-- If `a` does not accept `input`, then its reachable states form a rejection certificate. -/
theorem isRejectionCert_reachable (h : ¬ Acceptor.Accepts a input) :
    a.IsRejectionCert input (a.reachable input) where
  start_mem s hs :=
    ⟨{ input := input, pos := ⟨0, Nat.succ_pos _⟩, state := s },
      ⟨hs, Fin.ext (by simp), rfl⟩, Nat.succ_pos _, LTS.CanReach.refl _ _⟩
  step_closed c μ c' htr := by
    rintro ⟨hc_input, c₀, hstart, hlt, hreach⟩
    have hc'_input : c'.input = input := a.toCfgNA_input_eq input c μ c' htr hc_input
    rw [TwoWayNACfg.eta hc_input hlt] at hreach
    refine ⟨hc'_input, c₀, hstart, hc'_input ▸ c'.pos.isLt, ?_⟩
    rw [TwoWayNACfg.eta hc'_input]
    exact (LTS.reflTransGen_unlabelledTr_iff _).mp
      (((LTS.reflTransGen_unlabelledTr_iff _).mpr hreach).tail ⟨μ, htr⟩)
  accept_notMem s hs hacc := by
    obtain ⟨c₀, hstart, hlt, μs, hmtr⟩ := hs
    exact h ⟨μs, c₀, hstart, _, ⟨hacc, Fin.ext (by simp)⟩, hmtr⟩

/-- A two-way automaton rejects an input exactly when a rejection certificate for it exists. -/
theorem not_accepts_iff_exists_isRejectionCert (a : TwoWayNA State Symbol)
    (input : List Symbol) :
    ¬ Acceptor.Accepts a input ↔ ∃ T, a.IsRejectionCert input T :=
  ⟨fun h => ⟨_, isRejectionCert_reachable h⟩, by rintro ⟨_, hT⟩; exact hT.not_accepts⟩

/-! ## Localising the closure condition -/

/-- The subset that `cert` attaches to the position to the left of `i`, and everything at position
`0`, which has no position to its left. -/
def leftSet (cert : ℕ → Set State) : ℕ → Set State
  | 0 => Set.univ
  | i + 1 => cert i

/-- Every move of `a` out of a state in `cur` while reading `x` lands in `left`, in `cur` or in
`right`, according to whether it moves the head to the left, keeps it in place, or moves it to the
right. -/
def LocalOK (a : TwoWayNA State Symbol) (x : Symbol) (left cur right : Set State) : Prop :=
  ∀ q ∈ cur, ∀ m q', a.Tr q x m q' →
    q' ∈ match m with | .neg => left | .zero => cur | .pos => right

/-- Closure of `cert` under the transitions of `a` is the same as local consistency of `cert` at
every position carrying an input symbol. -/
theorem isStepClosed_iff_localOK :
    a.IsStepClosed input cert ↔
      ∀ i : Fin input.length, a.LocalOK input[i] (leftSet cert i) (cert i) (cert (i + 1)) := by
  constructor
  · intro hcl i q hq m q' htr
    have hlt : (i : ℕ) < input.length := i.isLt
    cases m with
    | zero =>
      exact (hcl ⟨input, q, ⟨i, by omega⟩⟩ (input[i], SignType.zero)
        ⟨input, q', ⟨i, by omega⟩⟩ ⟨rfl, by simp, htr, by simp⟩ ⟨rfl, hq⟩).2
    | pos =>
      exact (hcl ⟨input, q, ⟨i, by omega⟩⟩ (input[i], SignType.pos)
        ⟨input, q', ⟨i + 1, by omega⟩⟩ ⟨rfl, by simp, htr, by simp⟩ ⟨rfl, hq⟩).2
    | neg =>
      obtain ⟨iv, hiv⟩ := i
      obtain _ | j := iv
      · exact Set.mem_univ q'
      · exact (hcl ⟨input, q, ⟨j + 1, by omega⟩⟩ (input[j + 1], SignType.neg)
          ⟨input, q', ⟨j, by omega⟩⟩ ⟨rfl, by simp, htr, by simp⟩ ⟨rfl, hq⟩).2
  · rintro hloc c ⟨x, m⟩ c' hstep ⟨hc_input, hmem⟩
    refine ⟨a.toCfgNA_input_eq input c (x, m) c' hstep hc_input, ?_⟩
    obtain ⟨hlt, rfl⟩ := getElem_of_tr hstep hc_input
    obtain ⟨-, -, htr, hpos⟩ := hstep
    have hthis := hloc ⟨(c.pos : ℕ), hlt⟩ c.state hmem m c'.state htr
    cases m with
    | zero =>
      have hpos' : (c'.pos : ℕ) = (c.pos : ℕ) := by simp at hpos; omega
      rwa [hpos']
    | pos =>
      have hpos' : (c'.pos : ℕ) = (c.pos : ℕ) + 1 := by simp at hpos; omega
      rwa [hpos']
    | neg =>
      simp only [SignType.neg_eq_neg_one, SignType.coe_neg_one] at hpos
      obtain ⟨j, hj⟩ : ∃ j, (c.pos : ℕ) = j + 1 := ⟨(c.pos : ℕ) - 1, by omega⟩
      have hpos' : (c'.pos : ℕ) = j := by omega
      rw [hpos']
      rwa [show ((⟨(c.pos : ℕ), hlt⟩ : Fin input.length) : ℕ) = j + 1 from hj] at hthis

/-! ## The finite acceptor for the complement -/

/-- The nondeterministic finite acceptor that guesses a rejection certificate `cert` for `a` while
scanning the input, keeping the pair `(cert (i - 1), cert i)` in its state after reading `i`
symbols.
Reading the symbol at position `i` guesses `cert (i + 1)` and checks local consistency at `i`. -/
def complToNA (a : TwoWayNA State Symbol) : NA.FinAcc (Set State × Set State) Symbol where
  Tr
    | (prev, cur), x, (prev', cur') => prev' = cur ∧ a.LocalOK x prev cur cur'
  start := {(prev, cur) | prev = Set.univ ∧ a.start ⊆ cur}
  accept := {(_, cur) | ∀ s ∈ cur, s ∉ a.accept}

/-- An accepting multistep transition of `a.complToNA` out of `(left, cur)` over `xs` is the same
thing as a list of subsets starting with `left` and `cur` that is locally consistent at every
position of `xs` and ends in a subset without accepting states. -/
theorem exists_accepting_mTr_iff (a : TwoWayNA State Symbol) (xs : List Symbol)
    (left cur : Set State) :
    (∃ f ∈ a.complToNA.accept, a.complToNA.MTr (left, cur) xs f) ↔
      ∃ cert : List (Set State), cert.getI 0 = left ∧ cert.getI 1 = cur ∧
        (∀ i, ∀ hi : i < xs.length,
          a.LocalOK xs[i] (cert.getI i) (cert.getI (i + 1)) (cert.getI (i + 2))) ∧
          ∀ s ∈ cert.getI (xs.length + 1), s ∉ a.accept := by
  induction xs generalizing left cur with
  | nil =>
    constructor
    · rintro ⟨f, hf, hmtr⟩
      rw [LTS.MTr.nil_iff] at hmtr
      subst hmtr
      exact ⟨[left, cur], by simp, by simp, by simp, by simpa [complToNA] using hf⟩
    · rintro ⟨T, h0, h1, -, hacc⟩
      exact ⟨(left, cur), by simpa [complToNA, ← h1] using hacc, by simp⟩
  | cons x xs ih =>
    constructor
    · rintro ⟨f, hf, hmtr⟩
      rw [LTS.MTr.cons_iff] at hmtr
      obtain ⟨⟨m₁, m₂⟩, ⟨rfl, hlocal⟩, hmtr⟩ := hmtr
      obtain ⟨cert, h0, h1, hloc, hacc⟩ := (ih m₁ m₂).mp ⟨f, hf, hmtr⟩
      have hlocal' : a.LocalOK x left m₁ m₂ := hlocal
      have hstep : ∀ i, ∀ hi : i < (x :: xs).length, a.LocalOK (x :: xs)[i]
          ((left :: cert).getI i) ((left :: cert).getI (i + 1)) ((left :: cert).getI (i + 2)) := by
        intro i hi
        obtain _ | i := i
        · simpa [h0, h1] using hlocal
        · simpa using hloc i (by simpa using hi)
      exact ⟨left :: cert, by simp, by simpa using h0, hstep, by simpa using hacc⟩
    · rintro ⟨cert, h0, h1, hloc, hacc⟩
      have hstep : ∀ i, ∀ hi : i < xs.length,
          a.LocalOK xs[i] (cert.tail.getI i) (cert.tail.getI (i + 1)) (cert.tail.getI (i + 2)) := by
        intro i hi
        have h := hloc (i + 1) (by simpa using hi)
        rw [List.getElem_cons_succ] at h
        simpa using h
      obtain ⟨f, hf, hmtr⟩ := (ih cur (cert.getI 2)).mpr
        ⟨cert.tail, by simpa using h1, by simp, hstep, by simpa using hacc⟩
      have hlocal : a.LocalOK x left cur (cert.getI 2) := by
        have h := hloc 0 (by simp)
        rw [List.getElem_cons_zero] at h
        simpa [h0, h1] using h
      have htr : a.complToNA.Tr (left, cur) x (cur, cert.getI 2) := ⟨rfl, hlocal⟩
      exact ⟨f, hf, LTS.MTr.cons_iff.mpr ⟨(cur, cert.getI 2), htr, hmtr⟩⟩

/-- The family of subsets carried by a list, which holds the subset for the position to the left
of `0` in front, so that position `i` is entry `i + 1` of the list. -/
def certOfList (cert : List (Set State)) (i : ℕ) : Set State :=
  cert.getI (i + 1)

/-- The subsets that `cert` attaches to the positions of the input head, as a list, prefixed by
`Set.univ` for the position to the left of `0`. -/
def certToList (input : List Symbol) (cert : ℕ → Set State) : List (Set State) :=
  Set.univ :: (List.range (input.length + 1)).map cert

/-- Entry `i + 1` of `TwoWayNA.certToList` is the subset that `cert` attaches to position `i`. -/
@[simp]
theorem getI_certToList {i : ℕ} (hi : i < input.length + 1) :
    (certToList input cert).getI (i + 1) = cert i := by
  rw [certToList, List.getI_cons_succ, List.getI_eq_getElem (hn := by simpa using hi)]
  simp

/-- `a.complToNA` accepts exactly the words that `a` rejects. -/
theorem accepts_complToNA_iff (a : TwoWayNA State Symbol) (input : List Symbol) :
    Acceptor.Accepts a.complToNA input ↔ ¬ Acceptor.Accepts a input := by
  rw [not_accepts_iff_exists_isRejectionCert]
  constructor
  · rintro ⟨s, ⟨hs, hstart⟩, f, hf, hmtr⟩
    obtain ⟨cert, h0, h1, hloc, hacc⟩ := (exists_accepting_mTr_iff a input s.1 s.2).mp ⟨f, hf, hmtr⟩
    have hstep : ∀ i : Fin input.length, a.LocalOK input[i]
        (leftSet (certOfList cert) i) (certOfList cert i) (certOfList cert (i + 1)) := by
      intro i
      obtain ⟨iv, hiv⟩ := i
      obtain _ | j := iv
      · simpa [leftSet, certOfList, h0, hs] using hloc 0 hiv
      · simpa [leftSet, certOfList] using hloc (j + 1) hiv
    exact ⟨certOfList cert,
      { start_mem := by
          intro q hq
          simpa [certOfList, h1] using hstart hq
        step_closed := isStepClosed_iff_localOK.mpr hstep
        accept_notMem := by simpa [certOfList] using hacc }⟩
  · rintro ⟨cert, hCert⟩
    have hloc := isStepClosed_iff_localOK.mp hCert.step_closed
    have hstep : ∀ i, ∀ hi : i < input.length, a.LocalOK input[i]
        ((certToList input cert).getI i) ((certToList input cert).getI (i + 1))
          ((certToList input cert).getI (i + 2)) := by
      intro i hi
      have e0 : (certToList input cert).getI i = leftSet cert i := by
        cases i with
        | zero => rfl
        | succ j => exact getI_certToList (by omega)
      have e1 : (certToList input cert).getI (i + 1) = cert i := getI_certToList (by omega)
      have e2 : (certToList input cert).getI (i + 2) = cert (i + 1) := getI_certToList (by omega)
      simpa [e0, e1, e2] using hloc ⟨i, hi⟩
    obtain ⟨f, hf, hmtr⟩ := (exists_accepting_mTr_iff a input Set.univ (cert 0)).mpr
      ⟨certToList input cert, rfl, getI_certToList (by omega), hstep,
        by simpa using hCert.accept_notMem⟩
    exact ⟨(Set.univ, cert 0), ⟨rfl, hCert.start_mem⟩, f, hf, hmtr⟩

/-- `a.complToNA` recognises the complement of the language of `a`. -/
theorem language_complToNA (a : TwoWayNA State Symbol) :
    Acceptor.language a.complToNA = (Acceptor.language a)ᶜ := by
  ext xs
  simp only [Acceptor.mem_language]
  exact accepts_complToNA_iff a xs

end TwoWayNA

end Cslib.Automata
