/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Init
public import Cslib.Foundations.Data.OmegaSequence.Flatten
public import Cslib.Foundations.Semantics.FLTS.Basic
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

@[expose] public section

/-!
# Labelled Transition System (LTS)

A Labelled Transition System (`LTS`) models the observable behaviour of the possible states of a
system. They are particularly popular in the fields of concurrency theory, logic, and programming
languages.

## Main definitions

- `LTS` is a structure for labelled transition systems, consisting of a labelled transition
relation `Tr` between states. We follow the style and conventions in [Sangiorgi2011].

- `LTS.MTr` extends the transition relation of any LTS to a multistep transition relation,
formalising the inference system and admissible rules for such relations in [Montesi2023].

- Definitions for all the common classes of LTSs: image-finite, finitely branching, finite-state,
finite, and deterministic.

## Main statements

- A series of results on `LTS.MTr` that allow for obtaining and composing multistep transitions in
different ways.

- `LTS.deterministic_imageFinite`: every deterministic LTS is also image-finite.

- `LTS.finiteState_imageFinite`: every finite-state LTS is also image-finite.

- `LTS.finiteState_finitelyBranching`: every finite-state LTS is also finitely-branching, if the
type of labels is finite.

## References

* [F. Montesi, *Introduction to Choreographies*][Montesi2023]
* [D. Sangiorgi, *Introduction to Bisimulation and Coinduction*][Sangiorgi2011]
-/

namespace Cslib

universe u v

/--
A Labelled Transition System (LTS) for a type of states (`State`) and a type of transition
labels (`Label`) consists of a labelled transition relation (`Tr`).
-/
structure LTS (State : Type u) (Label : Type v) where
  /-- The transition relation. -/
  Tr : State → Label → State → Prop

/-- Returns the relation that relates all states `s1` and `s2` via a fixed transition label `μ`. -/
def LTS.Tr.toRelation (lts : LTS State Label) (μ : Label) : State → State → Prop :=
  fun s1 s2 => lts.Tr s1 μ s2

/-- Any homogeneous relation can be seen as an LTS where all transitions have the same label. -/
def Relation.toLTS [DecidableEq Label] (r : State → State → Prop) (μ : Label) :
  LTS State Label where
  Tr := fun s1 μ' s2 => if μ' = μ then r s1 s2 else False

section MultiStep

/-! ## Multistep transitions and executions with finite traces

This section treats executions with a finite number of steps.
-/

variable {State : Type u} {Label : Type v} (lts : LTS State Label)

/--
Definition of a multistep transition.

(Implementation note: compared to [Montesi2023], we choose stepL instead of stepR as fundamental
rule. This makes working with lists of labels more convenient, because we follow the same
construction. It is also similar to what is done in the `SimpleGraph` library in mathlib.)
-/
@[scoped grind]
inductive LTS.MTr (lts : LTS State Label) : State → List Label → State → Prop where
  | refl {s : State} : lts.MTr s [] s
  | stepL {s1 : State} {μ : Label} {s2 : State} {μs : List Label} {s3 : State} :
    lts.Tr s1 μ s2 → lts.MTr s2 μs s3 →
    lts.MTr s1 (μ :: μs) s3

/-- Any transition is also a multistep transition. -/
@[scoped grind →]
theorem LTS.MTr.single {s1 : State} {μ : Label} {s2 : State} :
  lts.Tr s1 μ s2 → lts.MTr s1 [μ] s2 := by
  intro h
  apply LTS.MTr.stepL
  · exact h
  · apply LTS.MTr.refl

/-- Any multistep transition can be extended by adding a transition. -/
theorem LTS.MTr.stepR {s1 : State} {μs : List Label} {s2 : State} {μ : Label} {s3 : State} :
  lts.MTr s1 μs s2 → lts.Tr s2 μ s3 → lts.MTr s1 (μs ++ [μ]) s3 := by
  intro h1 h2
  induction h1
  case refl s1' => exact LTS.MTr.single lts h2
  case stepL s1' μ' s2' μs' s3' h1' h3 ih =>
    apply LTS.MTr.stepL
    · exact h1'
    · apply ih h2

/-- Multistep transitions can be composed. -/
@[scoped grind <=]
theorem LTS.MTr.comp {s1 : State} {μs1 : List Label} {s2 : State} {μs2 : List Label} {s3 : State} :
  lts.MTr s1 μs1 s2 → lts.MTr s2 μs2 s3 →
  lts.MTr s1 (μs1 ++ μs2) s3 := by
  intro h1 h2
  induction h1
  case refl => assumption
  case stepL s1 μ s' μs1' s'' h1' h3 ih  =>
    apply LTS.MTr.stepL
    · exact h1'
    · apply ih h2

/-- Any 1-sized multistep transition implies a transition with the same states and label. -/
@[scoped grind .]
theorem LTS.MTr.single_invert (s1 : State) (μ : Label) (s2 : State) :
  lts.MTr s1 [μ] s2 → lts.Tr s1 μ s2 := by
  intro h
  cases h
  case stepL s1' htr hmtr =>
    cases hmtr
    exact htr

/-- In any zero-steps multistep transition, the origin and the derivative are the same. -/
@[scoped grind .]
theorem LTS.MTr.nil_eq (h : lts.MTr s1 [] s2) : s1 = s2 := by
  cases h
  rfl

/-- A finite execution, or sequence of transitions. -/
@[scoped grind =]
def LTS.IsExecution (lts : LTS State Label) (s1 : State) (μs : List Label) (s2 : State)
    (ss : List State) : Prop :=
  ∃ _ : ss.length = μs.length + 1, ss[0] = s1 ∧ ss[ss.length - 1] = s2 ∧
  ∀ k, {_ : k < μs.length} → lts.Tr ss[k] μs[k] ss[k + 1]

/-- Every execution has a start state. -/
@[scoped grind →]
theorem LTS.isExecution_nonEmpty_states (h : lts.IsExecution s1 μs s2 ss) :
    ss ≠ [] := by grind

/-- Every state has an execution of zero steps terminating in itself. -/
@[scoped grind ⇒]
theorem LTS.IsExecution.refl (lts : LTS State Label) (s : State) : lts.IsExecution s [] s [s] := by
  grind

/-- Equivalent of `MTr.stepL` for executions. -/
theorem LTS.IsExecution.stepL {lts : LTS State Label} (htr : lts.Tr s1 μ s2)
    (hexec : lts.IsExecution s2 μs s3 ss) : lts.IsExecution s1 (μ :: μs) s3 (s1 :: ss) := by grind

/-- Deconstruction of executions with `List.cons`. -/
theorem LTS.isExecution_cons_invert (h : lts.IsExecution s1 (μ :: μs) s2 (s1 :: ss)) :
    lts.IsExecution (ss[0]'(by grind)) μs s2 ss := by
  obtain ⟨_, _, _, h4⟩ := h
  exists (by grind)
  constructorm* _∧_
  · rfl
  · grind
  · intro k valid
    specialize h4 k <;> grind

open scoped LTS.IsExecution in
/-- A multistep transition implies the existence of an execution. -/
@[scoped grind →]
theorem LTS.mTr_isExecution {lts : LTS State Label} {s1 : State} {μs : List Label} {s2 : State}
    (h : lts.MTr s1 μs s2) : ∃ ss : List State, lts.IsExecution s1 μs s2 ss := by
  induction h
  case refl t =>
    use [t]
    grind
  case stepL t1 μ t2 μs t3 htr hmtr ih =>
    obtain ⟨ss', _⟩ := ih
    use t1 :: ss'
    grind

/-- Converts an execution into a multistep transition. -/
@[scoped grind →]
theorem LTS.isExecution_mTr (hexec : lts.IsExecution s1 μs s2 ss) :
    lts.MTr s1 μs s2 := by
  induction ss generalizing s1 μs
  case nil => grind
  case cons s1' ss ih =>
    let ⟨hlen, hstart, hfinal, hexec'⟩ := hexec
    have : s1' = s1 := by grind
    rw [this] at hexec' hexec
    cases μs
    · grind
    case cons μ μs =>
      specialize ih (s1 := ss[0]'(by grind)) (μs := μs)
      apply LTS.isExecution_cons_invert at hexec
      apply LTS.MTr.stepL
      · have : lts.Tr s1 μ (ss[0]'(by grind)) := by grind
        apply this
      · grind

/-- Correspondence of multistep transitions and executions. -/
@[scoped grind =]
theorem LTS.mTr_isExecution_iff : lts.MTr s1 μs s2 ↔
    ∃ ss : List State, lts.IsExecution s1 μs s2 ss := by
  grind

/-- An execution can be split at any intermediate state into two executions. -/
theorem LTS.IsExecution.split
    {lts : LTS State Label} {s t : State} {μs : List Label} {ss : List State}
    (he : lts.IsExecution s μs t ss) (n : ℕ) (hn : n ≤ μs.length) :
    lts.IsExecution s (μs.take n) (ss[n]'(by grind)) (ss.take (n + 1)) ∧
    lts.IsExecution (ss[n]'(by grind)) (μs.drop n) t (ss.drop n) := by
  have : n + (ss.length - n - 1) = ss.length - 1 := by grind
  simp [IsExecution]
  grind

/-- A multistep transition over a concatenation can be split into two multistep transitions. -/
theorem LTS.MTr.split {lts : LTS State Label} {s0 : State} {μs1 μs2 : List Label} {s2 : State}
    (h : lts.MTr s0 (μs1 ++ μs2) s2) : ∃ s1, lts.MTr s0 μs1 s1 ∧ lts.MTr s1 μs2 s2 := by
  obtain ⟨ss, h_ss⟩ := LTS.mTr_isExecution h
  obtain ⟨_, _⟩ := LTS.IsExecution.split h_ss μs1.length (by grind)
  use ss[μs1.length]'(by grind)
  grind [List.take_append]

/-- A state `s1` can reach a state `s2` if there exists a multistep transition from
`s1` to `s2`. -/
@[scoped grind =]
def LTS.CanReach (s1 s2 : State) : Prop :=
  ∃ μs, lts.MTr s1 μs s2

/-- Any state can reach itself. -/
@[scoped grind .]
theorem LTS.CanReach.refl (s : State) : lts.CanReach s s := by
  exists []
  apply LTS.MTr.refl

/-- The LTS generated by a state `s` is the LTS given by all the states reachable from `s`. -/
@[scoped grind =]
def LTS.generatedBy (s : State) : LTS {s' : State // lts.CanReach s s'} Label where
  Tr := fun s1 μ s2 => lts.CanReach s s1 ∧ lts.CanReach s s2 ∧ lts.Tr s1 μ s2

/-- Returns the relation that relates all states `s1` and `s2` via a fixed list of transition
labels `μs`. -/
def LTS.MTr.toRelation (lts : LTS State Label) (μs : List Label) : State → State → Prop :=
  fun s1 s2 => lts.MTr s1 μs s2

/-! ### Calc tactic support for MTr -/

/-- Transitions can be chained. -/
instance (lts : LTS State Label) :
  Trans
    (LTS.Tr.toRelation lts μ1)
    (LTS.Tr.toRelation lts μ2)
    (LTS.MTr.toRelation lts [μ1, μ2]) where
  trans := by
    intro s1 s2 s3 htr1 htr2
    apply LTS.MTr.single at htr1
    apply LTS.MTr.single at htr2
    apply LTS.MTr.comp lts htr1 htr2

/-- Transitions can be chained with multi-step transitions. -/
instance (lts : LTS State Label) :
  Trans
    (LTS.Tr.toRelation lts μ)
    (LTS.MTr.toRelation lts μs)
    (LTS.MTr.toRelation lts (μ :: μs)) where
  trans := by
    intro s1 s2 s3 htr1 hmtr2
    apply LTS.MTr.single at htr1
    apply LTS.MTr.comp lts htr1 hmtr2

/-- Multi-step transitions can be chained with transitions. -/
instance (lts : LTS State Label) :
  Trans
    (LTS.MTr.toRelation lts μs)
    (LTS.Tr.toRelation lts μ)
    (LTS.MTr.toRelation lts (μs ++ [μ])) where
  trans := by
    intro s1 s2 s3 hmtr1 htr2
    apply LTS.MTr.single at htr2
    apply LTS.MTr.comp lts hmtr1 htr2

/-- Multi-step transitions can be chained. -/
instance (lts : LTS State Label) :
  Trans
    (LTS.MTr.toRelation lts μs1)
    (LTS.MTr.toRelation lts μs2)
    (LTS.MTr.toRelation lts (μs1 ++ μs2)) where
  trans := by
    intro s1 s2 s3 hmtr1 hmtr2
    apply LTS.MTr.comp lts hmtr1 hmtr2

end MultiStep

section ωMultiStep

/-! ## Infinite sequences of transitions

This section treats infinite executions as ω-sequences of transitions.
-/

/-- Definition of an infinite execution, or ω-sequence of transitions. -/
@[scoped grind]
def LTS.ωTr (lts : LTS State Label) (ss : ωSequence State) (μs : ωSequence Label) :
    Prop := ∀ i, lts.Tr (ss i) (μs i) (ss (i + 1))

variable {lts : LTS State Label}

open scoped ωSequence in
/-- Any finite execution extracted from an infinite execution is valid. -/
theorem LTS.ωTr_mTr (h : lts.ωTr ss μs) {n m : ℕ} (hnm : n ≤ m) :
    lts.MTr (ss n) (μs.extract n m) (ss m) := by
  by_cases heq : n = m
  case pos => grind
  case neg =>
    cases m
    case zero => grind
    case succ m =>
      have : lts.MTr (ss n) (μs.extract n m) (ss m) := ωTr_mTr (hnm := by grind) h
      grind [MTr.comp]

open ωSequence

/-- Prepends an infinite execution with a transition. -/
theorem LTS.ωTr.cons (htr : lts.Tr s μ t) (hωtr : lts.ωTr ss μs) (hm : ss 0 = t) :
    lts.ωTr (s ::ω ss) (μ ::ω μs) := by
  intro i
  induction i <;> grind

/-- Prepends an infinite execution with a finite execution. -/
theorem LTS.ωTr.append
    (hmtr : lts.MTr s μl t) (hωtr : lts.ωTr ss μs) (hm : ss 0 = t) :
    ∃ ss', lts.ωTr ss' (μl ++ω μs) ∧ ss' 0 = s ∧ ss' μl.length = t ∧ ss'.drop μl.length = ss := by
  obtain ⟨sl, _, _, _, _⟩ := LTS.mTr_isExecution hmtr
  use sl.take μl.length ++ω ss
  split_ands
  · intro n
    by_cases n < μl.length
    · grind [get_append_left]
    · by_cases n = μl.length
      · grind [get_append_left, get_append_right']
      · grind [get_append_right', hωtr (n - μl.length - 1)]
  · grind [get_append_left]
  · grind [get_append_left]
  · grind [drop_append_of_ge_length]

open Nat in
/-- Concatenating an infinite sequence of finite executions. -/
theorem LTS.IsExecution.flatten [Inhabited Label]
    {ts : ωSequence State} {μls : ωSequence (List Label)} {sls : ωSequence (List State)}
    (hexec : ∀ k, lts.IsExecution (ts k) (μls k) (ts (k + 1)) (sls k))
    (hpos : ∀ k, (μls k).length > 0) :
    ∃ ss, lts.ωTr ss μls.flatten ∧
      ∀ k, ss.extract (μls.cumLen k) (μls.cumLen (k + 1)) = (sls k).take (μls k).length := by
  have : Inhabited State := by exact {default := ts 0}
  let segs := ωSequence.mk fun k ↦ (sls k).take (μls k).length
  have h_len : μls.cumLen = segs.cumLen := by ext k; induction k <;> grind
  have h_pos (k : ℕ) : (segs k).length > 0 := by grind [List.eq_nil_iff_length_eq_zero]
  have h_mono := cumLen_strictMono h_pos
  have h_zero := cumLen_zero (ls := segs)
  have h_seg0 (k : ℕ) : (segs k)[0]! = ts k := by grind
  use segs.flatten
  split_ands
  · intro n
    simp only [h_len, flatten_def]
    simp only [LTS.IsExecution] at hexec
    have := segment_lower_bound h_mono h_zero n
    by_cases h_n : n + 1 < segs.cumLen (segment segs.cumLen n + 1)
    · have := segment_range_val h_mono (by grind) h_n
      have : n + 1 - segs.cumLen (segment segs.cumLen n) < (μls (segment segs.cumLen n)).length :=
        by grind
      grind
    · have h1 : segs.cumLen (segment segs.cumLen n + 1) = n + 1 := by
        grind [segment_upper_bound h_mono h_zero n]
      have h2 : segment segs.cumLen (n + 1) = segment segs.cumLen n + 1 := by
        simp [← h1, segment_idem h_mono]
      have : n + 1 - segs.cumLen (segment segs.cumLen n) = (μls (segment segs.cumLen n)).length :=
        by grind
      have h3 : ts (segment segs.cumLen n + 1) =
          (sls (segment segs.cumLen n))[n + 1 - segs.cumLen (segment segs.cumLen n)]! := by
        grind
      simp [h1, h2, h_seg0, h3]
      grind
  · simp [h_len, extract_flatten h_pos, segs]

/-- Concatenating an infinite sequence of multistep transitions. -/
theorem LTS.ωTr.flatten [Inhabited Label] {ts : ωSequence State} {μls : ωSequence (List Label)}
    (hmtr : ∀ k, lts.MTr (ts k) (μls k) (ts (k + 1))) (hpos : ∀ k, (μls k).length > 0) :
    ∃ ss, lts.ωTr ss μls.flatten ∧ ∀ k, ss (μls.cumLen k) = ts k := by
  choose sls h_sls using fun k ↦ LTS.mTr_isExecution (hmtr k)
  obtain ⟨ss, h_ss, h_seg⟩ := LTS.IsExecution.flatten h_sls hpos
  use ss, h_ss
  intro k
  have h1 : 0 < (ss.extract (μls.cumLen k) (μls.cumLen (k + 1))).length := by grind
  grind [List.getElem_of_eq (h_seg k) h1]

end ωMultiStep

section Total

/-! ## Total LTS -/

open Sum ωSequence

variable {State Label : Type*} {lts : LTS State Label}

/-- An LTS is total iff every state has a `μ`-derivative for every label `μ`. -/
class LTS.Total (lts : LTS State Label) where
  /-- The condition of being total. -/
  total s μ : ∃ s', lts.Tr s μ s'

/-- Choose an FLTS that is a "sub-LTS" of a total LTS. -/
noncomputable def LTS.chooseFLTS (lts : LTS State Label) [h : lts.Total] : FLTS State Label where
  tr s μ := Classical.choose <| h.total s μ

/-- The FLTS chosen by `LTS.chooseFLTS` always provides legal transitions. -/
theorem LTS.chooseFLTS.total (lts : LTS State Label) [h : lts.Total] (s : State) (μ : Label) :
    lts.Tr s μ (lts.chooseFLTS.tr s μ) :=
  Classical.choose_spec <| h.total s μ

/-- `LTS.chooseωTr` builds an infinite execution of a total LTS from any starting state and
over any infinite sequence of labels. -/
noncomputable def LTS.chooseωTr (lts : LTS State Label) [lts.Total]
    (s : State) (μs : ωSequence Label) : ℕ → State
  | 0 => s
  | n + 1 => lts.chooseFLTS.tr (lts.chooseωTr s μs n) (μs n)

/-- If a LTS is total, then there exists an infinite execution from any starting state and
over any infinite sequence of labels. -/
theorem LTS.Total.ωTr_exists [h : lts.Total] (s : State) (μs : ωSequence Label) :
    ∃ ss, lts.ωTr ss μs ∧ ss 0 = s := by
  use lts.chooseωTr s μs
  grind [LTS.chooseωTr, LTS.chooseFLTS.total]

/-- If a LTS is total, then any finite execution can be extended to an infinite execution,
provided that the label type is inbabited. -/
theorem LTS.Total.mTr_ωTr [Inhabited Label] [ht : lts.Total] {μl : List Label} {s t : State}
    (hm : lts.MTr s μl t) : ∃ μs ss, lts.ωTr ss (μl ++ω μs) ∧ ss 0 = s ∧ ss μl.length = t := by
  let μs : ωSequence Label := .const default
  obtain ⟨ss', ho, h0⟩ := LTS.Total.ωTr_exists (h := ht) t μs
  grind [LTS.ωTr.append hm ho h0]

/-- `LTS.totalize` constructs a total LTS from any given LTS by adding a sink state. -/
def LTS.totalize (lts : LTS State Label) : LTS (State ⊕ Unit) Label where
  Tr s' μ t' := match s', t' with
    | inl s, inl t => lts.Tr s μ t
    | _, inr () => True
    | inr (), inl _ => False

/-- The LTS constructed by `LTS.totalize` is indeed total. -/
instance (lts : LTS State Label) : lts.totalize.Total where
  total _ _ := by simp [LTS.totalize]

/-- In `LTS.totalize`, there is no finite execution from the sink state to any non-sink state. -/
theorem LTS.totalize.not_right_left {μs : List Label} {t : State} :
    ¬ lts.totalize.MTr (inr ()) μs (inl t) := by
  intro h
  generalize h_s : (inr () : State ⊕ Unit) = s'
  generalize h_t : (inl t : State ⊕ Unit) = t'
  rw [h_s, h_t] at h
  induction h <;> grind [LTS.totalize]

/-- In `LTS.totalize`, the transitions between non-sink states correspond exactly to
the transitions in the original LTS. -/
@[simp]
theorem LTS.totalize.tr_left_iff {μ : Label} {s t : State} :
    lts.totalize.Tr (inl s) μ (inl t) ↔ lts.Tr s μ t := by
  simp [LTS.totalize]

/-- In `LTS.totalize`, the multistep transitions between non-sink states correspond exactly to
the multistep transitions in the original LTS. -/
@[simp]
theorem LTS.totalize.mtr_left_iff {μs : List Label} {s t : State} :
    lts.totalize.MTr (inl s) μs (inl t) ↔ lts.MTr s μs t := by
  constructor <;> intro h
  · generalize h_s : (inl s : State ⊕ Unit) = s'
    generalize h_t : (inl t : State ⊕ Unit) = t'
    rw [h_s, h_t] at h
    induction h generalizing s
    case refl _ => grind [LTS.MTr]
    case stepL t1' μ t2' μs t3' h_tr h_mtr h_ind =>
      obtain ⟨rfl⟩ := h_s
      cases t2'
      case inl t2 => grind [LTS.MTr, totalize.tr_left_iff.mp h_tr]
      case inr t2 => grind [totalize.not_right_left]
  · induction h
    case refl _ => grind [LTS.MTr]
    case stepL t1 μ t2 μs t3 h_tr h_mtr h_ind =>
      grind [LTS.MTr, totalize.tr_left_iff.mpr h_tr]

end Total

section Termination
/-! ## Definitions about termination -/

variable {State} {Label} (lts : LTS State Label) {Terminated : State → Prop}

/-- A state 'may terminate' if it can reach a terminated state. The definition of `Terminated`
is a parameter. -/
def LTS.MayTerminate (s : State) : Prop := ∃ s', Terminated s' ∧ lts.CanReach s s'

/-- A state 'is stuck' if it is not terminated and cannot go forward. The definition of `Terminated`
is a parameter. -/
def LTS.Stuck (s : State) : Prop :=
  ¬Terminated s ∧ ¬∃ μ s', lts.Tr s μ s'

end Termination

section Union
/-! ## Definitions for the unions of LTSs

Note: there is a nontrivial balance between ergonomics and generality here. These definitions might
change in the future. -/

variable {State : Type u} {Label : Type v}

/-- The union of two LTSs defined on the same types. -/
def LTS.union (lts1 lts2 : LTS State Label) : LTS State Label where
  Tr := lts1.Tr ⊔ lts2.Tr

/-- The union of two LTSs that have common supertypes for states and labels. -/
def LTS.unionSubtype
{S1 : State → Prop} {L1 : Label → Prop} {S2 : State → Prop} {L2 : Label → Prop}
[DecidablePred S1] [DecidablePred L1] [DecidablePred S2] [DecidablePred L2]
(lts1 : LTS (@Subtype State S1) (@Subtype Label L1))
(lts2 : LTS (@Subtype State S2) (@Subtype Label L2)) :
  LTS State Label where
  Tr := fun s μ s' =>
    if h : S1 s ∧ L1 μ ∧ S1 s' then
      lts1.Tr ⟨s, h.1⟩ ⟨μ, h.2.1⟩ ⟨s', h.2.2⟩
    else if h : S2 s ∧ L2 μ ∧ S2 s' then
      lts2.Tr ⟨s, h.1⟩ ⟨μ, h.2.1⟩ ⟨s', h.2.2⟩
    else
      False

/-- Lifting of an `LTS State Label` to `LTS (State ⊕ State') Label`. -/
def LTS.inl (lts : LTS State Label) :
    LTS { x : State ⊕ State' // x.isLeft } { _label : Label // True } where
  Tr s μ s' :=
    match s, s' with
    | ⟨.inl s1, _⟩, ⟨.inl s2, _⟩ => lts.Tr s1 μ s2
    | _, _ => False

/-- Lifting of an `LTS State Label` to `LTS (State' ⊕ State) Label`. -/
def LTS.inr (lts : LTS State Label) :
    LTS { x : State' ⊕ State // x.isRight } { _label : Label // True } where
  Tr s μ s' :=
    match s, s' with
    | ⟨.inr s1, _⟩, ⟨.inr s2, _⟩ => lts.Tr s1 μ s2
    | _, _ => False

/-- Union of two LTSs with the same `Label` type. The result combines the original respective state
types `State1` and `State2` into `(State1 ⊕ State2)`. -/
def LTS.unionSum (lts1 : LTS State1 Label) (lts2 : LTS State2 Label) :
    LTS (State1 ⊕ State2) Label :=
  LTS.unionSubtype lts1.inl lts2.inr

end Union

section Classes
/-!
### Classes of LTSs
-/

variable {State : Type u} {Label : Type v} (lts : LTS State Label)

/-- An lts is deterministic if a state cannot reach different states with the same transition
label. -/
@[scoped grind]
class LTS.Deterministic (lts : LTS State Label) where
  deterministic (s1 : State) (μ : Label) (s2 s3 : State) : lts.Tr s1 μ s2 → lts.Tr s1 μ s3 → s2 = s3

/-- The `μ`-image of a state `s` is the set of all `μ`-derivatives of `s`. -/
@[scoped grind =]
def LTS.image (s : State) (μ : Label) : Set State := { s' : State | lts.Tr s μ s' }

/-- The `μs`-image of a state `s`, where `μs` is a list of labels, is the set of all
`μs`-derivatives of `s`. -/
@[scoped grind =]
def LTS.imageMultistep (s : State) (μs : List Label) : Set State := { s' : State | lts.MTr s μs s' }

/-- The `μ`-image of a set of states `S` is the union of all `μ`-images of the states in `S`. -/
@[scoped grind =]
def LTS.setImage (S : Set State) (μ : Label) : Set State :=
  ⋃ s ∈ S, lts.image s μ

/-- The `μs`-image of a set of states `S`, where `μs` is a list of labels, is the union of all
`μs`-images of the states in `S`. -/
@[scoped grind =]
def LTS.setImageMultistep (S : Set State) (μs : List Label) : Set State :=
  ⋃ s ∈ S, lts.imageMultistep s μs

/-- Characterisation of `setImage` wrt `Tr`. -/
@[scoped grind =]
theorem LTS.mem_setImage {lts : LTS State Label} :
  s' ∈ lts.setImage S μ ↔ ∃ s ∈ S, lts.Tr s μ s' := by
  simp only [setImage, Set.mem_iUnion, exists_prop]
  grind

theorem LTS.tr_setImage {lts : LTS State Label} (hs : s ∈ S) (htr : lts.Tr s μ s') :
  s' ∈ lts.setImage S μ := by grind

/-- Characterisation of `setImageMultistep` with `MTr`. -/
@[scoped grind =]
theorem LTS.mem_setImageMultistep {lts : LTS State Label} :
  s' ∈ lts.setImageMultistep S μs ↔ ∃ s ∈ S, lts.MTr s μs s' := by
  simp only [setImageMultistep, Set.mem_iUnion, exists_prop]
  grind

@[scoped grind <=]
theorem LTS.mTr_setImage {lts : LTS State Label} (hs : s ∈ S) (htr : lts.MTr s μs s') :
  s' ∈ lts.setImageMultistep S μs := by grind

/-- The image of the empty set is always the empty set. -/
@[scoped grind =]
theorem LTS.setImage_empty (lts : LTS State Label) : lts.setImage ∅ μ = ∅ := by grind

@[scoped grind =]
lemma LTS.setImageMultistep_setImage_head (lts : LTS State Label) :
  lts.setImageMultistep S (μ :: μs) = lts.setImageMultistep (lts.setImage S μ ) μs := by grind

/-- Characterisation of `LTS.setImageMultistep` as `List.foldl` on `LTS.setImage`. -/
@[scoped grind _=_]
theorem LTS.setImageMultistep_foldl_setImage (lts : LTS State Label) :
  lts.setImageMultistep = List.foldl lts.setImage := by
  ext S μs s'
  induction μs generalizing S <;> grind

/-- Characterisation of membership in `List.foldl lts.setImage` with `MTr`. -/
@[scoped grind =]
theorem LTS.mem_foldl_setImage (lts : LTS State Label) :
  s' ∈ List.foldl lts.setImage S μs ↔ ∃ s ∈ S, lts.MTr s μs s' := by
  rw [← LTS.setImageMultistep_foldl_setImage]
  exact LTS.mem_setImageMultistep

/-- An lts is image-finite if all images of its states are finite. -/
@[scoped grind]
class LTS.ImageFinite [image_finite : ∀ s μ, Finite (lts.image s μ)]

/-- In a deterministic LTS, if a state has a `μ`-derivative, then it can have no other
`μ`-derivative. -/
@[scoped grind .]
theorem LTS.deterministic_not_lto [h : lts.Deterministic] :
  ∀ s μ s' s'', s' ≠ s'' → lts.Tr s μ s' → ¬lts.Tr s μ s'' := by grind

@[scoped grind _=_]
theorem LTS.deterministic_tr_image_singleton [lts.Deterministic] :
    lts.image s μ = {s'} ↔ lts.Tr s μ s' := by
  have := (lts.image s μ).eq_singleton_iff_unique_mem (a := s')
  grind

/-- In a deterministic LTS, any image is either a singleton or the empty set. -/
@[scoped grind .]
theorem LTS.deterministic_image_char [lts.Deterministic] (s : State) (μ : Label) :
  (∃ s', lts.image s μ = { s' }) ∨ (lts.image s μ = ∅) := by grind

/-- In a deterministic LTS, the image of any state-label combination is finite. -/
instance [lts.Deterministic] (s : State) (μ : Label) : Finite (lts.image s μ) := by
  have hDet := LTS.deterministic_image_char lts s μ
  cases hDet
  case inl hDet =>
    obtain ⟨s', hDet'⟩ := hDet
    simp only [hDet']
    apply Set.finite_singleton
  case inr hDet =>
    simp only [hDet]
    apply Set.finite_empty

/-- Every deterministic LTS is also image-finite. -/
instance LTS.deterministic_imageFinite [lts.Deterministic] : lts.ImageFinite := {}

/-- Every finite-state LTS is also image-finite. -/
@[scoped grind .]
instance LTS.finiteState_imageFinite [Finite State] : lts.ImageFinite := {}

/-- A state has an outgoing label `μ` if it has a `μ`-derivative. -/
def LTS.HasOutLabel (s : State) (μ : Label) : Prop :=
  ∃ s', lts.Tr s μ s'

/-- The set of outgoing labels of a state. -/
def LTS.outgoingLabels (s : State) := { μ | lts.HasOutLabel s μ }

/-- An LTS is finitely branching if it is image-finite and all states have finite sets of
outgoing labels. -/
class LTS.FinitelyBranching
  [image_finite : ∀ s μ, Finite (lts.image s μ)]
  [finite_state : ∀ s, Finite (lts.outgoingLabels s)]

/-- Every LTS with finite types for states and labels is also finitely branching. -/
@[scoped grind .]
instance LTS.finiteState_finitelyBranching [Finite State] [Finite Label] : lts.FinitelyBranching :=
  {}

/-- An LTS is acyclic if there are no infinite multistep transitions. -/
class LTS.Acyclic (lts : LTS State Label) where
  acyclic : ∃ n, ∀ s1 μs s2, lts.MTr s1 μs s2 → μs.length < n

/-- An LTS is finite if it is finite-state and acyclic.

We call this `FiniteLTS` instead of just `Finite` to avoid confusion with the standard `Finite`
class. -/
class LTS.FiniteLTS [Finite State] (lts : LTS State Label) extends lts.Acyclic

end Classes

/-! ## Weak transitions (single- and multistep) -/

section Weak

/-- A type of transition labels that includes a special 'internal' transition `τ`. -/
class HasTau (Label : Type v) where
  /-- The internal transition label, also known as τ. -/
  τ : Label

/-- Saturated transition relation. -/
inductive LTS.STr [HasTau Label] (lts : LTS State Label) : State → Label → State → Prop where
| refl : lts.STr s HasTau.τ s
| tr : lts.STr s1 HasTau.τ s2 → lts.Tr s2 μ s3 → lts.STr s3 HasTau.τ s4 → lts.STr s1 μ s4

/-- The `LTS` obtained by saturating the transition relation in `lts`. -/
@[scoped grind =]
def LTS.saturate [HasTau Label] (lts : LTS State Label) : LTS State Label where
  Tr := lts.STr

@[scoped grind _=_]
theorem LTS.saturate_tr_sTr [HasTau Label] {lts : LTS State Label} :
  lts.saturate.Tr = lts.STr := by rfl

/-- Any transition is also a saturated transition. -/
theorem LTS.STr.single [HasTau Label] (lts : LTS State Label) :
    lts.Tr s μ s' → lts.STr s μ s' := by
  intro h
  apply LTS.STr.tr LTS.STr.refl h LTS.STr.refl

/-- As `LTS.str`, but counts the number of `τ`-transitions. This is convenient as induction
metric. -/
@[scoped grind]
inductive LTS.STrN [HasTau Label] (lts : LTS State Label) :
  ℕ → State → Label → State → Prop where
  | refl : lts.STrN 0 s HasTau.τ s
  | tr :
    lts.STrN n s1 HasTau.τ s2 →
    lts.Tr s2 μ s3 →
    lts.STrN m s3 HasTau.τ s4 →
    lts.STrN (n + m + 1) s1 μ s4

/-- `LTS.str` and `LTS.strN` are equivalent. -/
@[scoped grind =]
theorem LTS.sTr_sTrN [HasTau Label] (lts : LTS State Label) :
  lts.STr s1 μ s2 ↔ ∃ n, lts.STrN n s1 μ s2 := by
  apply Iff.intro <;> intro h
  case mp =>
    induction h
    case refl =>
      exists 0
      exact LTS.STrN.refl
    case tr s1 sb μ sb' s2 hstr1 htr hstr2 ih1 ih2 =>
      obtain ⟨n1, ih1⟩ := ih1
      obtain ⟨n2, ih2⟩ := ih2
      exists (n1 + n2 + 1)
      apply LTS.STrN.tr ih1 htr ih2
  case mpr =>
    obtain ⟨n, h⟩ := h
    induction h
    case refl =>
      constructor
    case tr n s1 sb μ sb' m s2 hstr1 htr hstr2 ih1 ih2 =>
      apply LTS.STr.tr ih1 htr ih2

/-- Saturated transitions labelled by τ can be composed (weighted version). -/
@[scoped grind →]
theorem LTS.STrN.trans_τ
  [HasTau Label] (lts : LTS State Label)
  (h1 : lts.STrN n s1 HasTau.τ s2) (h2 : lts.STrN m s2 HasTau.τ s3) :
  lts.STrN (n + m) s1 HasTau.τ s3 := by
  cases h1
  case refl => grind
  case tr n1 sb sb' n2 hstr1 htr hstr2 =>
    have ih := LTS.STrN.trans_τ lts hstr2 h2
    have conc := LTS.STrN.tr hstr1 htr ih
    grind

/-- Saturated transitions labelled by τ can be composed. -/
@[scoped grind →]
theorem LTS.STr.trans_τ
  [HasTau Label] (lts : LTS State Label)
  (h1 : lts.STr s1 HasTau.τ s2) (h2 : lts.STr s2 HasTau.τ s3) :
  lts.STr s1 HasTau.τ s3 := by
  obtain ⟨n, h1N⟩ := (LTS.sTr_sTrN lts).1 h1
  obtain ⟨m, h2N⟩ := (LTS.sTr_sTrN lts).1 h2
  have concN := LTS.STrN.trans_τ lts h1N h2N
  apply (LTS.sTr_sTrN lts).2 ⟨n + m, concN⟩

/-- Saturated transitions can be appended with τ-transitions (weighted version). -/
@[scoped grind <=]
theorem LTS.STrN.append
  [HasTau Label] (lts : LTS State Label)
  (h1 : lts.STrN n1 s1 μ s2)
  (h2 : lts.STrN n2 s2 HasTau.τ s3) :
  lts.STrN (n1 + n2) s1 μ s3 := by
  cases h1
  case refl => grind
  case tr n11 sb sb' n12 hstr1 htr hstr2 =>
    have hsuffix := LTS.STrN.trans_τ lts hstr2 h2
    have n_eq : n11 + (n12 + n2) + 1 = (n11 + n12 + 1 + n2) := by omega
    rw [← n_eq]
    apply LTS.STrN.tr hstr1 htr hsuffix

/-- Saturated transitions can be composed (weighted version). -/
@[scoped grind <=]
theorem LTS.STrN.comp
  [HasTau Label] (lts : LTS State Label)
  (h1 : lts.STrN n1 s1 HasTau.τ s2)
  (h2 : lts.STrN n2 s2 μ s3)
  (h3 : lts.STrN n3 s3 HasTau.τ s4) :
  lts.STrN (n1 + n2 + n3) s1 μ s4 := by
  cases h2
  case refl =>
    apply LTS.STrN.trans_τ lts h1 h3
  case tr n21 sb sb' n22 hstr1 htr hstr2 =>
    have hprefix_τ := LTS.STrN.trans_τ lts h1 hstr1
    have hprefix := LTS.STrN.tr hprefix_τ htr hstr2
    have conc := LTS.STrN.append lts hprefix h3
    grind

/-- Saturated transitions can be composed. -/
@[scoped grind <=]
theorem LTS.STr.comp
  [HasTau Label] (lts : LTS State Label)
  (h1 : lts.STr s1 HasTau.τ s2)
  (h2 : lts.STr s2 μ s3)
  (h3 : lts.STr s3 HasTau.τ s4) :
  lts.STr s1 μ s4 := by
  obtain ⟨n1, h1N⟩ := (LTS.sTr_sTrN lts).1 h1
  obtain ⟨n2, h2N⟩ := (LTS.sTr_sTrN lts).1 h2
  obtain ⟨n3, h3N⟩ := (LTS.sTr_sTrN lts).1 h3
  have concN := LTS.STrN.comp lts h1N h2N h3N
  apply (LTS.sTr_sTrN lts).2 ⟨n1 + n2 + n3, concN⟩

open scoped LTS.STr in
/-- In a saturated LTS, the transition and saturated transition relations are the same. -/
@[scoped grind _=_]
theorem LTS.saturate_sTr_tr [hHasTau : HasTau Label] (lts : LTS State Label)
  (hμ : μ = hHasTau.τ) : lts.saturate.Tr s μ = lts.saturate.STr s μ := by
  ext s'
  apply Iff.intro <;> intro h
  case mp =>
    induction h
    case refl => constructor
    case tr s1 sb μ sb' s2 hstr1 htr hstr2 ih1 ih2 =>
      rw [hμ] at htr
      apply LTS.STr.single at htr
      rw [← LTS.saturate_tr_sTr] at htr
      grind [LTS.STr.tr]
  case mpr =>
    induction h
    case refl => constructor
    case tr s1 sb μ sb' s2 hstr1 htr hstr2 ih1 ih2 =>
      simp only [LTS.saturate] at ih1 htr ih2
      simp only [LTS.saturate]
      grind

/-- In a saturated LTS, every state is in its τ-image. -/
@[scoped grind .]
theorem LTS.mem_saturate_image_τ [HasTau Label] (lts : LTS State Label) :
  s ∈ lts.saturate.image s HasTau.τ := LTS.STr.refl

/-- The `τ`-closure of a set of states `S` is the set of states reachable by any state in `S`
by performing only `τ`-transitions. -/
@[scoped grind =]
def LTS.τClosure [HasTau Label] (lts : LTS State Label) (S : Set State) : Set State :=
  lts.saturate.setImage S HasTau.τ

end Weak

/-! ## Divergence -/

section Divergence

/-- An infinite trace is divergent if every label within it is τ. -/
def LTS.DivergentTrace [HasTau Label] (μs : ωSequence Label) := ∀ i, μs i = HasTau.τ

/-- A state is divergent if there is a divergent execution from it. -/
def LTS.Divergent [HasTau Label] (lts : LTS State Label) (s : State) : Prop :=
  ∃ ss μs, lts.ωTr ss μs ∧ ss 0 = s ∧ DivergentTrace μs

/-- If a trace is divergent, then any 'suffix' is also divergent. -/
@[scoped grind ⇒]
theorem LTS.divergentTrace_drop
  [HasTau Label] {μs : ωSequence Label}
  (h : DivergentTrace μs) (n : ℕ) :
  DivergentTrace (μs.drop n) := by
  intro m
  simp only [DivergentTrace] at h
  simp only [ωSequence.get_fun, ωSequence.drop]
  grind

/-- An LTS is divergence-free if it has no divergent state. -/
class LTS.DivergenceFree [HasTau Label] (lts : LTS State Label) where
  divergence_free : ¬∃ s, lts.Divergent s

end Divergence

meta section

open Lean Elab Meta Command Term

/-- A command to create an `LTS` from a labelled transition `α → β → α → Prop`, robust to use of
`variable `-/
elab "create_lts" lt:ident name:ident : command => do
  liftTermElabM do
    let lt ← realizeGlobalConstNoOverloadWithInfo lt
    let ci ← getConstInfo lt
    forallTelescope ci.type fun args ty => do
      let throwNotLT := throwError m!"type{indentExpr ci.type}\nis not a labelled transition"
      unless args.size ≥ 2 do
        throwNotLT
      unless ← isDefEq (← inferType args[args.size - 3]!) (← inferType args[args.size - 1]!) do
        throwNotLT
      unless (← whnf ty).isProp do
        throwError m!"expecting Prop, not{indentExpr ty}"
      let params := ci.levelParams.map .param
      let lt := mkAppN (.const lt params) args[0:args.size-3]
      let bundle ← mkAppM ``LTS.mk #[lt]
      let value ← mkLambdaFVars args[0:args.size-3] bundle
      let type ← inferType value
      addAndCompile <| .defnDecl {
        name := name.getId
        levelParams := ci.levelParams
        type
        value
        safety := .safe
        hints := Lean.ReducibilityHints.abbrev
      }
      addTermInfo' name (.const name.getId params) (isBinder := true)
      addDeclarationRangesFromSyntax name.getId name

/--
  This command adds transition notations for an `LTS`. This should not usually be called directly,
  but from the `lts` attribute.

  As an example `lts_transition_notation foo "β"` will add the notations "[⬝]⭢β" and "[⬝]↠β"

  Note that the string used will afterwards be registered as a notation. This means that if you have
  also used this as a constructor name, you will need quotes to access corresponding cases, e.g. «β»
  in the above example.
-/
syntax attrKind "lts_transition_notation" ident (str)? : command
macro_rules
  | `($kind:attrKind lts_transition_notation $lts $sym) =>
    `(
      @[nolint docBlame]
      $kind:attrKind notation3 t:39 "["μ"]⭢" $sym:str t':39 => (LTS.Tr.toRelation $lts μ) t t'
      @[nolint docBlame]
      $kind:attrKind notation3 t:39 "["μs"]↠" $sym:str t':39 => (LTS.MTr.toRelation $lts μs) t t'
     )
  | `($kind:attrKind lts_transition_notation $lts) =>
    `(
      @[nolint docBlame]
      $kind:attrKind notation3 t:39 "["μ"]⭢" t':39 => (LTS.Tr.toRelation $lts μ) t t'
      @[nolint docBlame]
      $kind:attrKind notation3 t:39 "["μs"]↠" t':39 => (LTS.MTr.toRelation $lts μs) t t'
     )

/-- This attribute calls the `lts_transition_notation` command for the annotated declaration. -/
syntax (name := lts_attr) "lts" ident (ppSpace str)? : attr

initialize Lean.registerBuiltinAttribute {
  name := `lts_attr
  descr := "Register notation for an LTS"
  add := fun decl stx _ => MetaM.run' do
    match stx with
    | `(attr | lts $lts $sym) =>
        let mut sym := sym
        unless sym.getString.endsWith " " do
          sym := Syntax.mkStrLit (sym.getString ++ " ")
        let lts := lts.getId.updatePrefix decl.getPrefix |> Lean.mkIdent
        liftCommandElabM <| Command.elabCommand (← `(create_lts $(mkIdent decl) $lts))
        liftCommandElabM <| (do
          modifyScope ({ · with currNamespace := decl.getPrefix })
          Command.elabCommand (← `(scoped lts_transition_notation $lts $sym)))
    | `(attr | lts $lts) =>
        let lts := lts.getId.updatePrefix decl.getPrefix |> Lean.mkIdent
        liftCommandElabM <| Command.elabCommand (← `(create_lts $(mkIdent decl) $lts))
        liftCommandElabM <| (do
          modifyScope ({ · with currNamespace := decl.getPrefix })
          Command.elabCommand (← `(scoped lts_transition_notation $lts)))
    | _ => throwError "invalid syntax for 'lts' attribute"
}

end

end Cslib
