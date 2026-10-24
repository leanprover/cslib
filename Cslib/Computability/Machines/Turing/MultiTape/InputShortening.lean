/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/
module

public import Cslib.Computability.Machines.Turing.MultiTape.ConfigBound
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Order.Atoms.Finite
public import Mathlib.Order.Cover
public import Mathlib.Order.Interval.Basic

/-!
# Input shortening for multi-tape Turing machines

Consider a deterministic Turing machine and a computation path on an input that ends halted. For
each input cell, we record the sequence of storages (`Storage`) of the running configurations of
the path that read that cell. If two distinct cells contain the same symbol and have the same
sequence, then deleting the symbols after the first cell through the second preserves every
storage reached by a step on either retained side. This property is the main ingredient in the
proof of `SPACE(o(log log n)) = SPACE(1)`.

The proof idea follows [Katz2007], §1.2, Theorem 4.

## Design

Collapsing the deleted cells onto the first cell maps the steps that stay on one retained side to
steps on the shortened input (`InputCut.stepHom`), so it maps such run paths with `RelSeries.map`.
The image forgets the output: the machine never reads it, and paired visits to the two endpoints
have equal storages but possibly different outputs. Their images are then equal configurations of
`MultiTapeTM.eraseOutput`, so the mapped segments of the path join with `RelSeries.smash`.

## Main definitions

* `MultiTapeNTM.RunPath.visits`: the indices of the running configurations reading a position.
* `MultiTapeNTM.RunPath.visitSequence`: the storages at those indices, in chronological order.
* `InputCut`: an ordered pair of input-symbol indices describing the endpoints of a deletion.
* `InputCut.shortened`: the input with the symbols after the first endpoint through the second
  deleted.
* `InputCut.SameSide`: two input-head positions on one retained side of the cut.
* `InputCut.cfg`: a configuration seen on the shortened input, with its output erased.
* `InputCut.stepHom`: `cfg` as a homomorphism from the steps on one retained side.

## Main results

* `MultiTapeNTM.RunPath.storage_injOn_visits`: distinct running visits to a position in a path that
  ends halted have distinct storages.
* `InputCut.exists_storage_eq`: equal boundary symbols and visit sequences preserve the storage
  reached by a step on a retained side, including a step that halts.
* `MultiTapeTM.exists_shorter_input_storage`: a sufficiently long input to a machine running in
  bounded space has a shorter input reaching any storage of a halting computation path.

## References

* [Jonathan Katz, *Notes on Complexity Theory, Lecture 5*][Katz2007],
  §1.2, Theorem 4, pp. 5-2–5-4.
-/

@[expose] public section

namespace Turing

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}

namespace MultiTapeNTM.RunPath

variable {ntm : MultiTapeNTM k Symbol State}

/-- The indices at which a run path reads input position `pos` in a running configuration. -/
def visits (p : ntm.RunPath input) (pos : ℕ) : Finset (Fin (p.length + 1)) :=
  {i | (p i).inputPos.val = pos ∧ ¬(p i).Halted}

@[simp]
lemma mem_visits {p : ntm.RunPath input} {pos : ℕ} {i : Fin (p.length + 1)} :
    i ∈ p.visits pos ↔ (p i).inputPos.val = pos ∧ ¬(p i).Halted := by
  simp [visits]

/-- The storages at the running visits to `pos`, in chronological order. -/
def visitSequence (p : ntm.RunPath input) (pos : ℕ) : List (Storage Symbol State k) :=
  ((p.visits pos).sort (· ≤ ·)).map fun i ↦ (p i).storage

/-- In a deterministic path that ends halted, distinct running visits to a position have distinct
storages: they would be equal configurations of the machine with its output erased. -/
lemma storage_injOn_visits {tm : MultiTapeTM k Symbol State} (p : tm.RunPath input)
    (h : p.last.Halted) (pos : ℕ) : Set.InjOn (fun i ↦ (p i).storage) (p.visits pos) := by
  intro i hi j hj hij
  simp only [Finset.mem_coe, mem_visits] at hi hj
  refine injOn_running (tm := tm.eraseOutput) (p.map tm.toMultiTapeNTM.eraseOutputHom) h hi.2
    hj.2 ?_
  simp only [Cfg.storage, Storage.mk.injEq] at hij
  simp only [RunPath.map, RelSeries.map_apply, eraseOutputHom_apply]
  exact Cfg.ext hij.1 (Fin.ext (hi.1.trans hj.1.symm)) hij.2.1 hij.2.2 rfl

end MultiTapeNTM.RunPath

/-- An ordered pair of input-symbol indices. The cut deletes the symbols after the first
through the second. Equal endpoints give an empty deletion.
`fst` and `snd` are zero-based list indices. `left` and `right` are the corresponding
input-head positions, offset by one because position `0` is the left endmarker. -/
abbrev InputCut (input : List Symbol) := NonemptyInterval (Fin input.length)

namespace InputCut

variable (cut : InputCut input)

/-- The head position of the retained endpoint: position `0` is the left endmarker. -/
def left : ℕ := cut.fst.val + 1

/-- The head position of the right endpoint: input symbol `i` is read at position `i + 1`. -/
def right : ℕ := cut.snd.val + 1

/-- The input obtained by deleting the cells after `left` through `right`. -/
def shortened : List Symbol :=
  input.take cut.left ++ input.drop cut.right

/-- Two input positions lie on the same retained side of the cut. -/
def SameSide (p q : ℕ) : Prop :=
  (p ≤ cut.left ∧ q ≤ cut.left) ∨ (cut.right ≤ p ∧ cut.right ≤ q)

/-- Adding back the deleted cells recovers the original input length. -/
lemma length_shortened_add :
    cut.shortened.length + (cut.right - cut.left) = input.length := by
  grind [shortened, left, right, cut.fst_le_snd]

/-- Collapse the deleted cells onto the left endpoint and shift later positions left. -/
def inputPos (p : Fin (input.length + 2)) : Fin (cut.shortened.length + 2) :=
  ⟨min p.val cut.left + (p.val - cut.right), by
    have := cut.length_shortened_add
    grind [left, right, cut.fst_le_snd, Fin.le_def]⟩

/-- Collapsing the cut commutes with an input-head move that stays on one retained side. -/
lemma inputPos_moveInputPos {p : Fin (input.length + 2)} {m : SignType}
    (h : cut.SameSide p (moveInputPos p m)) :
    cut.inputPos (moveInputPos p m) = moveInputPos (cut.inputPos p) m := by
  have := val_moveInputPos_eq p m
  have := val_moveInputPos_eq (cut.inputPos p) m
  apply Fin.ext
  cases m <;> grind [SameSide, inputPos, left, right, SignType.cast,
    Fin.le_def, cut.fst_le_snd, cut.length_shortened_add]

/-- A configuration on the original input, seen on the shortened input with its output erased. -/
def cfg (c : Cfg k Symbol State input) : Cfg k Symbol State cut.shortened :=
  ⟨c.state, cut.inputPos c.inputPos, c.workTapes, c.workTapePos, []⟩

/-- Outside the deleted cells, the collapsed configuration reads the same symbol when the endpoints
carry the same symbol. -/
lemma inputSymbol_cfg (hsym : input[cut.fst] = input[cut.snd]) {c : Cfg k Symbol State input}
    (hp : c.inputPos.val ≤ cut.left ∨ cut.right ≤ c.inputPos.val) :
    (cut.cfg c).inputSymbol = c.inputSymbol := by
  have he {l : List Symbol} (c : Cfg k Symbol State l) :
      c.inputSymbol = if c.inputPos.val = 0 then none else l[c.inputPos.val - 1]? := by
    grind [Cfg.inputSymbol]
  have hb : input[cut.left - 1]? = input[cut.right - 1]? := by
    simpa [left, right, Fin.getElem_fin] using congrArg some hsym
  simp only [he, cfg, inputPos, shortened, List.getElem?_append, List.length_take,
    List.getElem?_take, List.getElem?_drop] at *
  grind [left, right, cut.fst_le_snd, Fin.le_def]

/-- The steps of `ntm` that stay on one retained side of the cut. -/
abbrev sideStepRel (ntm : MultiTapeNTM k Symbol State) :
    SetRel (Cfg k Symbol State input) (Cfg k Symbol State input) :=
  {(c, c') | ntm.Step c c' ∧ cut.SameSide c.inputPos c'.inputPos}

/-- When the endpoints carry the same symbol, collapsing the cut maps the steps on either retained
side to steps on the shortened input, with the output erased. -/
def stepHom (ntm : MultiTapeNTM k Symbol State) (hsym : input[cut.fst] = input[cut.snd]) :
    (cut.sideStepRel ntm).Hom (ntm.eraseOutput.stepRel cut.shortened) where
  toFun := cut.cfg
  map_rel' {c c'} h := by
    obtain ⟨hstep, hside⟩ := h
    change ntm.eraseOutput.Step (cut.cfg c) (cut.cfg c')
    have hsymb := cut.inputSymbol_cfg hsym (c := c) (by unfold SameSide at hside; omega)
    rcases hq : c.state with _ | q
    · obtain rfl := (MultiTapeNTM.step_of_halt hq).mp hstep
      exact (MultiTapeNTM.step_of_halt (show (cut.cfg _).Halted from hq)).mpr rfl
    · have hst : (cut.cfg c).state = some q := hq
      unfold MultiTapeNTM.Step at hstep ⊢
      simp only [hq, hst] at hstep ⊢
      obtain ⟨a, ha, rfl⟩ := hstep
      refine ⟨{ a with output := none }, ⟨a, by rwa [hsymb], rfl⟩, ?_⟩
      exact Cfg.ext rfl (cut.inputPos_moveInputPos hside) rfl rfl
        (by simp [cfg, Action.apply])

/-! ### Simulating a computation path on the shortened input -/

variable {tm : MultiTapeTM k Symbol State}

open MultiTapeNTM MultiTapeNTM.RunPath

/-- `c'` is the last configuration of a computation path on the shortened input of the machine with
its output erased. -/
private abbrev Reached (tm : MultiTapeTM k Symbol State) (c' : Cfg k Symbol State cut.shortened) :
    Prop :=
  ∃ q : tm.eraseOutput.ComputationPath cut.shortened, q.last = c'

/-- The image of the initial configuration is reached. -/
private lemma reached_head {p : tm.ComputationPath input} :
    cut.Reached tm (cut.cfg p.toRunPath.head) :=
  ⟨⟨RelSeries.singleton _ (tm.eraseOutput.initCfg cut.shortened), rfl⟩, by
    rw [p.head_eq]
    exact Cfg.ext rfl (Fin.ext (by simp [cfg, inputPos, Cfg.init, left, right])) rfl rfl rfl⟩

/-- The running visits to the two endpoints, paired in chronological order, with equal storages. -/
private structure Pairing (p : tm.RunPath input) where
  /-- The `n`-th visit to the left endpoint is paired with the `n`-th visit to the right one. -/
  orderIso : p.visits cut.left ≃o p.visits cut.right
  /-- Paired visits have equal storages. -/
  storage_eq (u : p.visits cut.left) : (p u.val).storage = (p (orderIso u).val).storage

/-- Equal visit sequences pair the visits of the same index. -/
private def pairing {p : tm.RunPath input}
    (hseq : p.visitSequence cut.left = p.visitSequence cut.right) : cut.Pairing p := by
  have hcard : (p.visits cut.right).card = (p.visits cut.left).card := by
    simpa [visitSequence] using congrArg List.length hseq.symm
  let l := (p.visits cut.left).orderIsoOfFin rfl
  let r := (p.visits cut.right).orderIsoOfFin hcard
  refine ⟨l.symm.trans r, fun u ↦ ?_⟩
  have hl : (l.symm u).val < (p.visitSequence cut.left).length := by simp [visitSequence]
  have hr : (l.symm u).val < (p.visitSequence cut.right).length := by
    simp [visitSequence, hcard]
  have he : (p.visitSequence cut.left)[(l.symm u).val] =
      (p.visitSequence cut.right)[(l.symm u).val] := by simp only [hseq]
  simp only [visitSequence, List.getElem_map] at he
  change (p (l (l.symm u)).val).storage = (p (r (l.symm u)).val).storage at he
  simpa only [OrderIso.trans_apply, l.apply_symm_apply] using he

variable {cut} in
/-- Paired visits have the same image on the shortened input. -/
private lemma Pairing.cfg_eq {p : tm.RunPath input} (e : cut.Pairing p) (u : p.visits cut.left) :
    cut.cfg (p u.val) = cut.cfg (p (e.orderIso u).val) := by
  have hl := (mem_visits.mp u.property).1
  have hr := (mem_visits.mp (e.orderIso u).property).1
  have hs := e.storage_eq u
  simp only [Cfg.storage, Storage.mk.injEq] at hs
  refine Cfg.ext hs.1 (Fin.ext ?_) hs.2.1 hs.2.2 rfl
  grind [cfg, inputPos, left, right, cut.fst_le_snd, Fin.le_def]

variable {cut} (hsym : input[cut.fst] = input[cut.snd])
include hsym

/-- A step on a retained side extends a computation path on the shortened input. -/
private lemma Reached.step {c c' : Cfg k Symbol State input} (h : cut.Reached tm (cut.cfg c))
    (hstep : tm.Step c c') (hside : cut.SameSide c.inputPos c'.inputPos) :
    cut.Reached tm (cut.cfg c') := by
  obtain ⟨q, hq⟩ := h
  have hr : (cut.cfg c, cut.cfg c') ∈ tm.eraseOutput.stepRel cut.shortened :=
    (cut.stepHom tm.toMultiTapeNTM hsym).map_rel
      (show (c, c') ∈ cut.sideStepRel _ from ⟨hstep, hside⟩)
  rw [← hq] at hr
  exact ⟨⟨q.toRunPath.snoc _ hr, (RelSeries.head_snoc ..).trans q.head_eq⟩,
    RelSeries.last_snoc q.toRunPath _ hr⟩

/-- A run path on a retained side extends a computation path on the shortened input. -/
private lemma Reached.path {p : tm.RunPath input} (h : cut.Reached tm (cut.cfg p.head))
    (hp : (∀ c ∈ p, c.inputPos.val ≤ cut.left) ∨ ∀ c ∈ p, cut.right ≤ c.inputPos.val) :
    cut.Reached tm (cut.cfg p.last) :=
  -- `p` is a series of side steps, which `stepHom` maps
  let s : RelSeries (cut.sideStepRel tm.toMultiTapeNTM) := ⟨p.length, p, fun i ↦ ⟨p.step i,
    hp.imp (fun h ↦ ⟨h _ ⟨_, rfl⟩, h _ ⟨_, rfl⟩⟩) fun h ↦ ⟨h _ ⟨_, rfl⟩, h _ ⟨_, rfl⟩⟩⟩⟩
  let ⟨q, hq⟩ := h
  ⟨⟨q.toRunPath.smash (s.map (cut.stepHom tm.toMultiTapeNTM hsym)) hq,
    (RelSeries.head_smash _).trans q.head_eq⟩, RelSeries.last_smash hq⟩

/-- From `a` up to the next running visit `v` to `pos`, the path stays on the side of `pos` where
it is at `a`, so the image of `p a` reaches that of `p v`. -/
private lemma Reached.slice {p : tm.RunPath input} {pos : ℕ} {a : Fin (p.length + 1)}
    {v : p.visits pos} (hfirst : IsLeast {w : p.visits pos | a ≤ w.val} v)
    (hside : ((p a).inputPos.val ≤ pos ∧ pos ≤ cut.left) ∨
      (pos ≤ (p a).inputPos.val ∧ cut.right ≤ pos))
    (h : cut.Reached tm (cut.cfg (p a))) : cut.Reached tm (cut.cfg (p v.val)) := by
  obtain ⟨hav, hnext⟩ := hfirst
  let s := (p.take v.val).drop ⟨a, Nat.lt_succ_of_le hav⟩
  have hs : s.head = p a := by simp [s, RelSeries.take]
  have hne (i : Fin s.length) : (s i.castSucc).inputPos.val ≠ pos := by
    intro hi
    have hi' : i.val + a.val < v.val.val := by
      have : i.val < v.val.val - a.val := i.isLt
      omega
    exact (hnext (a := ⟨⟨_, hi'.trans v.val.isLt⟩, mem_visits.mpr
      ⟨hi, p.not_halted_of_le hi'.le (mem_visits.mp v.property).2⟩⟩)
      (show a.val ≤ i.val + a.val by omega)).not_gt hi'
  simpa [s] using Reached.path hsym (p := s) (hs ▸ h) (by
    rcases hside with hl | hr
    · exact .inl fun c hc => ((inputPos_side s hne hc).1 (hs.symm ▸ hl.1)).trans hl.2
    · exact .inr fun c hc => hr.2.trans ((inputPos_side s hne hc).2 (hs.symm ▸ hr.1)))

/-- Between consecutive running visits `u ⋖ v` to `pos`, the path continues on the side its first
step enters, so the image of the visit `u` reaches that of `v`. -/
private lemma Reached.covBy {p : tm.RunPath input} {pos : ℕ} {u v : p.visits pos} (huv : u ⋖ v)
    (h : cut.Reached tm (cut.cfg (p u.val)))
    (hside : ((tm.step (p u.val)).inputPos.val ≤ pos ∧ pos ≤ cut.left) ∨
      (pos ≤ (tm.step (p u.val)).inputPos.val ∧ cut.right ≤ pos)) :
    cut.Reached tm (cut.cfg (p v.val)) := by
  have hlt : u.val.val < p.length := lt_of_lt_of_le huv.lt (Nat.lt_succ_iff.mp v.val.isLt)
  have hu := (mem_visits.mp u.property).1
  have hpi : tm.Step (p u.val) (p (⟨u.val, hlt⟩ : Fin p.length).succ) := p.step ⟨u.val, hlt⟩
  rw [MultiTapeTM.step_iff.mp hpi] at hside
  refine Reached.slice hsym ?_ hside (h.step hsym hpi (by unfold SameSide; omega))
  exact ⟨Nat.succ_le_of_lt huv.lt, fun _ hw => huv.ge_of_gt hw⟩

/-- At paired visits, the step from the left visit stays left or that from the right visit stays
right: both read the same symbol with the same storage, so they move the input head alike. -/
private lemma Pairing.step_sides {p : tm.RunPath input} (e : cut.Pairing p)
    (u : p.visits cut.left) :
    (tm.step (p u.val)).inputPos.val ≤ cut.left ∨
      cut.right ≤ (tm.step (p (e.orderIso u).val)).inputPos.val := by
  have hl := mem_visits.mp u.property
  have hr := (mem_visits.mp (e.orderIso u).property).1
  have he := e.cfg_eq u
  have hw : (p u.val).workTapeSymbols = (p (e.orderIso u).val).workTapeSymbols :=
    congrArg (·.workTapeSymbols) he
  obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp hl.2
  rw [MultiTapeTM.step_inputPos_of_state hq,
    MultiTapeTM.step_inputPos_of_state (show (p (e.orderIso u).val).state = some q from
      (congrArg Cfg.state he).symm.trans hq),
    ← cut.inputSymbol_cfg hsym (.inl hl.1.le), he, cut.inputSymbol_cfg hsym (.inr hr.ge),
    hw]
  generalize (tm.tr q _ _).inputTape = m
  have := val_moveInputPos_eq (p u.val).inputPos m
  have := val_moveInputPos_eq (p (e.orderIso u).val).inputPos m
  cases m <;> simp -failIfUnchanged [SignType.cast] at * <;> omega

/-- Every running visit to the left endpoint is reached, by induction over the visits. -/
private lemma Pairing.reached {p : tm.ComputationPath input} (e : cut.Pairing p.toRunPath)
    (u : visits p.toRunPath cut.left) : cut.Reached tm (cut.cfg (p.toRunPath u.val)) := by
  induction u using WellFoundedLT.induction with | ind u ih =>
  by_cases hu : IsMin u
  · exact Reached.slice hsym ⟨Fin.zero_le _, fun w _ => (le_total u w).elim id (hu ·)⟩
      (.inl ⟨by simp [show p.toRunPath 0 = _ from p.head_eq, left], le_rfl⟩) (reached_head cut)
  obtain ⟨w, hwu⟩ := not_isMin_iff.mp hu
  obtain ⟨v, -, hvu⟩ := exists_le_covBy_of_lt hwu
  rcases e.step_sides hsym v with hl | hr
  · exact Reached.covBy hsym hvu (ih v hvu.lt) (.inl ⟨hl, le_rfl⟩)
  · rw [e.cfg_eq]
    exact Reached.covBy hsym ((apply_covBy_apply_iff e.orderIso).mpr hvu)
      (e.cfg_eq v ▸ ih v hvu.lt) (.inr ⟨hr, le_rfl⟩)

/-- Every running configuration outside the deleted cells is reached, by induction over the
path. -/
private lemma Pairing.reached_of_not_halted {p : tm.ComputationPath input}
    (e : cut.Pairing p.toRunPath) {c : Cfg k Symbol State input} (hc : c ∈ p.toRunPath)
    (ht : ¬c.Halted) (hout : c.inputPos.val ≤ cut.left ∨ cut.right ≤ c.inputPos.val) :
    cut.Reached tm (cut.cfg c) := by
  obtain ⟨t, rfl⟩ := hc
  induction t using Fin.induction with
  | zero => exact reached_head cut
  | succ t ih =>
    by_cases hb : (p.toRunPath t.succ).inputPos.val = cut.left
    · exact e.reached hsym ⟨_, mem_visits.mpr ⟨hb, ht⟩⟩
    by_cases hb' : (p.toRunPath t.succ).inputPos.val = cut.right
    · have := e.reached hsym (e.orderIso.symm ⟨_, mem_visits.mpr ⟨hb', ht⟩⟩)
      rwa [e.cfg_eq, OrderIso.apply_symm_apply] at this
    have hm := abs_le.mp (Step.inputPos_le (p.step t))
    have hside : cut.SameSide (p.toRunPath t.castSucc).inputPos (p.toRunPath t.succ).inputPos := by
      unfold SameSide
      omega
    refine (ih (not_halted_of_le _ (Fin.castSucc_lt_succ ..).le ht) ?_).step hsym (p.step t) hside
    unfold SameSide at hside
    omega

omit hsym in
variable (cut) in
/-- **Input shortening.** If the endpoints of the cut carry the same symbol and a computation path
visits them with the same storages, a step on a retained side from a running configuration of the
path reaches the same storage on the shortened input. -/
theorem exists_storage_eq (hsym : input[cut.fst] = input[cut.snd])
    {path : tm.ComputationPath input}
    (hseq : visitSequence path.toRunPath cut.left = visitSequence path.toRunPath cut.right)
    {c : Cfg k Symbol State input} (hc : c ∈ path.toRunPath) (hrun : ¬c.Halted)
    (hside : cut.SameSide c.inputPos (tm.step c).inputPos) :
    ∃ q : tm.ComputationPath cut.shortened, q.last.storage = (tm.step c).storage := by
  obtain ⟨q, hq⟩ := ((cut.pairing hseq).reached_of_not_halted hsym hc hrun
    (by unfold SameSide at hside; omega)).step hsym (MultiTapeTM.step_iff.mpr rfl) hside
  -- the path of the same length of `tm` erases to `q`
  let p := ComputationPath.ofDeterministic tm cut.shortened q.length
  refine ⟨p, ?_⟩
  have hp := RunPath.eq_take (tm := tm.eraseOutput)
    (p := p.toRunPath.map tm.toMultiTapeNTM.eraseOutputHom) (q := q.toRunPath)
    q.head_eq.symm le_rfl
  exact (congrArg (fun r ↦ r.last.storage) hp).trans (congrArg Cfg.storage hq)

end InputCut

namespace MultiTapeTM

variable {tm : MultiTapeTM k Symbol State}

open MultiTapeNTM MultiTapeNTM.RunPath

/-- On a sufficiently long input, two cells on the same side of `pos` carry the same symbol and
visit sequence, and deleting between them shortens the input. -/
private lemma exists_inputCut [Fintype Symbol] [Fintype State] {s : ℕ}
    {path : tm.ComputationPath input} (hs : path.space ≤ s) (hhalt : path.last.Halted)
    (hlen : 2 * Fintype.card Symbol *
      (storageBound Symbol State k s + 1) ^ storageBound Symbol State k s + 1 < input.length)
    (pos : ℕ) :
    ∃ cut : InputCut input, cut.shortened.length < input.length ∧
      input[cut.fst] = input[cut.snd] ∧
      visitSequence path.toRunPath cut.left = visitSequence path.toRunPath cut.right ∧
      (cut.left < pos ↔ cut.right < pos) := by
  classical
  let P := path.toRunPath
  -- Every prefix fits in the windows given by the space of this path.
  let w := spaceUsedByTape P
  let B := storageBound Symbol State k s
  have hS (t : Fin (path.length + 1)) : (P t).storage.FitsIn w := by
    let q : tm.ComputationPath input := ⟨P.take t, by simp [P, path.head_eq]⟩
    exact Storage.FitsIn_mono
      (fun j => Finset.card_le_card (visitedByTapeHead_take_subset P t j)) q.storage_fitsIn
  have hfits {pos n : ℕ} {x} (hx : (visitSequence P pos)[n]? = some x) : x.FitsIn w := by
    obtain ⟨t, -, rfl⟩ := List.mem_map.mp (List.mem_of_getElem? hx)
    exact hS t
  have hcard : Fintype.card (BoundedStorage Symbol State w) ≤ B := card_boundedStorage_le hs
  have hlength (pos : ℕ) : (visitSequence P pos).length ≤ B := by
    simp only [visitSequence, List.length_map, Finset.length_sort]
    exact (Finset.card_le_card_of_injOn (fun t ↦ (P t).storage.toBounded w)
      (fun _ _ ↦ Finset.mem_coe.mpr (Finset.mem_univ _)) fun u hu v hv h ↦
        storage_injOn_visits P hhalt pos hu hv (Storage.toBounded_injOn w (hS u) (hS v) h)).trans
      (by simpa using hcard)
  -- Record the side of `pos`, the input symbol, and the bounded visit sequence.
  let f (j : Fin input.length) : Bool × Symbol × (Fin B → Option (BoundedStorage Symbol State w)) :=
    (decide (j.val + 1 < pos), input[j], fun n ↦ ((visitSequence P (j.val + 1))[n.val]?).map
      (·.toBounded w))
  have hsig : Fintype.card (Bool × Symbol × (Fin B → Option (BoundedStorage Symbol State w))) <
      input.length := by
    rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_bool, Fintype.card_fun,
      Fintype.card_option, Fintype.card_fin, ← mul_assoc]
    calc
      _ ≤ 2 * Fintype.card Symbol * (B + 1) ^ B := by gcongr; omega
      _ < input.length := by dsimp only [B]; omega
  obtain ⟨a, b, hab, hf⟩ : ∃ a b, a < b ∧ f a = f b := by
    obtain ⟨a, b, hne, hf⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by simpa using hsig)
    grind
  obtain ⟨hside, hsym, hseq⟩ := (by simpa only [f, Prod.mk.injEq, decide_eq_decide] using hf)
  have hseq' : visitSequence P (a.val + 1) = visitSequence P (b.val + 1) := by
    apply List.ext_getElem?'
    intro r hr
    have he := congrFun hseq ⟨r, hr.trans_le (max_le (hlength _) (hlength _))⟩
    rcases ha : (visitSequence P (a.val + 1))[r]? with _ | x <;>
      rcases hb : (visitSequence P (b.val + 1))[r]? with _ | y <;>
      simp only [ha, hb, Option.map_none, Option.map_some, reduceCtorEq, Option.some.injEq]
        at he ⊢
    exact Storage.toBounded_injOn w (hfits ha) (hfits hb) he
  let cut : InputCut input := ⟨⟨a, b⟩, hab.le⟩
  refine ⟨cut, ?_, hsym, hseq', hside⟩
  have := cut.length_shortened_add
  change cut.shortened.length + (b.val + 1 - (a.val + 1)) = input.length at this
  omega

/-- **Input shortening.** A sufficiently long input to a machine running in space `s` has a shorter
input on which a computation path reaches any storage of a halting computation path. -/
theorem exists_shorter_input_storage [Fintype Symbol] [Fintype State] {s : ℕ}
    (hs : tm.RunsInSpace input s) {path : tm.ComputationPath input} (hhalt : path.last.Halted)
    (hlen : 2 * Fintype.card Symbol *
      (storageBound Symbol State k s + 1) ^ storageBound Symbol State k s + 1 < input.length)
    {d : Cfg k Symbol State input} (hd : d ∈ path.toRunPath) :
    ∃ input' : List Symbol, input'.length < input.length ∧
      ∃ q : tm.ComputationPath input', q.last.storage = d.storage := by
  let P := path.toRunPath
  obtain ⟨j, rfl⟩ := hd
  induction j using Fin.induction with
  | zero =>
    -- the initial storage does not depend on the input
    refine ⟨[], by simp; omega, .ofDeterministic tm [] 0, ?_⟩
    change (tm.initCfg []).storage = P.head.storage
    rw [path.head_eq]
    rfl
  | succ i ih =>
  by_cases hi : (P i.castSucc).Halted
  · rw [(MultiTapeNTM.step_of_halt hi).mp (P.step i)]
    exact ih
  -- Matching cells on the same side of both head positions retain this step.
  obtain ⟨cut, hshort, hsym, hseq, hside⟩ :=
    exists_inputCut (hs path) hhalt hlen (max (P i.castSucc).inputPos.val (P i.succ).inputPos.val)
  refine ⟨cut.shortened, hshort, ?_⟩
  have hstep : tm.step (P i.castSucc) = P i.succ := step_iff.mp (P.step i)
  rw [← hstep]
  refine cut.exists_storage_eq hsym hseq ⟨_, rfl⟩ hi ?_
  have := abs_le.mp (Step.inputPos_le (P.step i))
  rw [hstep]
  unfold InputCut.SameSide
  omega

end MultiTapeTM

end Turing
