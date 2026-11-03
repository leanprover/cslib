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
sequence, then deleting the symbols after the first cell through the second preserves the storage
of every configuration of the path away from the two cells and the cells between them. This
property is the main ingredient in the proof of `SPACE(o(log log n)) = SPACE(1)`.

The proof idea follows [Katz2007], §1.2, Theorem 4.

## Design

Collapsing the deleted cells onto the first cell maps a step that stays on one retained side to a
step on the shortened input. The image forgets the output: the machine never reads it, and the
shortened run skips the output written in the deleted cells, so paired visits to the two endpoints
have equal storages but possibly different outputs. Their images are equal configurations of the
machine with its output writes erased, whose run on the shortened input thus reaches the image of
every configuration outside the cut.

## Main definitions

* `MultiTapeNTM.RunPath.visits`: the indices of the running configurations reading a position.
* `MultiTapeNTM.RunPath.visitSequence`: the storages at those indices, in chronological order.
* `InputCut`: an ordered pair of input-symbol indices describing the endpoints of a deletion.
* `InputCut.shortened`: the input with the symbols after the first endpoint through the second
  deleted.
* `InputCut.SameSide`: two input-head positions on one retained side of the cut.

## Main results

* `MultiTapeNTM.RunPath.storage_injOn_visits`: distinct running visits to a position in a path that
  ends halted have distinct storages.
* `InputCut.exists_storage_eq`: equal boundary symbols and visit sequences preserve the storage of
  every configuration of the path outside the endpoints and the cells between them.
* `MultiTapeTM.exists_shorter_input_storage`: a sufficiently long input has a shorter input reaching
  any storage of a halting computation path in bounded space.

## References

* [Jonathan Katz, *Notes on Complexity Theory, Lecture 5*][Katz2007],
  §1.2, Theorem 4, pp. 5-2–5-4.
-/

@[expose] public section

namespace Turing

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}

namespace MultiTapeTM

/-- `tm` with its output writes erased. A machine never reads its output tape, so the erased machine
takes the same steps up to the output. -/
private noncomputable def eraseOutput (tm : MultiTapeTM k Symbol State) :
    MultiTapeTM k Symbol State :=
  tm.adapt { read := id, action := fun _ a => { a with output := none } }

/-- Erasing the output preserves steps, so it maps run paths of `tm` to run paths of
`tm.eraseOutput`. -/
private noncomputable def eraseOutputHom (tm : MultiTapeTM k Symbol State) :
    (tm.stepRel input).Hom (tm.eraseOutput.stepRel input) :=
  follows_adapt.stepHom (fun c => { c with output := [] }) (fun _ => Option.map_id_apply)
    (fun _ => rfl) fun _ _ => by simp [Action.apply]

end MultiTapeTM

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
  refine injOn_running (tm := tm.eraseOutput) (p.map tm.eraseOutputHom) h hi.2 hj.2 ?_
  simp only [Cfg.storage, Storage.mk.injEq] at hij
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
    cut.inputPos (moveInputPos p m) = moveInputPos (cut.inputPos p) m :=
  Fin.ext <| by grind [SameSide, inputPos, left, right, SignType.cast, val_moveInputPos_eq,
    cut.fst_le_snd, cut.length_shortened_add]

/-- A configuration on the original input, seen on the shortened input with its output erased. -/
private def cfg (c : Cfg k Symbol State input) : Cfg k Symbol State cut.shortened :=
  ⟨c.state, cut.inputPos c.inputPos, c.workTapes, c.workTapePos, []⟩

/-- Outside the cells strictly between the endpoints, the collapsed configuration reads the same
symbol when the endpoints carry the same symbol. -/
private lemma inputSymbol_cfg (hsym : input[cut.fst] = input[cut.snd])
    {c : Cfg k Symbol State input} (hp : c.inputPos.val ∉ Set.Ioo cut.left cut.right) :
    (cut.cfg c).inputSymbol = c.inputSymbol := by
  have he {l : List Symbol} (c : Cfg k Symbol State l) :
      c.inputSymbol = if c.inputPos.val = 0 then none else l[c.inputPos.val - 1]? := by
    grind [Cfg.inputSymbol]
  have hb : input[cut.left - 1]? = input[cut.right - 1]? := by
    simpa [left, right, Fin.getElem_fin] using congrArg some hsym
  simp only [Set.mem_Ioo, he, cfg, inputPos, shortened, List.getElem?_append, List.length_take,
    List.getElem?_take, List.getElem?_drop] at *
  grind [left, right, cut.fst_le_snd, Fin.le_def]

variable {tm : MultiTapeTM k Symbol State}

/-- When the endpoints carry the same symbol, collapsing the cut maps a step on either retained side
to a step on the shortened input of the machine with its output erased. -/
private lemma step_cfg (hsym : input[cut.fst] = input[cut.snd]) {c c' : Cfg k Symbol State input}
    (hstep : tm.Step c c') (hside : cut.SameSide c.inputPos c'.inputPos) :
    tm.eraseOutput.step (cut.cfg c) = cut.cfg c' :=
  MultiTapeTM.step_iff.mp <| MultiTapeTM.follows_adapt.step cut.cfg hstep Option.map_id_apply
    (HeadSymbols.ext (cut.inputSymbol_cfg hsym (by
      rw [Set.mem_Ioo]; unfold SameSide at hside; omega)) rfl)
    fun _ ↦ by rintro rfl; exact Cfg.ext rfl (cut.inputPos_moveInputPos hside).symm rfl rfl rfl

/-! ### Simulating a computation path on the shortened input -/

open MultiTapeNTM MultiTapeNTM.RunPath

/-- The image of `c` on the shortened input appears in the run of the machine with its output
erased. -/
private abbrev Reached (tm : MultiTapeTM k Symbol State) (c : Cfg k Symbol State input) : Prop :=
  ∃ t, tm.eraseOutput.runFrom (tm.initCfg cut.shortened) t = cut.cfg c

/-- The image of the initial configuration is reached. -/
private lemma reached_head {p : tm.ComputationPath input} : cut.Reached tm p.head :=
  ⟨0, by
    rw [p.head_eq]
    exact Cfg.ext rfl (Fin.ext (by
      simp [MultiTapeTM.runFrom, cfg, inputPos, Cfg.init, left, right])) rfl rfl rfl⟩

/-- The running visits to the two endpoints, paired in chronological order, with the same image on
the shortened input. -/
private structure Pairing (p : tm.RunPath input) where
  /-- The `n`-th visit to the left endpoint is paired with the `n`-th visit to the right one. -/
  orderIso : p.visits cut.left ≃o p.visits cut.right
  /-- Paired visits have the same image on the shortened input. -/
  cfg_eq (u : p.visits cut.left) : cut.cfg (p u.val) = cut.cfg (p (orderIso u).val)

/-- Equal visit sequences pair the visits of the same index, which have equal storages. -/
private def pairing {p : tm.RunPath input}
    (hseq : p.visitSequence cut.left = p.visitSequence cut.right) : cut.Pairing p := by
  have hcard : (p.visits cut.right).card = (p.visits cut.left).card := by
    simpa [visitSequence] using congrArg List.length hseq.symm
  let l := (p.visits cut.left).orderIsoOfFin rfl
  let r := (p.visits cut.right).orderIsoOfFin hcard
  refine ⟨l.symm.trans r, fun u ↦ ?_⟩
  obtain ⟨n, rfl⟩ := l.surjective u
  have hs : (p (l n)).storage = (p (r n)).storage := by
    simpa [visitSequence, hcard, l, r, Finset.coe_orderIsoOfFin_apply,
      Finset.orderEmbOfFin_apply] using congrArg (·[n.val]?) hseq
  have hl := (mem_visits.mp (l n).property).1
  have hr := (mem_visits.mp (r n).property).1
  simp only [Cfg.storage, Storage.mk.injEq, OrderIso.trans_apply, OrderIso.symm_apply_apply] at hs ⊢
  exact Cfg.ext hs.1 (Fin.ext (by grind [cfg, inputPos, left, right, cut.fst_le_snd, Fin.le_def]))
    hs.2.1 hs.2.2 rfl

variable {cut} (hsym : input[cut.fst] = input[cut.snd])
include hsym

/-- A step on a retained side extends the run on the shortened input by one step. -/
private lemma Reached.step {c c' : Cfg k Symbol State input} (h : cut.Reached tm c)
    (hstep : tm.Step c c') (hside : cut.SameSide c.inputPos c'.inputPos) : cut.Reached tm c' :=
  let ⟨t, ht⟩ := h
  ⟨t + 1, by rw [MultiTapeTM.runFrom, Function.iterate_succ_apply', ← MultiTapeTM.runFrom, ht,
    cut.step_cfg hsym hstep hside]⟩

/-- From `a` up to the next running visit `v` to `pos`, the path stays on the side of `pos` where
it is at `a`, so the image of `p a` reaches that of `p v`. -/
private lemma Reached.slice {p : tm.RunPath input} {pos : ℕ} {a : Fin (p.length + 1)}
    {v : p.visits pos} (hfirst : IsLeast {w : p.visits pos | a ≤ w.val} v)
    (hside : ((p a).inputPos.val ≤ pos ∧ pos ≤ cut.left) ∨
      (pos ≤ (p a).inputPos.val ∧ cut.right ≤ pos))
    (h : cut.Reached tm (p a)) : cut.Reached tm (p v.val) := by
  obtain ⟨hav, hnext⟩ := hfirst
  suffices ∀ j, a ≤ j → j ≤ v.val → (((p j).inputPos.val ≤ pos ∧ pos ≤ cut.left) ∨
      (pos ≤ (p j).inputPos.val ∧ cut.right ≤ pos)) ∧ cut.Reached tm (p j) from
    (this v.val hav le_rfl).2
  intro j haj hjv
  induction j using Fin.induction with
  | zero => obtain rfl := Fin.le_zero_iff.mp haj; exact ⟨hside, h⟩
  | succ j ih =>
    rcases haj.eq_or_lt with rfl | haj
    · exact ⟨hside, h⟩
    have hj : j.castSucc < v.val := Fin.castSucc_lt_succ.trans_le hjv
    obtain ⟨hs, hr⟩ := ih (Fin.le_castSucc_iff.mpr haj) hj.le
    have hne : (p j.castSucc).inputPos.val ≠ pos := fun hp ↦
      (hnext (a := ⟨_, mem_visits.mpr ⟨hp, mt (p.halted_mono hj.le) (mem_visits.mp v.2).2⟩⟩)
        (Fin.le_castSucc_iff.mpr haj)).not_gt hj
    have hm := abs_le.mp (Step.inputPos_le (p.step j))
    exact ⟨by omega, hr.step hsym (p.step j) (by unfold SameSide; omega)⟩

/-- Between consecutive running visits `u ⋖ v` to `pos`, the path continues on the side its first
step enters, so the image of the visit `u` reaches that of `v`. -/
private lemma Reached.covBy {p : tm.RunPath input} {pos : ℕ} {u v : p.visits pos} (huv : u ⋖ v)
    (h : cut.Reached tm (p u.val))
    (hside : ((tm.step (p u.val)).inputPos.val ≤ pos ∧ pos ≤ cut.left) ∨
      (pos ≤ (tm.step (p u.val)).inputPos.val ∧ cut.right ≤ pos)) :
    cut.Reached tm (p v.val) := by
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
    ← cut.inputSymbol_cfg hsym (Set.notMem_Ioo_of_le hl.1.le), he,
    cut.inputSymbol_cfg hsym (Set.notMem_Ioo_of_ge hr.ge),
    hw]
  grind [val_moveInputPos_eq, SignType.cast]

/-- Every running visit to the left endpoint is reached, by induction over the visits. -/
private lemma Pairing.reached {p : tm.ComputationPath input} (e : cut.Pairing p.toRunPath)
    (u : visits p.toRunPath cut.left) : cut.Reached tm (p u.val) := by
  induction u using WellFoundedLT.induction with | ind u ih =>
  by_cases hu : IsMin u
  · exact Reached.slice hsym ⟨Fin.zero_le _, fun w _ => (le_total u w).elim id (hu ·)⟩
      (.inl ⟨by simp [show p 0 = _ from p.head_eq, left], le_rfl⟩) (reached_head cut)
  obtain ⟨w, hwu⟩ := not_isMin_iff.mp hu
  obtain ⟨v, -, hvu⟩ := exists_le_covBy_of_lt hwu
  rcases e.step_sides hsym v with hl | hr
  · exact Reached.covBy hsym hvu (ih v hvu.lt) (.inl ⟨hl, le_rfl⟩)
  · have := ih v hvu.lt
    rw [Reached, e.cfg_eq] at this ⊢
    exact Reached.covBy hsym ((apply_covBy_apply_iff e.orderIso).mpr hvu) this (.inr ⟨hr, le_rfl⟩)

/-- Every configuration outside the endpoints and the cells between them is reached, by induction
over the path: its predecessor is a visit to an endpoint or outside them too. A configuration that
halts at an endpoint may be entered from the deleted cells. -/
private lemma Pairing.reached_of_mem {p : tm.ComputationPath input} (e : cut.Pairing p.toRunPath)
    {c : Cfg k Symbol State input} (hc : c ∈ p)
    (hout : c.inputPos.val ∉ Set.Icc cut.left cut.right) : cut.Reached tm c := by
  obtain ⟨t, rfl⟩ := hc
  induction t using Fin.induction with
  | zero => exact reached_head cut
  | succ t ih =>
    rw [Set.mem_Icc] at hout ih
    have hm := abs_le.mp (Step.inputPos_le (p.step t))
    have hprev : cut.Reached tm (p t.castSucc) := by
      by_cases hb : (p t.castSucc).inputPos.val = cut.left ∨ (p t.castSucc).inputPos.val = cut.right
      · have ht : ¬(p t.castSucc).Halted := fun h ↦ by
          grind [left, right, cut.fst_le_snd, Fin.le_def, (step_of_halt h).mp (p.step t)]
        rcases hb with hb | hb
        · exact e.reached hsym ⟨_, mem_visits.mpr ⟨hb, ht⟩⟩
        · have := e.reached hsym (e.orderIso.symm ⟨_, mem_visits.mpr ⟨hb, ht⟩⟩)
          rwa [Reached, e.cfg_eq, OrderIso.apply_symm_apply] at this
      · exact ih (by omega)
    exact hprev.step hsym (p.step t) (by unfold SameSide; omega)

omit hsym in
variable (cut) in
/-- **Input shortening.** If the endpoints of the cut carry the same symbol and a computation path
visits them with the same storages, every configuration of the path outside the endpoints and the
cells between them has its storage reached on the shortened input. -/
theorem exists_storage_eq (hsym : input[cut.fst] = input[cut.snd])
    {path : tm.ComputationPath input}
    (hseq : visitSequence path.toRunPath cut.left = visitSequence path.toRunPath cut.right)
    {c : Cfg k Symbol State input} (hc : c ∈ path)
    (hout : c.inputPos.val ∉ Set.Icc cut.left cut.right) :
    ∃ q : tm.ComputationPath cut.shortened, q.last.storage = c.storage := by
  obtain ⟨t, ht⟩ := (cut.pairing hseq).reached_of_mem hsym hc hout
  exact ⟨.ofDeterministic tm cut.shortened t, congrArg Cfg.storage
    ((MultiTapeTM.runFrom_map tm.eraseOutputHom (tm.initCfg cut.shortened) t).symm.trans ht)⟩

end InputCut

namespace MultiTapeTM

variable {tm : MultiTapeTM k Symbol State}

open MultiTapeNTM MultiTapeNTM.RunPath

/-- **Input shortening.** A sufficiently long input has a shorter input on which a computation path
reaches any storage of a halting computation path in space `s`: two cells on the same side of the
storage carry the same symbol and visit sequence, and the cut between them avoids it. -/
theorem exists_shorter_input_storage [Fintype Symbol] [Fintype State] {s : ℕ}
    {path : tm.ComputationPath input} (hs : path.space ≤ s) (hhalt : path.last.Halted)
    (hlen : 3 * Fintype.card Symbol *
      (storageBound Symbol State k s + 1) ^ storageBound Symbol State k s < input.length)
    {d : Cfg k Symbol State input} (hd : d ∈ path) :
    ∃ input' : List Symbol, input'.length < input.length ∧
      ∃ q : tm.ComputationPath input', q.last.storage = d.storage := by
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
  -- Record the side of `d`, the input symbol, and the bounded visit sequence.
  let f (j : Fin input.length) :
      Ordering × Symbol × (Fin B → Option (BoundedStorage Symbol State w)) :=
    (compare (j.val + 1) d.inputPos.val, input[j],
      fun n ↦ ((visitSequence P (j.val + 1))[n.val]?).map (·.toBounded w))
  have hsig : Fintype.card (Ordering × Symbol × (Fin B → Option (BoundedStorage Symbol State w))) <
      input.length := by
    rw [Fintype.card_prod, Fintype.card_prod, show Fintype.card Ordering = 3 by decide,
      Fintype.card_fun, Fintype.card_option, Fintype.card_fin, ← mul_assoc]
    calc
      _ ≤ 3 * Fintype.card Symbol * (B + 1) ^ B := by gcongr; omega
      _ < input.length := hlen
  obtain ⟨a, b, hab, hf⟩ : ∃ a b, a < b ∧ f a = f b := by
    obtain ⟨a, b, hne, hf⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by simpa using hsig)
    grind
  obtain ⟨hside, hsym, hseq⟩ := (by simpa only [f, Prod.mk.injEq] using hf)
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
  have hout : d.inputPos.val ∉ Set.Icc cut.left cut.right := by
    cases h : compare (a.val + 1) d.inputPos.val <;> rw [h, eq_comm] at hside
    · exact Set.notMem_Icc_of_gt (compare_lt_iff_lt.mp hside)
    · rw [compare_eq_iff_eq] at h hside
      omega
    · exact Set.notMem_Icc_of_lt (compare_gt_iff_gt.mp h)
  refine ⟨cut.shortened, ?_, cut.exists_storage_eq hsym hseq' hd hout⟩
  have := cut.length_shortened_add
  change cut.shortened.length + (b.val + 1 - (a.val + 1)) = input.length at this
  omega

end MultiTapeTM

end Turing
