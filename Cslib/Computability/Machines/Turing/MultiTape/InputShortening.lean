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

Consider a deterministic Turing machine and a halting computation path on an input. The *crossing
sequence* at an input position is the list of storages (`Storage`) of the path at the time steps
when the input head is at that position, in chronological order.

Take two input positions `a ≤ b` that hold the same symbol and have the same crossing sequence, and
call `[a, b]` the cut. Deleting the symbols in `(a, b]` gives the *shortened input*. Every
configuration in the path with the input head outside the cut has its storage reached by the machine
on the shortened input. This is the main ingredient in the proof of
`SPACE(o(log log n)) = SPACE(1)`.

The proof idea follows [Katz2007], §1.2, Theorem 4.

## Main definitions

* `MultiTapeNTM.RunPath.visits`: the time steps at which a run path is in a configuration with its
  input head at a given position.
* `MultiTapeNTM.RunPath.crossingSequence`: the storages at those time steps, in chronological order.
* `InputCut`: a nonempty interval `[a, b]` of input positions.
* `InputCut.shortened`: the input with the symbols in `(a, b]` cut out.
* `InputCut.SameSide`: two input head positions on the same side of the cut.

## Main results

* `MultiTapeNTM.RunPath.storage_injOn_visits`: in a run path of a Turing machine that ends halted,
  the configurations at distinct time steps in `visits` have distinct storages.
* `InputCut.exists_storage_eq`: if the endpoints of the cut hold the same symbol and have the same
  crossing sequence, every configuration in the path with the input head outside the cut has its
  storage reached on the shortened input.
* `MultiTapeTM.exists_shorter_input_storage`: for a halting computation path in space `s` on a long
  enough input, every storage in the path is reached on some shorter input.

## References

* [Jonathan Katz, *Notes on Complexity Theory, Lecture 5*][Katz2007],
  §1.2, Theorem 4, pp. 5-2–5-4.
-/

@[expose] public section

namespace Turing

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}

namespace MultiTapeNTM.RunPath

variable {ntm : MultiTapeNTM k Symbol State}

/-- The times at which the run path `p` has its input head at position `pos`, leaving out halted
configurations. -/
def visits (p : ntm.RunPath input) (pos : ℕ) : Finset (Fin (p.length + 1)) :=
  {i | (p i).inputPos.val = pos ∧ ¬(p i).Halted}

@[simp]
lemma mem_visits {p : ntm.RunPath input} {pos : ℕ} {i : Fin (p.length + 1)} :
    i ∈ p.visits pos ↔ (p i).inputPos.val = pos ∧ ¬(p i).Halted := by
  simp [visits]

/-- The crossing sequence of the run path `p` at input position `pos`: the storages that `p` has at
its visits to `pos`, in the order of the visits. -/
def crossingSequence (p : ntm.RunPath input) (pos : ℕ) : List (Storage Symbol State k) :=
  ((p.visits pos).sort (· ≤ ·)).map fun i ↦ (p i).storage

/-- A Turing machine that halts never visits an input position twice with the same storage: from
the second visit on, it would repeat itself forever. -/
lemma storage_injOn_visits {tm : MultiTapeTM k Symbol State} (p : tm.RunPath input)
    (h : p.last.Halted) (pos : ℕ) : Set.InjOn (fun i ↦ (p i).storage) (p.visits pos) := by
  intro i hi j hj hij
  simp only [Finset.mem_coe, mem_visits] at hi hj
  exact p.core_injOn_running h hi.2 hj.2 (Prod.ext (Fin.ext (hi.1.trans hj.1.symm)) hij)

end MultiTapeNTM.RunPath

/-- A cut of `input`: a nonempty interval `[a, b]` of input positions. -/
abbrev InputCut (input : List Symbol) := NonemptyInterval (Fin input.length)

namespace InputCut

variable (cut : InputCut input)

/-- The input head position at the left endpoint `a` of the cut. -/
def left : ℕ := cut.fst.val + 1

/-- The input head position at the right endpoint `b` of the cut. -/
def right : ℕ := cut.snd.val + 1

/-- The shortened input: the original input with the symbols in `(a, b]` cut out. -/
def shortened : List Symbol :=
  input.take cut.left ++ input.drop cut.right

/-- The input head positions `p` and `q` are on the same side of the cut, where each endpoint counts
as part of its side. -/
def SameSide (p q : ℕ) : Prop :=
  (p ≤ cut.left ∧ q ≤ cut.left) ∨ (cut.right ≤ p ∧ cut.right ≤ q)

/-- Cutting out `(a, b]` shortens the input by `b - a` symbols. -/
lemma length_shortened_add :
    cut.shortened.length + (cut.right - cut.left) = input.length := by
  grind [shortened, left, right, cut.fst_le_snd]

/-- Where an input head position on the original input lands on the shortened input. Positions left
of the cut stay, the whole cut collapses onto `a`, and positions right of the cut shift left by
`b - a`. -/
def inputPos (p : Fin (input.length + 2)) : Fin (cut.shortened.length + 2) :=
  ⟨min p.val cut.left + (p.val - cut.right), by
    have := cut.length_shortened_add
    grind [left, right, cut.fst_le_snd, Fin.le_def]⟩

/-- A move of the input head that stays on one side of the cut is the same move on the shortened
input. -/
lemma inputPos_moveInputPos {p : Fin (input.length + 2)} {m : SignType}
    (h : cut.SameSide p (moveInputPos p m)) :
    cut.inputPos (moveInputPos p m) = moveInputPos (cut.inputPos p) m :=
  Fin.ext <| by grind [SameSide, inputPos, left, right, SignType.cast, val_moveInputPos_eq,
    cut.fst_le_snd, cut.length_shortened_add]

/-- The configuration `c` on the shortened input: its input head lands at `inputPos`, and the rest
stays the same. -/
private def cfg (c : Cfg k Symbol State input) : Cfg k Symbol State cut.shortened :=
  ⟨c.state, cut.inputPos c.inputPos, c.workTapes, c.workTapePos, c.output⟩

/-- If the endpoints of the cut hold the same symbol, a configuration whose input head is not
strictly inside the cut reads the same symbol on the shortened input. At `b`, it reads the symbol
at `a` there, which is the same. -/
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

/-- If the endpoints of the cut hold the same symbol, a step that stays on one side of the cut is
also a step on the shortened input. -/
private lemma step_cfg (hsym : input[cut.fst] = input[cut.snd]) {c c' : Cfg k Symbol State input}
    (hstep : tm.Step c c') (hside : cut.SameSide c.inputPos c'.inputPos) :
    tm.step (cut.cfg c) = cut.cfg c' :=
  MultiTapeTM.step_iff.mp <| MultiTapeNTM.Follows.step (state := id) (adapter := .mapState id)
    (fun _ _ _ h ↦ h) cut.cfg hstep Option.map_id_apply
    (HeadSymbols.ext (cut.inputSymbol_cfg hsym (by
      rw [Set.mem_Ioo]; unfold SameSide at hside; omega)) rfl)
    fun _ ↦ by rintro rfl; exact Cfg.ext rfl (cut.inputPos_moveInputPos hside).symm rfl rfl rfl

/-! ### Mapping a computation path on the original input to the shortened input -/

open MultiTapeNTM MultiTapeNTM.RunPath

/-- The run of `tm` on the shortened input gets to `c`, ignoring the output. -/
private abbrev Reached (tm : MultiTapeTM k Symbol State) (c : Cfg k Symbol State input) : Prop :=
  (cut.cfg c).core ∈ Cfg.core '' tm.reachable cut.shortened

/-- The initial configuration is reached. -/
private lemma reached_head {p : tm.ComputationPath input} : cut.Reached tm p.head :=
  ⟨_, ⟨0, rfl⟩, by
    rw [p.head_eq]
    exact Prod.ext (Fin.ext (by simp [MultiTapeTM.runFrom, cfg, inputPos, Cfg.init, left, right]))
      rfl⟩

variable {cut} (hsym : input[cut.fst] = input[cut.snd])
include hsym

/-- A step that stays on one side of the cut keeps configurations reached. -/
private lemma reached_step {c c' : Cfg k Symbol State input} (h : cut.Reached tm c)
    (hstep : tm.Step c c') (hside : cut.SameSide c.inputPos c'.inputPos) : cut.Reached tm c' :=
  let ⟨d, hd, hdc⟩ := h
  ⟨tm.step d, MultiTapeTM.step_mem_reachable hd,
    (MultiTapeTM.core_step hdc).trans (congrArg Cfg.core (cut.step_cfg hsym hstep hside))⟩

/-- On the endpoints of the cut: the input head cannot cross an endpoint without visiting it. So if
the head starts on the outer side of an endpoint at a reached configuration, the path stays reached
up to the next visit to that endpoint. -/
private lemma reached_slice {p : tm.RunPath input} {pos : ℕ}
    (hpos : pos = cut.left ∨ pos = cut.right) {a : Fin (p.length + 1)} {v : p.visits pos}
    (hfirst : IsLeast {w : p.visits pos | a ≤ w.val} v) (hside : cut.SameSide (p a).inputPos pos)
    (h : cut.Reached tm (p a)) : cut.Reached tm (p v.val) := by
  obtain ⟨hav, hnext⟩ := hfirst
  suffices ∀ j, a ≤ j → j ≤ v.val → cut.SameSide (p j).inputPos pos ∧ cut.Reached tm (p j) from
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
      (hnext (a := ⟨_, mem_visits.mpr ⟨hp, mt (p.halted_mono hj.le) (mem_visits.mp v.property).2⟩⟩)
        (Fin.le_castSucc_iff.mpr haj)).not_gt hj
    have hm := abs_le.mp (Step.inputPos_le (p.step j))
    unfold SameSide at hs ⊢
    exact ⟨by omega, reached_step hsym hr (p.step j) (by unfold SameSide; omega)⟩

/-- Take two consecutive visits to an endpoint of the cut, the first of them reached. If the step
from the first visit does not move the input head into the cut, then the second visit is reached
too: in between, the input head stays on the outer side of the endpoint. -/
private lemma reached_covBy {p : tm.RunPath input} {pos : ℕ}
    (hpos : pos = cut.left ∨ pos = cut.right) {u v : p.visits pos} (huv : u ⋖ v)
    (h : cut.Reached tm (p u.val)) (hside : cut.SameSide (tm.step (p u.val)).inputPos pos) :
    cut.Reached tm (p v.val) := by
  have hlt : u.val.val < p.length := lt_of_lt_of_le huv.lt (Nat.lt_succ_iff.mp v.val.isLt)
  have hu := (mem_visits.mp u.property).1
  have hpi : tm.Step (p u.val) (p (⟨u.val, hlt⟩ : Fin p.length).succ) := p.step ⟨u.val, hlt⟩
  rw [MultiTapeTM.step_iff.mp hpi] at hside
  refine reached_slice hsym hpos ?_ hside (reached_step hsym h hpi (by unfold SameSide at *; omega))
  exact ⟨Nat.succ_le_of_lt huv.lt, fun _ hw => huv.ge_of_gt hw⟩

/-- At two visits to the endpoints of the cut with the same storage, the machine reads the same
symbol and so moves the input head the same way. Hence at least one of the two steps does not move
into the cut. -/
private lemma step_sides {p : tm.RunPath input} (u : p.visits cut.left) (v : p.visits cut.right)
    (hs : (p u.val).storage = (p v.val).storage) :
    (tm.step (p u.val)).inputPos.val ≤ cut.left ∨ cut.right ≤ (tm.step (p v.val)).inputPos.val := by
  have hl := mem_visits.mp u.property
  have hr := (mem_visits.mp v.property).1
  have hi : (p u.val).inputSymbol = (p v.val).inputSymbol := by
    rw [inputSymbolInner cut.fst (by grind [left]) cut.fst.isLt,
      inputSymbolInner cut.snd (by grind [right]) cut.snd.isLt]
    exact congrArg some hsym
  simp only [Cfg.storage, Storage.mk.injEq] at hs
  have hw : (p u.val).workTapeSymbols = (p v.val).workTapeSymbols := by
    unfold Cfg.workTapeSymbols
    rw [hs.2.1, hs.2.2]
  obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp hl.2
  rw [MultiTapeTM.step_inputPos_of_state hq, MultiTapeTM.step_inputPos_of_state (hs.1 ▸ hq), hi, hw]
  grind [val_moveInputPos_eq, SignType.cast]

/-- If the endpoints of the cut have the same crossing sequence, every visit to an endpoint is
reached.

The `n`-th visits to the two endpoints have the same storage, so they are the same configuration on
the shortened input, up to the output. By induction on `n`: one of the two steps from the `n`-th
visits does not move into the cut (`step_sides`), so the next visit to that endpoint is reached
(`reached_covBy`), and with it the next visit to the other endpoint. -/
private lemma reached_visit {p : tm.ComputationPath input}
    (hseq : crossingSequence p.toRunPath cut.left = crossingSequence p.toRunPath cut.right)
    {pos : ℕ} (hpos : pos = cut.left ∨ pos = cut.right) (u : visits p.toRunPath pos) :
    cut.Reached tm (p u.val) := by
  have hcard : (visits p.toRunPath cut.right).card = (visits p.toRunPath cut.left).card := by
    simpa [crossingSequence] using congrArg List.length hseq.symm
  let l := (visits p.toRunPath cut.left).orderIsoOfFin rfl
  let r := (visits p.toRunPath cut.right).orderIsoOfFin hcard
  have hs (n) : (p (l n)).storage = (p (r n)).storage := by
    simpa [crossingSequence, hcard, l, r, Finset.coe_orderIsoOfFin_apply,
      Finset.orderEmbOfFin_apply] using congrArg (·[n.val]?) hseq
  have hcore (n) : cut.Reached tm (p (l n)) ↔ cut.Reached tm (p (r n)) := by
    have hl := (mem_visits.mp (l n).property).1
    have hr := (mem_visits.mp (r n).property).1
    rw [Reached, Reached, show (cut.cfg (p (l n))).core = (cut.cfg (p (r n))).core from
      Prod.ext (Fin.ext (by grind [Cfg.core, cfg, inputPos, left, right, cut.fst_le_snd])) (hs n)]
  have hl (n : ℕ) (hn : n < (visits p.toRunPath cut.left).card) :
      cut.Reached tm (p (l ⟨n, hn⟩)) := by
    induction n with
    | zero =>
      exact reached_slice hsym (.inl rfl)
        ⟨Fin.zero_le _, fun w _ ↦ l.le_symm_apply.mp (Nat.zero_le _)⟩
        (.inl ⟨by simp [show p 0 = _ from p.head_eq, left], le_rfl⟩) (reached_head cut)
    | succ n ih =>
      have hcov : (⟨n, by omega⟩ : Fin _) ⋖ ⟨n + 1, hn⟩ := Fin.covBy_iff.mpr (Order.covBy_add_one n)
      rcases step_sides hsym (l _) (r _) (hs ⟨n, by omega⟩) with h | h
      · exact reached_covBy hsym (.inl rfl) ((apply_covBy_apply_iff l).mpr hcov) (ih _)
          (.inl ⟨h, le_rfl⟩)
      · exact (hcore _).mpr (reached_covBy hsym (.inr rfl) ((apply_covBy_apply_iff r).mpr hcov)
          ((hcore _).mp (ih _)) (.inr ⟨h, le_rfl⟩))
  rcases hpos with rfl | rfl
  · obtain ⟨n, rfl⟩ := l.surjective u
    exact hl n n.isLt
  · obtain ⟨n, rfl⟩ := r.surjective u
    exact (hcore n).mp (hl n n.isLt)

/-- If the endpoints of the cut have the same crossing sequence, every configuration in the path
with the input head outside the cut is reached.

By induction along the path: one step earlier, the input head was outside the cut too, or at an
endpoint, where `reached_visit` applies. -/
private lemma reached_of_mem {p : tm.ComputationPath input}
    (hseq : crossingSequence p.toRunPath cut.left = crossingSequence p.toRunPath cut.right)
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
        exact reached_visit hsym hseq hb ⟨t.castSucc, mem_visits.mpr ⟨rfl, ht⟩⟩
      · exact ih (by omega)
    exact reached_step hsym hprev (p.step t) (by unfold SameSide; omega)

omit hsym in
variable (cut) in
/-- **Input shortening.** If the endpoints of the cut hold the same symbol and have the same
crossing sequence in `path`, then every storage in `path` with the input head outside the cut also
occurs in the run of `tm` on the shortened input. -/
theorem exists_storage_eq (hsym : input[cut.fst] = input[cut.snd])
    {path : tm.ComputationPath input}
    (hseq : crossingSequence path.toRunPath cut.left = crossingSequence path.toRunPath cut.right)
    {c : Cfg k Symbol State input} (hc : c ∈ path)
    (hout : c.inputPos.val ∉ Set.Icc cut.left cut.right) :
    c.storage ∈ Cfg.storage '' tm.reachable cut.shortened :=
  let ⟨d, hd, hdc⟩ := reached_of_mem hsym hseq hc hout
  ⟨d, hd, congrArg Prod.snd hdc⟩

end InputCut

namespace MultiTapeTM

variable {tm : MultiTapeTM k Symbol State}

open MultiTapeNTM MultiTapeNTM.RunPath

/-- **Input shortening.** If a computation path of `tm` halts in space `s` on an input longer than
`3 * |Symbol| * (B + 1) ^ B`, where `B` bounds the number of storages in space `s`, then for every
configuration `c` in the path, the storage of `c` is reached on some shorter input.

By the pigeonhole principle, two input positions on the same side of the input head of `c` hold the
same symbol and have the same crossing sequence. Then `InputCut.exists_storage_eq` applies to the
cut between them. -/
theorem exists_shorter_input_storage [Fintype Symbol] [Fintype State] {s : ℕ}
    {path : tm.ComputationPath input} (hs : path.space ≤ s) (hhalt : path.last.Halted)
    (hlen : 3 * Fintype.card Symbol *
      (storageBound Symbol State k s + 1) ^ storageBound Symbol State k s < input.length)
    {c : Cfg k Symbol State input} (hc : c ∈ path) :
    ∃ input' : List Symbol, input'.length < input.length ∧
      c.storage ∈ Cfg.storage '' tm.reachable input' := by
  let P := path.toRunPath
  -- Every prefix fits in the windows given by the space of this path.
  let w := spaceUsedByTape P
  let B := storageBound Symbol State k s
  have hS (t : Fin (path.length + 1)) : (P t).storage.FitsIn w := by
    let q : tm.ComputationPath input := ⟨P.take t, by simp [P, path.head_eq]⟩
    exact Storage.FitsIn_mono
      (fun j => Finset.card_le_card (visitedByTapeHead_take_subset P t j)) q.storage_fitsIn
  have hfits {pos n : ℕ} {x} (hx : (crossingSequence P pos)[n]? = some x) : x.FitsIn w := by
    obtain ⟨t, -, rfl⟩ := List.mem_map.mp (List.mem_of_getElem? hx)
    exact hS t
  have hcard : Fintype.card (BoundedStorage Symbol State w) ≤ B := card_boundedStorage_le hs
  have hlength (pos : ℕ) : (crossingSequence P pos).length ≤ B := by
    simp only [crossingSequence, List.length_map, Finset.length_sort]
    exact (Finset.card_le_card_of_injOn _ (fun _ _ ↦ Finset.mem_coe.mpr (Finset.mem_univ _))
      ((Storage.toBounded_injOn w).comp (storage_injOn_visits P hhalt pos) fun t _ ↦ hS t)).trans
      (by simpa using hcard)
  -- Record the side of `c`, the input symbol, and the bounded crossing sequence.
  let f (j : Fin input.length) := (compare (j.val + 1) c.inputPos.val, input[j],
    fun n : Fin B ↦ ((crossingSequence P (j.val + 1))[n.val]?).map (·.toBounded w))
  obtain ⟨a, b, hab, hf⟩ : ∃ a b, a < b ∧ f a = f b := by
    obtain ⟨a, b, hne, hf⟩ := Fintype.exists_ne_map_eq_of_card_lt f <| by
      rw [Fintype.card_prod, Fintype.card_prod, show Fintype.card Ordering = 3 by decide,
        Fintype.card_fun, Fintype.card_option, Fintype.card_fin, Fintype.card_fin, ← mul_assoc]
      calc
        _ ≤ 3 * Fintype.card Symbol * (B + 1) ^ B := by gcongr; omega
        _ < input.length := hlen
    grind
  obtain ⟨hside, hsym, hseq⟩ := (by simpa only [f, Prod.mk.injEq] using hf)
  have hseq' : crossingSequence P (a.val + 1) = crossingSequence P (b.val + 1) := by
    refine List.ext_getElem?' fun r hr ↦ ?_
    have he := congrFun hseq ⟨r, hr.trans_le (max_le (hlength _) (hlength _))⟩
    rcases ha : (crossingSequence P (a.val + 1))[r]? with _ | x <;>
      rcases hb : (crossingSequence P (b.val + 1))[r]? with _ | y <;>
      simp only [ha, hb, Option.map_none, Option.map_some, reduceCtorEq, Option.some.injEq]
        at he ⊢
    exact Storage.toBounded_injOn w (hfits ha) (hfits hb) he
  let cut : InputCut input := ⟨⟨a, b⟩, hab.le⟩
  have hout : ¬(a.val + 1 ≤ c.inputPos.val ∧ c.inputPos.val ≤ b.val + 1) := by
    grind [compare_lt_iff_lt, compare_eq_iff_eq, compare_gt_iff_gt]
  refine ⟨cut.shortened, ?_, cut.exists_storage_eq hsym hseq' hc hout⟩
  have := cut.length_shortened_add
  change cut.shortened.length + (b.val + 1 - (a.val + 1)) = input.length at this
  omega

end MultiTapeTM

end Turing
