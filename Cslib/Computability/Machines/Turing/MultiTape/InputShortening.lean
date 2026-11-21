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

Consider a deterministic Turing machine and a halting computation path on an input. Input-head
positions are counted from the left endmarker at position `0`, so the input symbol at index `i` is
read at position `i + 1`. The *crossing sequence* at an input-head position is the list of storages
(`Storage`: state, work tapes and work heads) of the running configurations of the path with the
input head at that position, in chronological order.

Take two input-symbol indices `a ≤ b` that carry the same symbol and whose positions `a + 1` and
`b + 1` have the same crossing sequence. Deleting the symbols at indices `a + 1, ..., b` gives the
*shortened input*. Every configuration of the path whose input head is outside positions
`a + 1, ..., b + 1` has its storage reached by the machine on the shortened input. This is the main
ingredient in the proof of `SPACE(o(log log n)) = SPACE(1)`.

The proof idea follows [Katz2007], §1.2, Theorem 4.

## Main definitions

* `MultiTapeNTM.RunPath.visits`: the time steps at which a run path is running with its input head
  at a given position.
* `MultiTapeNTM.RunPath.crossingSequence`: the storages at those time steps, in chronological order.
* `InputCut`: an interval `[a, b]` of input-symbol indices; the symbols at indices `a + 1, ..., b`
  are deleted.
* `InputCut.shortened`: the shortened input.
* `InputCut.SameSide`: two input-head positions on the original input that are on the same side
  of the deleted symbols.

## Main results

* `MultiTapeNTM.RunPath.storage_injOn_visits`: in a halting deterministic run path, the running
  configurations at distinct time steps with the input head at the same position have distinct
  storages.
* `InputCut.exists_storage_eq`: if the two endpoints of the cut carry the same symbol and have the
  same crossing sequence, every configuration of the path with the input head outside the
  endpoints and the positions between them has its storage reached on the shortened input.
* `MultiTapeTM.exists_shorter_input_storage`: for a halting computation path in space `s` on a long
  enough input, every storage of the path is reached on some shorter input.

## References

* [Jonathan Katz, *Notes on Complexity Theory, Lecture 5*][Katz2007],
  §1.2, Theorem 4, pp. 5-2–5-4.
-/

@[expose] public section

namespace Turing

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}

namespace MultiTapeNTM.RunPath

variable {ntm : MultiTapeNTM k Symbol State}

/-- The time steps at which the run path `p` is in a running configuration with its input head at
position `pos`. -/
def visits (p : ntm.RunPath input) (pos : ℕ) : Finset (Fin (p.length + 1)) :=
  {i | (p i).inputPos.val = pos ∧ ¬(p i).Halted}

@[simp]
lemma mem_visits {p : ntm.RunPath input} {pos : ℕ} {i : Fin (p.length + 1)} :
    i ∈ p.visits pos ↔ (p i).inputPos.val = pos ∧ ¬(p i).Halted := by
  simp [visits]

/-- The crossing sequence of the run path `p` at input-head position `pos`: the storages of `p` at
the time steps in `p.visits pos`, in chronological order. -/
def crossingSequence (p : ntm.RunPath input) (pos : ℕ) : List (Storage Symbol State k) :=
  ((p.visits pos).sort (· ≤ ·)).map fun i ↦ (p i).storage

/-- In a deterministic run path `p` that ends halted, the configurations at distinct time steps in
`p.visits pos` have distinct storages. Equal storages at the same input-head position would repeat
the `Cfg.core` of a running configuration, which a halting deterministic run never does. -/
lemma storage_injOn_visits {tm : MultiTapeTM k Symbol State} (p : tm.RunPath input)
    (h : p.last.Halted) (pos : ℕ) : Set.InjOn (fun i ↦ (p i).storage) (p.visits pos) := by
  intro i hi j hj hij
  simp only [Finset.mem_coe, mem_visits] at hi hj
  exact p.core_injOn_running h hi.2 hj.2 (Prod.ext (Fin.ext (hi.1.trans hj.1.symm)) hij)

end MultiTapeNTM.RunPath

/-- A cut of `input`: an interval `[a, b]` of input-symbol indices. It deletes the symbols at
indices `a + 1, ..., b` and keeps those at `a` and `b`, so `a = b` deletes nothing. -/
abbrev InputCut (input : List Symbol) := NonemptyInterval (Fin input.length)

namespace InputCut

variable (cut : InputCut input)

/-- The input-head position on the original input that reads the first index `a` of the cut. The
left endmarker is at position `0`, so the symbol at index `i` is read at position `i + 1`. -/
def left : ℕ := cut.fst.val + 1

/-- The input-head position on the original input that reads the last index `b` of the cut. -/
def right : ℕ := cut.snd.val + 1

/-- The shortened input: the original input without the symbols at indices `a + 1, ..., b`. On the
original input, these symbols are read at input-head positions `cut.left + 1, ..., cut.right`. -/
def shortened : List Symbol :=
  input.take cut.left ++ input.drop cut.right

/-- The input-head positions `p` and `q` on the original input are on the same side of the deleted
symbols: both are at most `cut.left`, or both are at least `cut.right`. -/
def SameSide (p q : ℕ) : Prop :=
  (p ≤ cut.left ∧ q ≤ cut.left) ∨ (cut.right ≤ p ∧ cut.right ≤ q)

/-- The shortened input is `cut.right - cut.left` symbols shorter than the original input. -/
lemma length_shortened_add :
    cut.shortened.length + (cut.right - cut.left) = input.length := by
  grind [shortened, left, right, cut.fst_le_snd]

/-- Maps an input-head position `p` on the original input to one on the shortened input. Positions
up to `cut.left` are unchanged, positions between `cut.left` and `cut.right` go to `cut.left`, and
positions from `cut.right` on move left by `cut.right - cut.left`. -/
def inputPos (p : Fin (input.length + 2)) : Fin (cut.shortened.length + 2) :=
  ⟨min p.val cut.left + (p.val - cut.right), by
    have := cut.length_shortened_add
    grind [left, right, cut.fst_le_snd, Fin.le_def]⟩

/-- Let the input head on the original input move from position `p` by `m` and stay on the same
side of the deleted symbols. Then mapping to the shortened input commutes with the move. -/
lemma inputPos_moveInputPos {p : Fin (input.length + 2)} {m : SignType}
    (h : cut.SameSide p (moveInputPos p m)) :
    cut.inputPos (moveInputPos p m) = moveInputPos (cut.inputPos p) m :=
  Fin.ext <| by grind [SameSide, inputPos, left, right, SignType.cast, val_moveInputPos_eq,
    cut.fst_le_snd, cut.length_shortened_add]

/-- Maps a configuration `c` on the original input to one on the shortened input. The input-head
position is mapped by `inputPos`, and everything else is unchanged. -/
private def cfg (c : Cfg k Symbol State input) : Cfg k Symbol State cut.shortened :=
  ⟨c.state, cut.inputPos c.inputPos, c.workTapes, c.workTapePos, c.output⟩

/-- Let the symbols at indices `a` and `b` be equal, and let `c` be a configuration on the original
input whose input head is not strictly between `cut.left` and `cut.right`. Then the image of `c` on
the shortened input reads the same input symbol as `c`. -/
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

/-- Let the symbols at indices `a` and `b` be equal, and let `tm` step from `c` to `c'` on the
original input with the input head staying on one side of the deleted symbols. Then on the
shortened input, `tm` steps from the image of `c` to the image of `c'`. -/
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

/-- A configuration `c` on the original input is reached when its image on the shortened input has
the same `Cfg.core` as a configuration that `tm` reaches on the shortened input. -/
private abbrev Reached (tm : MultiTapeTM k Symbol State) (c : Cfg k Symbol State input) : Prop :=
  (cut.cfg c).core ∈ Cfg.core '' tm.reachable cut.shortened

/-- The first configuration of a computation path on the original input is reached: its image is
the initial configuration on the shortened input. -/
private lemma reached_head {p : tm.ComputationPath input} : cut.Reached tm p.head :=
  ⟨_, ⟨0, rfl⟩, by
    rw [p.head_eq]
    exact Prod.ext (Fin.ext (by simp [MultiTapeTM.runFrom, cfg, inputPos, Cfg.init, left, right]))
      rfl⟩

variable {cut} (hsym : input[cut.fst] = input[cut.snd])
include hsym

/-- If the configuration `c` on the original input is reached and `tm` steps from `c` to `c'` with
the input head staying on one side of the deleted symbols, then `c'` is reached. -/
private lemma reached_step {c c' : Cfg k Symbol State input} (h : cut.Reached tm c)
    (hstep : tm.Step c c') (hside : cut.SameSide c.inputPos c'.inputPos) : cut.Reached tm c' :=
  let ⟨d, hd, hdc⟩ := h
  ⟨tm.step d, MultiTapeTM.step_mem_reachable hd,
    (MultiTapeTM.core_step hdc).trans (congrArg Cfg.core (cut.step_cfg hsym hstep hside))⟩

/-- Let `pos` be `cut.left` or `cut.right`, let `a` be a time step of the run path `p` on the
original input, and let `v` be the first time step from `a` on in `p.visits pos`. If at time `a` the
input head is on the same side of the deleted symbols as `pos`, it stays on that side until time
`v`. So if `p a` is reached, then `p v` is reached. -/
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
      (hnext (a := ⟨_, mem_visits.mpr ⟨hp, mt (p.halted_mono hj.le) (mem_visits.mp v.2).2⟩⟩)
        (Fin.le_castSucc_iff.mpr haj)).not_gt hj
    have hm := abs_le.mp (Step.inputPos_le (p.step j))
    unfold SameSide at hs ⊢
    exact ⟨by omega, reached_step hsym hr (p.step j) (by unfold SameSide; omega)⟩

/-- Let `pos` be `cut.left` or `cut.right`, and let `u ⋖ v` be consecutive time steps in
`p.visits pos`. If the step from `p u` moves the input head to the same side of the deleted symbols
as `pos`, and `p u` is reached, then `p v` is reached. -/
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

/-- Let `u` be a time step in `p.visits cut.left` and `v` one in `p.visits cut.right`, with the same
storage. The two configurations read the same input symbol, so `tm` moves the input head in the same
direction from both. Hence the step from `p u` keeps the input head at most `cut.left`, or the step
from `p v` keeps it at least `cut.right`. -/
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

/-- Let the computation path `p` on the original input have the same crossing sequence at `cut.left`
and `cut.right`, and let `u` be a time step in `p.visits pos` with `pos` one of them. Then `p u` is
reached.

The proof is by induction on the index `n` of the time step in `p.visits pos`. The `n`-th time steps
at `cut.left` and at `cut.right` have the same storage. Both input-head positions map to `cut.left`
on the shortened input, so the two configurations are both reached or both not. By `step_sides`, the
step from one of them stays on its side, so by `reached_covBy` the `n + 1`-th time step there is
reached, and with it the one at the other endpoint. -/
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

/-- Let the computation path `p` on the original input have the same crossing sequence at `cut.left`
and `cut.right`. Then every configuration `c` of `p` with the input head outside positions
`cut.left, ..., cut.right` is reached.

The proof is by induction on the time step of `c`. The previous configuration is a running
configuration at `cut.left` or `cut.right`, reached by `reached_visit`, or is outside these
positions too. A halted configuration at `cut.left` or `cut.right` is excluded, because it may be
entered from a deleted symbol. -/
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
/-- **Input shortening.** Let the symbols at the cut's indices `a` and `b` be equal, and let the
computation path `path` of `tm` on the original input have the same crossing sequence at the
input-head positions `cut.left` and `cut.right`. Then for every configuration `c` of `path` with
the input head outside positions `cut.left, ..., cut.right`, `tm` reaches a configuration with the
storage of `c` on the shortened input. -/
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

/-- **Input shortening.** Let `path` be a halting computation path of `tm` on `input` in space `s`,
and let `input` have more than `3 * |Symbol| * (B + 1) ^ B` symbols, where `B` bounds the number of
storages in space `s`. Then for every configuration `d` of `path`, `tm` reaches a configuration
with the storage of `d` on some shorter input.

By the pigeonhole principle, there are indices `a < b` whose input-head positions are on the same
side of that of `d`, with the same symbol and the same crossing sequence. Then
`InputCut.exists_storage_eq` applies to the cut `[a, b]`. -/
theorem exists_shorter_input_storage [Fintype Symbol] [Fintype State] {s : ℕ}
    {path : tm.ComputationPath input} (hs : path.space ≤ s) (hhalt : path.last.Halted)
    (hlen : 3 * Fintype.card Symbol *
      (storageBound Symbol State k s + 1) ^ storageBound Symbol State k s < input.length)
    {d : Cfg k Symbol State input} (hd : d ∈ path) :
    ∃ input' : List Symbol, input'.length < input.length ∧
      d.storage ∈ Cfg.storage '' tm.reachable input' := by
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
  -- Record the side of `d`, the input symbol, and the bounded crossing sequence.
  let f (j : Fin input.length) := (compare (j.val + 1) d.inputPos.val, input[j],
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
  have hout : ¬(a.val + 1 ≤ d.inputPos.val ∧ d.inputPos.val ≤ b.val + 1) := by
    grind [compare_lt_iff_lt, compare_eq_iff_eq, compare_gt_iff_gt]
  refine ⟨cut.shortened, ?_, cut.exists_storage_eq hsym hseq' hd hout⟩
  have := cut.length_shortened_add
  change cut.shortened.length + (b.val + 1 - (a.val + 1)) = input.length at this
  omega

end MultiTapeTM

end Turing
