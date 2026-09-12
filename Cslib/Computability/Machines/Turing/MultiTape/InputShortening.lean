/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/
module

public import Cslib.Computability.Machines.Turing.MultiTape.ConfigBound
public import Mathlib.Combinatorics.Pigeonhole
public import Mathlib.Data.Finset.Sort

/-!
# Input shortening for multi-tape Turing machines

A visit sequence records the storages seen at a fixed input position during a finite run.
Up to the first halt, these storages are distinct: repeating a core would repeat the rest of the
computation, regardless of the write-only output.

The input-shortening argument follows Gadi Aleksandrowicz's account at
<https://gadial.net/2009/10/04/sub_loglog_space_is_constant/>.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}
variable {tm : MultiTapeTM k Symbol State}

/-- Times up to `T` at which the input head is at `p`. -/
def visitTimes (cfg : Cfg k Symbol State input) (T p : ℕ) : Finset ℕ :=
  (Finset.range (T + 1)).filter fun t => (tm.runFrom cfg t).inputPos.val = p

@[simp]
lemma mem_visitTimes {cfg : Cfg k Symbol State input} {T p t : ℕ} :
    t ∈ tm.visitTimes cfg T p ↔ t ≤ T ∧ (tm.runFrom cfg t).inputPos.val = p := by
  simp [visitTimes]

/-- The chronological list of storages encountered at input position `p` through time `T`. -/
def visitSequence (cfg : Cfg k Symbol State input) (T p : ℕ) : List (Storage Symbol State k) :=
  ((tm.visitTimes cfg T p).sort (· ≤ ·)).map fun t => (tm.runFrom cfg t).storage

@[simp]
lemma length_visitSequence (cfg : Cfg k Symbol State input) (T p : ℕ) :
    (tm.visitSequence cfg T p).length = (tm.visitTimes cfg T p).card := by
  simp [visitSequence]

/-- No storage occurs twice at one input position before the first halt. -/
lemma visitSequence_nodup {cfg : Cfg k Symbol State input} {T : ℕ}
    (hhalt : (tm.runFrom cfg T).Halted)
    (hfirst : ∀ t < T, ¬ (tm.runFrom cfg t).Halted) (p : ℕ) :
    (tm.visitSequence cfg T p).Nodup := by
  classical
  apply List.Nodup.map_on _ (Finset.sort_nodup _ _)
  intro a ha b hb h
  have ha' := tm.mem_visitTimes.mp (by simpa using ha)
  have hb' := tm.mem_visitTimes.mp (by simpa using hb)
  apply tm.core_runFrom_injOn hhalt hfirst ha'.1 hb'.1
  exact Prod.ext (Fin.ext (ha'.2.trans hb'.2.symm)) h

/-- Deleting the cells after `a` through `b` preserves symbols at positions at most `a`. -/
private lemma inputSymbol_cut_left {a b : ℕ} (ha : a ≤ input.length)
    (c : Cfg k Symbol State input)
    (c' : Cfg k Symbol State (input.take a ++ input.drop b))
    (hc : c.inputPos.val ≤ a) (hp : c'.inputPos.val = c.inputPos.val) :
    c.inputSymbol = c'.inputSymbol := by
  rw [inputSymbol_eq_getElem?, inputSymbol_eq_getElem?, hp]
  split_ifs with h
  · rfl
  · have hi : c.inputPos.val - 1 < a := by omega
    simp [List.getElem?_append, ha, hi]

/-- After deleting the cells after `a` through `b`, symbols at positions at least `b`
are preserved by shifting left by `b - a`, provided the symbols at `a` and `b` agree. -/
private lemma inputSymbol_cut_right {a b : ℕ}
    (ha : 0 < a) (hab : a < b) (hb : b ≤ input.length)
    (hsym : input[a - 1]? = input[b - 1]?)
    (c : Cfg k Symbol State input)
    (c' : Cfg k Symbol State (input.take a ++ input.drop b))
    (hc : b ≤ c.inputPos.val) (hp : c'.inputPos.val + (b - a) = c.inputPos.val) :
    c.inputSymbol = c'.inputSymbol := by
  have hp₀ : c.inputPos.val ≠ 0 := by omega
  have hp'₀ : c'.inputPos.val ≠ 0 := by omega
  rw [inputSymbol_eq_getElem?, inputSymbol_eq_getElem?, ite_eq_right hp₀,
    ite_eq_right hp'₀]
  have htake : (input.take a).length = a := by simp; omega
  by_cases heq : c.inputPos.val = b
  · have hpa : c'.inputPos.val = a := by omega
    simp [hpa, heq, List.getElem?_append, htake,
      show a - 1 < a by omega, ← hsym]
  · have hi : a ≤ c'.inputPos.val - 1 := by omega
    have he : b + (c'.inputPos.val - 1 - a) = c.inputPos.val - 1 := by omega
    simp [List.getElem?_append, htake, not_lt.mpr hi, he]

/-- Propagate a predicate from `u` to `v` using steps within `[u, v]`. -/
private lemma propagate {P : ℕ → Prop} {u v : ℕ} (huv : u ≤ v) (hu : P u)
    (hstep : ∀ t, u ≤ t → t < v → P t → P (t + 1)) : P v := by
  induction v, huv using Nat.le_induction with
  | base => exact hu
  | succ v huv ih =>
    exact hstep v huv (Nat.lt_succ_self _) (ih fun t hut htv => hstep t hut (by omega))

/-- After staying left of `a` for one step, a walk cannot cross `a` without revisiting it. -/
private lemma walk_left {p : ℕ → ℕ} {u v a : ℕ}
    (hstep : ∀ t, u ≤ t → t < v → p (t + 1) ≤ p t + 1)
    (hu : p u ≤ a) (hu' : p (u + 1) ≤ a)
    (hno : ∀ t, u < t → t < v → p t ≠ a) :
    ∀ t, u ≤ t → t ≤ v → p t ≤ a := by
  intro t hut htv
  apply propagate hut hu
  intro r hur hrt hr
  by_cases heq : r = u
  · simpa [heq] using hu'
  · have := hstep r hur (by omega)
    have := hno r (by omega) (by omega)
    omega

/-- After staying right of `b` for one step, a walk cannot cross `b` without revisiting it. -/
private lemma walk_right {p : ℕ → ℕ} {u v b : ℕ}
    (hstep : ∀ t, u ≤ t → t < v → p t ≤ p (t + 1) + 1)
    (hu : b ≤ p u) (hu' : b ≤ p (u + 1))
    (hno : ∀ t, u < t → t < v → p t ≠ b) :
    ∀ t, u ≤ t → t ≤ v → b ≤ p t := by
  intro t hut htv
  apply propagate hut hu
  intro r hur hrt hr
  by_cases heq : r = u
  · simpa [heq] using hu'
  · have := hstep r hur (by omega)
    have := hno r (by omega) (by omega)
    omega

/-- Matching ordered visits at `a` and `b` allow the portions of a walk outside `(a, b)`
to be joined. Any predicate `R` preserved along those portions holds throughout the joined walk. -/
private lemma glue_visits {S : Type*} (p : ℕ → ℕ) (q : ℕ → S) {T a b m : ℕ}
    (hab : a < b) (hp₀ : p 0 ≤ a)
    (hstep : ∀ t < T, p (t + 1) ≤ p t + 1 ∧ p t ≤ p (t + 1) + 1)
    (A B : Fin m ↪o ℕ)
    (hA : ∀ i, A i ≤ T ∧ p (A i) = a)
    (hB : ∀ i, B i ≤ T ∧ p (B i) = b)
    (hAc : ∀ t ≤ T, p t = a → ∃ i, A i = t)
    (hBc : ∀ t ≤ T, p t = b → ∃ i, B i = t)
    (hq : ∀ i, q (A i) = q (B i))
    (hmove : ∀ i, p (A i + 1) + b = p (B i + 1) + a)
    (R : ℕ → S → Prop) (hR₀ : R (p 0) (q 0))
    (hleft : ∀ t < T, p t ≤ a → p (t + 1) ≤ a →
      R (p t) (q t) → R (p (t + 1)) (q (t + 1)))
    (hright : ∀ t < T, b ≤ p t → b ≤ p (t + 1) →
      R (p t - (b - a)) (q t) → R (p (t + 1) - (b - a)) (q (t + 1))) :
    ∀ t ≤ T, p t ≤ a ∨ b ≤ p t →
      R (if p t ≤ a then p t else p t - (b - a)) (q t) := by
  have hba : b - (b - a) = a := by omega
  have boundary : ∀ i, R a (q (A i)) := by
    cases m with
    | zero => exact fun i => Fin.elim0 i
    | succ m =>
      intro i
      induction i using Fin.induction with
      | zero =>
        have hno : ∀ t < A 0, p t ≠ a := by
          intro t ht hpt
          obtain ⟨j, rfl⟩ := hAc t (ht.le.trans (hA 0).1) hpt
          exact (not_lt_of_ge (A.monotone (Fin.zero_le j))) ht
        have hside : ∀ t ≤ A 0, p t ≤ a := by
          intro t ht
          apply propagate (Nat.zero_le t) hp₀
          intro r _ hrt hr
          have := (hstep r (by have := (hA 0).1; omega)).1
          have := hno r (by omega)
          omega
        have hr := propagate (Nat.zero_le (A 0)) hR₀ fun t _ ht =>
          hleft t (ht.trans_le (hA 0).1) (hside t ht.le) (hside (t + 1) ht)
        simpa [(hA 0).2] using hr
      | succ i ih =>
        have hAj := A.strictMono i.castSucc_lt_succ
        have hBj := B.strictMono i.castSucc_lt_succ
        have hnoA : ∀ t, A i.castSucc < t → t < A i.succ → p t ≠ a := by
          intro t hjt hti hpt
          obtain ⟨r, rfl⟩ := hAc t (hti.le.trans (hA i.succ).1) hpt
          exact (not_lt_of_ge (Fin.le_castSucc_iff.mpr (A.lt_iff_lt.mp hti)))
            (A.lt_iff_lt.mp hjt)
        have hnoB : ∀ t, B i.castSucc < t → t < B i.succ → p t ≠ b := by
          intro t hjt hti hpt
          obtain ⟨r, rfl⟩ := hBc t (hti.le.trans (hB i.succ).1) hpt
          exact (not_lt_of_ge (Fin.le_castSucc_iff.mpr (B.lt_iff_lt.mp hti)))
            (B.lt_iff_lt.mp hjt)
        by_cases hdir : p (A i.castSucc + 1) ≤ a
        · have hside := walk_left
            (fun t (_ : A i.castSucc ≤ t) (ht : t < A i.succ) =>
              (hstep t (ht.trans_le (hA i.succ).1)).1)
            (le_of_eq (hA i.castSucc).2) hdir hnoA
          have hr := propagate hAj.le
            (show R (p (A i.castSucc)) (q (A i.castSucc)) by
              simpa [(hA i.castSucc).2] using ih) fun t hjt hti =>
                hleft t (hti.trans_le (hA i.succ).1)
                  (hside t hjt hti.le) (hside (t + 1) (by omega) hti)
          simpa [(hA i.succ).2] using hr
        · have hdir' : b ≤ p (B i.castSucc + 1) := by have := hmove i.castSucc; omega
          have hside := walk_right
            (fun t (_ : B i.castSucc ≤ t) (ht : t < B i.succ) =>
              (hstep t (ht.trans_le (hB i.succ).1)).2)
            (ge_of_eq (hB i.castSucc).2) hdir' hnoB
          have hr := propagate hBj.le
            (show R (p (B i.castSucc) - (b - a)) (q (B i.castSucc)) by
              simpa [(hB i.castSucc).2, hba, ← hq i.castSucc] using ih) fun t hjt hti =>
                hright t (hti.trans_le (hB i.succ).1)
                  (hside t hjt hti.le) (hside (t + 1) (by omega) hti)
          simpa [(hB i.succ).2, hba, ← hq i.succ] using hr
  intro t
  induction t with
  | zero => intro _ _; simpa [hp₀] using hR₀
  | succ t ih =>
    intro ht hside
    have hst := hstep t (by omega)
    by_cases hl : p (t + 1) ≤ a
    · rw [ite_eq_left hl]
      by_cases heq : p (t + 1) = a
      · obtain ⟨i, hi⟩ := hAc (t + 1) ht heq
        simpa [hi, heq] using boundary i
      · have hprev : p t ≤ a := by omega
        exact hleft t (by omega) hprev hl (by
          simpa [hprev] using ih (by omega) (Or.inl hprev))
    · rw [ite_eq_right hl]
      have hr : b ≤ p (t + 1) := hside.resolve_left hl
      by_cases heq : p (t + 1) = b
      · obtain ⟨i, hi⟩ := hBc (t + 1) ht heq
        simpa [hq i, hi, heq, hba] using boundary i
      · have hprev : b ≤ p t := by omega
        have hprev' : ¬ p t ≤ a := by omega
        exact hright t (by omega) hprev hr (by
          simpa [hprev'] using ih (by omega) (Or.inr hprev))

/-- The entry at index `i` is the storage at the `i`th visit time. -/
private lemma visitSequence_get {cfg : Cfg k Symbol State input} {T p m : ℕ}
    (h : (tm.visitTimes cfg T p).card = m) (i : Fin m) :
    (tm.visitSequence cfg T p)[i.val]'(by rw [length_visitSequence, h]; exact i.isLt) =
      (tm.runFrom cfg ((tm.visitTimes cfg T p).orderEmbOfFin h i)).storage := by
  simp [visitSequence, Finset.orderEmbOfFin_apply]

/-- Deleting the cells after `a` through `b` preserves every storage reached outside the deleted
interval, provided the symbols and visit sequences at `a` and `b` agree. Input positions are
one-based, as in `Cfg.inputPos`; neither cut position is an endmarker. -/
theorem exists_storage_cut {a b T : ℕ}
    (ha : 0 < a) (hab : a < b) (hb : b ≤ input.length)
    (hsym : input[a - 1]? = input[b - 1]?)
    (hseq : tm.visitSequence (tm.initCfg input) T a =
      tm.visitSequence (tm.initCfg input) T b)
    {t : ℕ} (ht : t ≤ T)
    (hp : (tm.runFrom (tm.initCfg input) t).inputPos.val ≤ a ∨
      b ≤ (tm.runFrom (tm.initCfg input) t).inputPos.val) :
    ∃ u, (tm.runFrom (tm.initCfg (input.take a ++ input.drop b)) u).storage =
      (tm.runFrom (tm.initCfg input) t).storage := by
  let c := tm.runFrom (tm.initCfg input)
  let c' := tm.runFrom (tm.initCfg (input.take a ++ input.drop b))
  let m := (tm.visitTimes (tm.initCfg input) T a).card
  have hcard : (tm.visitTimes (tm.initCfg input) T b).card = m := by
    simpa [m] using (congrArg List.length hseq).symm
  let A := (tm.visitTimes (tm.initCfg input) T a).orderEmbOfFin rfl
  let B := (tm.visitTimes (tm.initCfg input) T b).orderEmbOfFin hcard
  have hA : ∀ i, A i ≤ T ∧ (c (A i)).inputPos.val = a := fun i =>
    tm.mem_visitTimes.mp (Finset.orderEmbOfFin_mem _ _ i)
  have hB : ∀ i, B i ≤ T ∧ (c (B i)).inputPos.val = b := fun i =>
    tm.mem_visitTimes.mp (Finset.orderEmbOfFin_mem _ _ i)
  have hAc : ∀ u ≤ T, (c u).inputPos.val = a → ∃ i, A i = u := by
    intro u hu hpu
    change u ∈ Set.range A
    simpa only [A, Finset.range_orderEmbOfFin, Finset.mem_coe] using
      tm.mem_visitTimes.mpr ⟨hu, hpu⟩
  have hBc : ∀ u ≤ T, (c u).inputPos.val = b → ∃ i, B i = u := by
    intro u hu hpu
    change u ∈ Set.range B
    simpa only [B, Finset.range_orderEmbOfFin, Finset.mem_coe] using
      tm.mem_visitTimes.mpr ⟨hu, hpu⟩
  have hq : ∀ i, (c (A i)).storage = (c (B i)).storage := by
    intro i
    have heq := List.getElem_of_eq hseq (i := i.val)
      (by rw [length_visitSequence]; exact i.isLt)
    exact (visitSequence_get rfl i).symm.trans (heq.trans (visitSequence_get hcard i))
  have hmove : ∀ i,
      (c (A i + 1)).inputPos.val + b = (c (B i + 1)).inputPos.val + a := by
    intro i
    have hsy : (c (A i)).inputSymbol = (c (B i)).inputSymbol := by
      rw [inputSymbol_eq_getElem?, inputSymbol_eq_getElem?, (hA i).2, (hB i).2]
      simpa [Nat.ne_of_gt ha, show b ≠ 0 by omega] using hsym
    have hcong := step_congr_storage (tm := tm) (hq i) hsy
      (fun p p' => p + b = p' + a)
      (by rw [(hA i).2, (hB i).2]; omega) (fun dir => by
        have hm := moveInputPos_interior (c (A i)).inputPos (c (B i)).inputPos
          (by rw [(hA i).2]; exact ha) (by rw [(hA i).2]; omega)
          (by rw [(hB i).2]; omega) (by rw [(hB i).2]; exact hb) dir
        have := (hA i).2
        have := (hB i).2
        omega)
    simpa only [c, runFrom_succ_eq_step'] using hcong.2
  let R := fun p s => ∃ u, (c' u).inputPos.val = p ∧ (c' u).storage = s
  have hR₀ : R (c 0).inputPos.val (c 0).storage := by
    refine ⟨0, ?_, ?_⟩ <;> simp [c, c', Cfg.storage]
  have hlen : (input.take a ++ input.drop b).length + (b - a) = input.length := by
    simp only [List.length_append, List.length_take, List.length_drop]
    omega
  have hleft : ∀ u < T, (c u).inputPos.val ≤ a → (c (u + 1)).inputPos.val ≤ a →
      R (c u).inputPos.val (c u).storage → R (c (u + 1)).inputPos.val (c (u + 1)).storage := by
    rintro u _ hpu _ ⟨v, hpv, hsv⟩
    have hsy := inputSymbol_cut_left (by omega : a ≤ input.length) (c u) (c' v) hpu hpv
    have hcong := step_congr_storage (tm := tm) hsv.symm hsy Eq hpv.symm
      (fun dir => moveInputPos_same (c u).inputPos (c' v).inputPos hpv.symm
        (by omega) (by omega) dir)
    refine ⟨v + 1, ?_, ?_⟩
    · simpa only [c, c', runFrom_succ_eq_step'] using hcong.2.symm
    · simpa only [c, c', runFrom_succ_eq_step'] using hcong.1.symm
  have hright : ∀ u < T, b ≤ (c u).inputPos.val → b ≤ (c (u + 1)).inputPos.val →
      R ((c u).inputPos.val - (b - a)) (c u).storage →
      R ((c (u + 1)).inputPos.val - (b - a)) (c (u + 1)).storage := by
    rintro u _ hpu _ ⟨v, hpv, hsv⟩
    have hpv' : (c' v).inputPos.val + (b - a) = (c u).inputPos.val := by omega
    have hsy := inputSymbol_cut_right ha hab hb hsym (c u) (c' v) hpu hpv'
    have hcong := step_congr_storage (tm := tm) hsv.symm hsy
      (fun p p' => p' + (b - a) = p) hpv'
      (fun dir => moveInputPos_shift (c u).inputPos (c' v).inputPos hpv' hlen (by omega) dir)
    refine ⟨v + 1, ?_, ?_⟩
    · have hpos : (c' (v + 1)).inputPos.val + (b - a) = (c (u + 1)).inputPos.val := by
        simpa only [c, c', runFrom_succ_eq_step'] using hcong.2
      omega
    · simpa only [c, c', runFrom_succ_eq_step'] using hcong.1.symm
  have hglue := glue_visits (fun u => (c u).inputPos.val) (fun u => (c u).storage)
    hab (by simp [c]; omega)
    (fun u _ => by simpa only [c, runFrom_succ_eq_step'] using tm.inputPos_step_bounds (c u))
    A B hA hB hAc hBc hq hmove R hR₀ hleft hright t ht hp
  obtain ⟨u, _, hstore⟩ := hglue
  exact ⟨u, hstore⟩

/-- Every entry of a visit sequence is a storage reached by the run. -/
lemma mem_range_of_mem_visitSequence {cfg : Cfg k Symbol State input} {T p : ℕ}
    {s : Storage Symbol State k} (h : s ∈ tm.visitSequence cfg T p) :
    s ∈ Set.range (fun t => (tm.runFrom cfg t).storage) := by
  obtain ⟨t, _, rfl⟩ := List.mem_map.mp h
  exact ⟨t, rfl⟩

/-- A visit sequence of a halting space-bounded run has length at most the storage bound. -/
lemma length_visitSequence_le [Fintype Symbol] [Fintype State] {T s : ℕ}
    (hhalt : (tm.runFrom (tm.initCfg input) T).Halted)
    (hfirst : ∀ t < T, ¬ (tm.runFrom (tm.initCfg input) t).Halted)
    (hs : ∀ t, tm.spaceUsed (tm.initCfg input) t ≤ s) (p : ℕ) :
    (tm.visitSequence (tm.initCfg input) T p).length ≤ storageBound Symbol State k s := by
  classical
  have hn := tm.visitSequence_nodup hhalt hfirst p
  have hsub : ((tm.visitSequence (tm.initCfg input) T p).toFinset : Set _) ⊆
      Set.range (fun t => (tm.runFrom (tm.initCfg input) t).storage) := by
    intro x hx
    exact tm.mem_range_of_mem_visitSequence (List.mem_toFinset.mp hx)
  have hle := (Set.encard_le_encard hsub).trans (tm.encard_storages_le hs)
  rw [Set.encard_coe_eq_coe_finsetCard, List.toFinset_card_of_nodup hn] at hle
  exact_mod_cast hle

/-- A sufficiently long input to a halting space-bounded machine can be shortened while
preserving any designated storage reached by the run. -/
theorem exists_shorter_input_storage [Fintype Symbol] [Fintype State] {s : ℕ}
    (hhalt : ∃ T, (tm.runFrom (tm.initCfg input) T).Halted)
    (hs : ∀ t, tm.spaceUsed (tm.initCfg input) t ≤ s)
    (hlen : 2 * Fintype.card Symbol *
      (storageBound Symbol State k s + 1) ^ storageBound Symbol State k s < input.length)
    (t : ℕ) :
    ∃ input' : List Symbol, input'.length < input.length ∧
      ∃ u, (tm.runFrom (tm.initCfg input') u).storage =
        (tm.runFrom (tm.initCfg input) t).storage := by
  classical
  obtain ⟨T, hT, hfirst⟩ := Nat.findX hhalt
  wlog ht : t ≤ T generalizing t
  · simpa only [tm.runFrom_eq_of_halt (Nat.le_of_not_ge ht) hT] using this T le_rfl
  let B := storageBound Symbol State k s
  let S := Set.range (fun u => (tm.runFrom (tm.initCfg input) u).storage)
  have hbound : S.encard ≤ B := tm.encard_storages_le hs
  let : Fintype S := (Set.finite_of_encard_le_coe hbound).fintype
  have hcard : Fintype.card S ≤ B := by
    have h := hbound
    rw [← Set.coe_fintypeCard] at h
    exact_mod_cast h
  let seq := tm.visitSequence (tm.initCfg input) T
  let enc (p : ℕ) : List S := (seq p).attachWith (· ∈ S)
    (fun _ h => tm.mem_range_of_mem_visitSequence h)
  have henc (p : ℕ) : (enc p).map Subtype.val = seq p :=
    List.attachWith_map_subtype_val _
  have hlength (p : ℕ) : (enc p).length ≤ B := by
    simpa only [enc, List.length_attachWith] using tm.length_visitSequence_le hT hfirst hs p
  let f (i : Fin input.length) : Symbol × (Fin B → Option S) :=
    (input[i], fun j => (enc (i.val + 1))[j.val]?)
  have heq {i j : Fin input.length} (h : f i = f j) :
      input[i] = input[j] ∧ seq (i.val + 1) = seq (j.val + 1) := by
    refine ⟨congrArg Prod.fst h, ?_⟩
    have hh : enc (i.val + 1) = enc (j.val + 1) := by
      apply List.ext_getElem?
      intro r
      by_cases hr : r < B
      · exact congrFun (congrArg Prod.snd h) ⟨r, hr⟩
      · rw [List.getElem?_eq_none (by have := hlength (i.val + 1); omega),
          List.getElem?_eq_none (by have := hlength (j.val + 1); omega)]
    simpa only [henc] using congrArg (List.map Subtype.val) hh
  have hsig : Fintype.card (Symbol × (Fin B → Option S)) ≤
      Fintype.card Symbol * (B + 1) ^ B := by
    simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_option]
    gcongr
    omega
  obtain ⟨v, hv⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card f (n := 2) (by
    rw [Fintype.card_fin]
    change 2 * Fintype.card Symbol * (B + 1) ^ B < input.length at hlen
    calc Fintype.card (Symbol × (Fin B → Option S)) * 2
      _ ≤ (Fintype.card Symbol * (B + 1) ^ B) * 2 := Nat.mul_le_mul_right 2 hsig
      _ = 2 * Fintype.card Symbol * (B + 1) ^ B := by ring
      _ < input.length := hlen)
  let e := (Finset.univ.filter (fun i => f i = v)).orderEmbOfCardLe
    (show 3 ≤ (Finset.univ.filter (fun i => f i = v)).card by omega)
  have he (i : Fin 3) : f (e i) = v := by
    have hmem : e i ∈ Finset.univ.filter (fun i => f i = v) :=
      Finset.orderEmbOfCardLe_mem _ _ i
    exact (Finset.mem_filter.mp hmem).2
  have hab : (e 0).val + 1 < (e 1).val + 1 :=
    Nat.add_lt_add_right (e.strictMono (by decide)) 1
  have hbc : (e 1).val + 1 < (e 2).val + 1 :=
    Nat.add_lt_add_right (e.strictMono (by decide)) 1
  have hab' := heq ((he 0).trans (he 1).symm)
  have hbc' := heq ((he 1).trans (he 2).symm)
  have cut {i j : Fin input.length} (hij : i.val + 1 < j.val + 1)
      (hij' : input[i] = input[j] ∧ seq (i.val + 1) = seq (j.val + 1))
      (hpos : (tm.runFrom (tm.initCfg input) t).inputPos.val ≤ i.val + 1 ∨
        j.val + 1 ≤ (tm.runFrom (tm.initCfg input) t).inputPos.val) :
      ∃ input' : List Symbol, input'.length < input.length ∧
        ∃ u, (tm.runFrom (tm.initCfg input') u).storage =
          (tm.runFrom (tm.initCfg input) t).storage := by
    refine ⟨input.take (i.val + 1) ++ input.drop (j.val + 1), ?_, ?_⟩
    · simp only [List.length_append, List.length_take, List.length_drop]
      have := i.isLt
      have := j.isLt
      omega
    · exact tm.exists_storage_cut (by omega) hij (by have := j.isLt; omega)
        (by simpa [List.getElem?_eq_getElem i.isLt, List.getElem?_eq_getElem j.isLt] using hij'.1)
        hij'.2 ht hpos
  by_cases hpos : (tm.runFrom (tm.initCfg input) t).inputPos.val ≤ (e 0).val + 1 ∨
      (e 1).val + 1 ≤ (tm.runFrom (tm.initCfg input) t).inputPos.val
  · exact cut hab hab' hpos
  · exact cut hbc hbc' (Or.inl (by omega))

end Turing.MultiTapeTM
