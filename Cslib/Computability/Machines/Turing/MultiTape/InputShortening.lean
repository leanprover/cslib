/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/
module

public import Cslib.Computability.Machines.Turing.MultiTape.ConfigBound
public import Mathlib.Combinatorics.Pigeonhole
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Nat.Count
public import Mathlib.Data.Part
public import Mathlib.Order.Interval.Set.Infinite

/-!
# Input shortening for multi-tape Turing machines

A visit sequence records the storages seen at a fixed input position over the entire run.
Its entries are partial values (`Part`): searching for the `n`th visit returns its storage if that
visit occurs. Both definitions are computable and independent of halting.

Equal visit sequences allow an interval of the input to be deleted. Finite visit sets have distinct
storages, so their cardinalities are bounded by the storage bound. On a halting run only the final
input position has infinitely many visits; the counting argument omits that position.

The input-shortening argument follows Gadi Aleksandrowicz's account at
<https://gadial.net/2009/10/04/sub_loglog_space_is_constant/>.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}
variable {tm : MultiTapeTM k Symbol State}

/-- Runs starting with the same core keep the same core. -/
lemma core_runFrom_eq_of_core_eq {c₁ c₂ : Cfg k Symbol State input}
    (h : c₁.core = c₂.core) (t : ℕ) :
    (tm.runFrom c₁ t).core = (tm.runFrom c₂ t).core := by
  induction t with
  | zero => exact h
  | succ t ih =>
    simpa only [runFrom_succ_eq_step'] using core_step_eq_of_core_eq (tm := tm) ih

/-- All times when the input head is at position `p`. -/
def visitTimes (cfg : Cfg k Symbol State input) (p : ℕ) : Set ℕ :=
  {t | (tm.runFrom cfg t).inputPos.val = p}

@[simp]
lemma mem_visitTimes {cfg : Cfg k Symbol State input} {p t : ℕ} :
    t ∈ tm.visitTimes cfg p ↔ (tm.runFrom cfg t).inputPos.val = p := Iff.rfl

instance {cfg : Cfg k Symbol State input} {p : ℕ} :
    DecidablePred (· ∈ tm.visitTimes cfg p) := fun _ =>
  inferInstanceAs (Decidable ((_ : ℕ) = p))

/-- The storage at the `n`th visit to `p`, obtained by searching the run in time order.
An entry is undefined if that visit never occurs. No halting assumption is needed. -/
def visitSequence (cfg : Cfg k Symbol State input) (p : ℕ) :
    ℕ → Part (Storage Symbol State k) := fun n =>
  ⟨∃ t ∈ tm.visitTimes cfg p, Nat.count (· ∈ tm.visitTimes cfg p) t = n,
    fun h => (tm.runFrom cfg (Nat.find h)).storage⟩

/-- An entry records the storage at the visit with exactly `n` earlier visits. -/
lemma mem_visitSequence {cfg : Cfg k Symbol State input} {p n : ℕ}
    {s : Storage Symbol State k} :
    s ∈ tm.visitSequence cfg p n ↔ ∃ t ∈ tm.visitTimes cfg p,
      Nat.count (· ∈ tm.visitTimes cfg p) t = n ∧ (tm.runFrom cfg t).storage = s := by
  constructor
  · rintro ⟨h, hs⟩
    exact ⟨Nat.find h, (Nat.find_spec h).1, (Nat.find_spec h).2, hs⟩
  · rintro ⟨t, ht, hn, rfl⟩
    let h : ∃ u ∈ tm.visitTimes cfg p, Nat.count (· ∈ tm.visitTimes cfg p) u = n :=
      ⟨t, ht, hn⟩
    exact ⟨h, congrArg (fun u => (tm.runFrom cfg u).storage)
      (Nat.count_injective (Nat.find_spec h).1 ht ((Nat.find_spec h).2.trans hn.symm))⟩

/-- Equal visit sequences match visit times in order and preserve their storages. -/
lemma exists_visitTimes_orderIso {cfg : Cfg k Symbol State input} {a b : ℕ}
    (hseq : tm.visitSequence cfg a = tm.visitSequence cfg b) :
    ∃ e : tm.visitTimes cfg a ≃o tm.visitTimes cfg b,
      ∀ t : tm.visitTimes cfg a,
        (tm.runFrom cfg t).storage = (tm.runFrom cfg (e t)).storage := by
  have hmatch (t : tm.visitTimes cfg a) : ∃ u : tm.visitTimes cfg b,
      Nat.count (· ∈ tm.visitTimes cfg a) t = Nat.count (· ∈ tm.visitTimes cfg b) u ∧
        (tm.runFrom cfg t).storage = (tm.runFrom cfg u).storage := by
    have h := tm.mem_visitSequence.mpr ⟨t, t.property, rfl, rfl⟩
    rw [hseq] at h
    obtain ⟨u, hu, hn, hs⟩ := tm.mem_visitSequence.mp h
    exact ⟨⟨u, hu⟩, hn.symm, hs.symm⟩
  choose f hf hs using hmatch
  have hmono : StrictMono f := fun t u h => Nat.lt_of_count_lt_count (by
    rw [← hf t, ← hf u]
    exact Nat.count_strict_mono t.property h)
  have hsurj : Function.Surjective f := by
    intro u
    have h := tm.mem_visitSequence.mpr ⟨u, u.property, rfl, rfl⟩
    rw [← hseq] at h
    obtain ⟨t, ht, hn, _⟩ := tm.mem_visitSequence.mp h
    exact ⟨⟨t, ht⟩, Subtype.ext (Nat.count_injective (f ⟨t, ht⟩).property u.property
      ((hf ⟨t, ht⟩).symm.trans hn))⟩
  exact ⟨OrderIso.ofSurjective (OrderEmbedding.ofStrictMono f hmono) hsurj, hs⟩

/-- The final input position has infinitely many visits, since the halted configuration repeats. -/
lemma visitTimes_infinite_of_halt {cfg : Cfg k Symbol State input} {T : ℕ}
    (hhalt : (tm.runFrom cfg T).Halted) :
    (tm.visitTimes cfg (tm.runFrom cfg T).inputPos.val).Infinite := by
  apply Set.Infinite.mono ?_ (Set.Ici_infinite T)
  intro t ht
  exact congrArg (fun c => c.inputPos.val) (tm.runFrom_eq_of_halt ht hhalt)

/-- Visits to any other input position occur strictly before a halting time. -/
lemma visitTimes_subset_Iio_of_halt {cfg : Cfg k Symbol State input} {T p : ℕ}
    (hhalt : (tm.runFrom cfg T).Halted) (hp : p ≠ (tm.runFrom cfg T).inputPos.val) :
    tm.visitTimes cfg p ⊆ Set.Iio T := by
  intro t ht
  change t < T
  by_contra! h
  exact hp (ht.symm.trans (congrArg (fun c => c.inputPos.val)
    (tm.runFrom_eq_of_halt h hhalt)))

/-- On a halting run, the visit set is finite exactly away from the final input position. -/
lemma visitTimes_finite_iff_of_halt {cfg : Cfg k Symbol State input} {T p : ℕ}
    (hhalt : (tm.runFrom cfg T).Halted) :
    (tm.visitTimes cfg p).Finite ↔ p ≠ (tm.runFrom cfg T).inputPos.val := by
  constructor
  · intro hf hp
    exact tm.visitTimes_infinite_of_halt hhalt (hp ▸ hf)
  · intro hp
    exact (Set.finite_Iio T).subset (tm.visitTimes_subset_Iio_of_halt hhalt hp)

/-- If every work head stays in `[-R, R]`, the run visits at most `k * (2 * R + 1)` cells. -/
lemma spaceUsed_le_of_workTapePos_natAbs_le (cfg : Cfg k Symbol State input) (T R : ℕ)
    (h : ∀ t ≤ T, ∀ i, ((tm.runFrom cfg t).workTapePos i).natAbs ≤ R) :
    tm.spaceUsed cfg T ≤ k * (2 * R + 1) := by
  calc tm.spaceUsed cfg T
    _ ≤ ∑ _ : Fin k, (window R).card := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.card_le_card
      intro z hz
      obtain ⟨t, ht, rfl⟩ := tm.mem_visitedByTapeHead.mp hz
      exact mem_window.mpr (h t (by omega) i)
    _ = k * (2 * R + 1) := by simp

/-- Equal storage and input symbols give equal storage after one step. A relation `r` between
the input positions is also preserved if it holds after every common head move. -/
lemma step_congr_storage {input' : List Symbol}
    {c : Cfg k Symbol State input} {c' : Cfg k Symbol State input'}
    (hstore : c.storage = c'.storage) (hsym : c.inputSymbol = c'.inputSymbol)
    (r : ℕ → ℕ → Prop)
    (hm : ∀ m, r (moveInputPos c.inputPos m).val (moveInputPos c'.inputPos m).val) :
    (tm.step c).storage = (tm.step c').storage ∧
      r (tm.step c).inputPos.val (tm.step c').inputPos.val := by
  rcases c with ⟨state, pos, tapes, heads, out⟩
  rcases c' with ⟨state', pos', tapes', heads', out'⟩
  simp only [Cfg.storage, Storage.mk.injEq] at hstore
  rcases hstore with ⟨rfl, rfl, rfl⟩
  cases state with
  | none => exact ⟨rfl, by simpa only [moveInputPos_zero, step] using hm 0⟩
  | some state =>
    dsimp only [step]
    unfold Cfg.workTapeSymbols
    rw [hsym]
    exact ⟨rfl, hm _⟩

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
private lemma glue_visits {S : Type*} (p : ℕ → ℕ) (q : ℕ → S) {a b : ℕ}
    (hab : a < b) (hp₀ : p 0 ≤ a)
    (hstep : ∀ t, p (t + 1) ≤ p t + 1 ∧ p t ≤ p (t + 1) + 1)
    (e : {t // p t = a} ≃o {t // p t = b})
    (hq : ∀ t : {t // p t = a}, q t = q (e t))
    (hmove : ∀ t : {t // p t = a}, p (t + 1) + b = p (e t + 1) + a)
    (R : ℕ → S → Prop) (hR₀ : R (p 0) (q 0))
    (hleft : ∀ t, p t ≤ a → p (t + 1) ≤ a →
      R (p t) (q t) → R (p (t + 1)) (q (t + 1)))
    (hright : ∀ t, b ≤ p t → b ≤ p (t + 1) →
      R (p t - (b - a)) (q t) → R (p (t + 1) - (b - a)) (q (t + 1))) :
    ∀ t, p t ≤ a ∨ b ≤ p t →
      R (if p t ≤ a then p t else p t - (b - a)) (q t) := by
  classical
  have hba : b - (b - a) = a := by omega
  have boundary : ∀ t, p t = a → R a (q t) := by
    intro t
    induction t using Nat.strong_induction_on with
    | h t ih =>
      intro ht
      by_cases hex : ∃ u < t, p u = a
      · obtain ⟨u, hut, hu, hno⟩ :
          ∃ u < t, p u = a ∧ ∀ v, u < v → v < t → p v ≠ a := by
          obtain ⟨v, hvt, hv⟩ := hex
          refine ⟨Nat.findGreatest (fun u => p u = a) (t - 1),
            lt_of_le_of_lt (Nat.findGreatest_le _) (by omega),
            Nat.findGreatest_spec (P := fun u => p u = a) (by omega) hv, ?_⟩
          exact fun w huw hwt hw => (not_le_of_gt huw)
            (Nat.le_findGreatest (P := fun u => p u = a) (by omega) hw)
        let i : {t // p t = a} := ⟨u, hu⟩
        let j : {t // p t = a} := ⟨t, ht⟩
        by_cases hdir : p (u + 1) ≤ a
        · have hside := walk_left (fun v _ _ => (hstep v).1) hu.le hdir hno
          have hr := propagate hut.le (show R (p u) (q u) from hu ▸ ih u hut hu)
            fun v huv hvt => hleft v (hside v huv hvt.le) (hside (v + 1) (by omega) hvt)
          simpa [ht] using hr
        · have hdir' : b ≤ p (e i + 1) := by
            have h := hmove i
            change p (u + 1) + b = p (e i + 1) + a at h
            omega
          have hno' : ∀ v, (e i).val < v → v < (e j).val → p v ≠ b := by
            intro v hiv hvj hv
            let w : {t // p t = b} := ⟨v, hv⟩
            exact hno (e.symm w)
              (show i < e.symm w from e.lt_symm_apply.mpr (show e i < w from hiv))
              (show e.symm w < j from e.symm_apply_lt.mpr (show w < e j from hvj))
              (e.symm w).property
          have hside := walk_right (fun v _ _ => (hstep v).2) (e i).property.ge hdir' hno'
          have hr := propagate (e.strictMono hut).le
            (show R (p (e i) - (b - a)) (q (e i)) by
              simpa only [(e i).property, hba, ← hq i] using ih u hut hu)
            fun v huv hvt => hright v (hside v huv hvt.le) (hside (v + 1) (by omega) hvt)
          simpa only [(e j).property, hba, ← hq j] using hr
      · have hside : ∀ u ≤ t, p u ≤ a := by
          intro u hut
          apply propagate (Nat.zero_le u) hp₀
          intro v _ hvu hv
          have := (hstep v).1
          have : p v ≠ a := fun h => hex ⟨v, by omega, h⟩
          omega
        have hr := propagate (Nat.zero_le t) hR₀ fun u _ hut =>
          hleft u (hside u hut.le) (hside (u + 1) hut)
        simpa [ht] using hr
  intro t
  induction t with
  | zero => intro _; simpa [hp₀] using hR₀
  | succ t ih =>
    intro hside
    have hst := hstep t
    by_cases hl : p (t + 1) ≤ a
    · rw [ite_eq_left hl]
      by_cases heq : p (t + 1) = a
      · simpa [heq] using boundary (t + 1) heq
      · have hprev : p t ≤ a := by omega
        exact hleft t hprev hl (by simpa [hprev] using ih (Or.inl hprev))
    · rw [ite_eq_right hl]
      have hr : b ≤ p (t + 1) := hside.resolve_left hl
      by_cases heq : p (t + 1) = b
      · let j : {t // p t = b} := ⟨t + 1, heq⟩
        simpa only [hq (e.symm j), e.apply_symm_apply, heq, hba] using
          boundary (e.symm j) (e.symm j).property
      · have hprev : b ≤ p t := by omega
        have hprev' : ¬ p t ≤ a := by omega
        exact hright t hprev hr (by simpa [hprev'] using ih (Or.inr hprev))

/-- Deleting the cells after `a` through `b` preserves every storage reached outside the deleted
interval, provided the symbols and visit sequences at `a` and `b` agree.
Input positions are one-based, as in `Cfg.inputPos`; neither cut position is an endmarker. -/
theorem exists_storage_cut {a b : ℕ}
    (ha : 0 < a) (hab : a < b) (hb : b ≤ input.length)
    (hsym : input[a - 1]? = input[b - 1]?)
    (hseq : tm.visitSequence (tm.initCfg input) a =
      tm.visitSequence (tm.initCfg input) b)
    {t : ℕ}
    (hp : (tm.runFrom (tm.initCfg input) t).inputPos.val ≤ a ∨
      b ≤ (tm.runFrom (tm.initCfg input) t).inputPos.val) :
    ∃ u, (tm.runFrom (tm.initCfg (input.take a ++ input.drop b)) u).storage =
      (tm.runFrom (tm.initCfg input) t).storage := by
  classical
  obtain ⟨e, hq⟩ := tm.exists_visitTimes_orderIso hseq
  let c := tm.runFrom (tm.initCfg input)
  let c' := tm.runFrom (tm.initCfg (input.take a ++ input.drop b))
  have hA (i : tm.visitTimes (tm.initCfg input) a) : (c i).inputPos.val = a := i.property
  have hB (i : tm.visitTimes (tm.initCfg input) a) : (c (e i)).inputPos.val = b := (e i).property
  have hmove (i : tm.visitTimes (tm.initCfg input) a) :
      (c (i.val + 1)).inputPos.val + b = (c (e i + 1)).inputPos.val + a := by
    have hsy : (c i).inputSymbol = (c (e i)).inputSymbol := by
      rw [inputSymbol_eq_getElem?, inputSymbol_eq_getElem?, hA i, hB i]
      simpa [Nat.ne_of_gt ha, show b ≠ 0 by omega] using hsym
    have hcong := step_congr_storage (tm := tm)
      (show (c i).storage = (c (e i)).storage from hq i) hsy
      (fun p p' => p + b = p' + a) (fun dir => by
        have hm := moveInputPos_interior (c i).inputPos (c (e i)).inputPos
          (by rw [hA i]; exact ha) (by rw [hA i]; omega)
          (by rw [hB i]; omega) (by rw [hB i]; exact hb) dir
        have := hA i
        have := hB i
        omega)
    simpa only [c, runFrom_succ_eq_step'] using hcong.2
  let R := fun p s => ∃ u, (c' u).inputPos.val = p ∧ (c' u).storage = s
  have hR₀ : R (c 0).inputPos.val (c 0).storage := by
    refine ⟨0, ?_, ?_⟩ <;> simp [c, c', Cfg.storage]
  have hlen : (input.take a ++ input.drop b).length + (b - a) = input.length := by
    simp only [List.length_append, List.length_take, List.length_drop]
    omega
  have hleft : ∀ u, (c u).inputPos.val ≤ a → (c (u + 1)).inputPos.val ≤ a →
      R (c u).inputPos.val (c u).storage → R (c (u + 1)).inputPos.val (c (u + 1)).storage := by
    rintro u hpu _ ⟨v, hpv, hsv⟩
    have hsy := inputSymbol_cut_left (by omega : a ≤ input.length) (c u) (c' v) hpu hpv
    have hcong := step_congr_storage (tm := tm) hsv.symm hsy Eq
      (fun dir => moveInputPos_same (c u).inputPos (c' v).inputPos hpv.symm
        (by omega) (by omega) dir)
    refine ⟨v + 1, ?_, ?_⟩
    · simpa only [c, c', runFrom_succ_eq_step'] using hcong.2.symm
    · simpa only [c, c', runFrom_succ_eq_step'] using hcong.1.symm
  have hright : ∀ u, b ≤ (c u).inputPos.val → b ≤ (c (u + 1)).inputPos.val →
      R ((c u).inputPos.val - (b - a)) (c u).storage →
      R ((c (u + 1)).inputPos.val - (b - a)) (c (u + 1)).storage := by
    rintro u hpu _ ⟨v, hpv, hsv⟩
    have hpv' : (c' v).inputPos.val + (b - a) = (c u).inputPos.val := by omega
    have hsy := inputSymbol_cut_right ha hab hb hsym (c u) (c' v) hpu hpv'
    have hcong := step_congr_storage (tm := tm) hsv.symm hsy
      (fun p p' => p' + (b - a) = p)
      (fun dir => moveInputPos_shift (c u).inputPos (c' v).inputPos hpv' hlen (by omega) dir)
    refine ⟨v + 1, ?_, ?_⟩
    · have hpos : (c' (v + 1)).inputPos.val + (b - a) = (c (u + 1)).inputPos.val := by
        simpa only [c, c', runFrom_succ_eq_step'] using hcong.2
      omega
    · simpa only [c, c', runFrom_succ_eq_step'] using hcong.1.symm
  have hglue := glue_visits (fun u => (c u).inputPos.val) (fun u => (c u).storage)
    hab (by simp [c]; omega)
    (fun u => by simpa only [c, runFrom_succ_eq_step'] using tm.inputPos_step_bounds (c u))
    e hq hmove R hR₀ hleft hright t hp
  obtain ⟨u, _, hstore⟩ := hglue
  exact ⟨u, hstore⟩

/-- A finite set of visits has distinct storages: a repeated core would force another visit
strictly after the last one. -/
lemma storage_runFrom_injOn_visitTimes {cfg : Cfg k Symbol State input} {p : ℕ}
    (hf : (tm.visitTimes cfg p).Finite) :
    Set.InjOn (fun t => (tm.runFrom cfg t).storage) (tm.visitTimes cfg p) := by
  intro a ha b hb heq
  wlog hab : a ≤ b generalizing a b
  · exact (this hb ha heq.symm (le_of_not_ge hab)).symm
  obtain ⟨T, hT, hmax⟩ := hf.toFinset.exists_max_image id ⟨a, hf.mem_toFinset.mpr ha⟩
  have haT : a ≤ T := hmax a (hf.mem_toFinset.mpr ha)
  have hcore := tm.core_runFrom_eq_of_core_eq
    (Prod.ext (Fin.ext (ha.trans hb.symm)) heq) (T - a)
  rw [← runFrom_add, ← runFrom_add, Nat.add_sub_of_le haT] at hcore
  have hvisit : b + (T - a) ∈ tm.visitTimes cfg p :=
    (congrArg Fin.val (congrArg Prod.fst hcore)).symm.trans (hf.mem_toFinset.mp hT)
  have := hmax _ (hf.mem_toFinset.mpr hvisit)
  dsimp only [id] at this
  omega

/-- A finite visit set of a space-bounded run has cardinality at most the storage bound. -/
lemma encard_visitTimes_le [Fintype Symbol] [Fintype State] {s p : ℕ}
    (hs : ∀ t, tm.spaceUsed (tm.initCfg input) t ≤ s)
    (hf : (tm.visitTimes (tm.initCfg input) p).Finite) :
    (tm.visitTimes (tm.initCfg input) p).encard ≤ storageBound Symbol State k s :=
  (Set.encard_le_encard_of_injOn
    (t := Set.range (fun t => (tm.runFrom (tm.initCfg input) t).storage)) (fun t _ => ⟨t, rfl⟩)
    (tm.storage_runFrom_injOn_visitTimes hf)).trans (tm.encard_storages_le hs)

/-- A sufficiently long input to a halting space-bounded machine can be shortened while
preserving any designated storage reached by the run. The extra `1` in the length threshold
accounts for omitting the final input position from the counting argument. -/
theorem exists_shorter_input_storage [Fintype Symbol] [Fintype State] {s : ℕ}
    (hhalt : ∃ T, (tm.runFrom (tm.initCfg input) T).Halted)
    (hs : ∀ t, tm.spaceUsed (tm.initCfg input) t ≤ s)
    (hlen : 2 * Fintype.card Symbol *
      (storageBound Symbol State k s + 1) ^ storageBound Symbol State k s + 1 < input.length)
    (t : ℕ) :
    ∃ input' : List Symbol, input'.length < input.length ∧
      ∃ u, (tm.runFrom (tm.initCfg input') u).storage =
        (tm.runFrom (tm.initCfg input) t).storage := by
  classical
  let B := storageBound Symbol State k s
  let S := Set.range (fun u => (tm.runFrom (tm.initCfg input) u).storage)
  have hbound : S.encard ≤ B := tm.encard_storages_le hs
  let : Fintype S := (Set.finite_of_encard_le_coe hbound).fintype
  have hcard : Fintype.card S ≤ B := by
    have h := hbound
    rw [← Set.coe_fintypeCard] at h
    exact_mod_cast h
  obtain ⟨T, hT⟩ := hhalt
  let D := {i : Fin input.length //
    i.val + 1 ≠ (tm.runFrom (tm.initCfg input) T).inputPos.val}
  have hsize : input.length - 1 ≤ Fintype.card D := by
    have hbad : Fintype.card {i : Fin input.length //
        i.val + 1 = (tm.runFrom (tm.initCfg input) T).inputPos.val} ≤ 1 := by
      apply Fintype.card_le_one_iff.mpr
      intro i j
      apply Subtype.ext
      apply Fin.ext
      have := i.property
      have := j.property
      omega
    dsimp only [D]
    rw [Fintype.card_subtype_compl, Fintype.card_fin]
    omega
  have hfinite (i : D) : (tm.visitTimes (tm.initCfg input) (i.val.val + 1)).Finite :=
    (tm.visitTimes_finite_iff_of_halt hT).mpr i.property
  let enc (p n : ℕ) : Option S :=
    if h : (tm.visitSequence (tm.initCfg input) p n).Dom then
      some ⟨(tm.visitSequence (tm.initCfg input) p n).get h, by
        obtain ⟨u, _, _, hu⟩ := tm.mem_visitSequence.mp (Part.get_mem h)
        exact ⟨u, hu⟩⟩
    else none
  have henc (p n : ℕ) : (enc p n).map Subtype.val =
      (tm.visitSequence (tm.initCfg input) p n).toOption := by
    dsimp only [enc, Part.toOption]
    split_ifs <;> rfl
  have hindex (i : D) {n : ℕ} (hn : (tm.visitSequence (tm.initCfg input) (i.val.val + 1) n).Dom) :
      n < B := by
    obtain ⟨u, hu, rfl⟩ := hn
    have hbound := tm.encard_visitTimes_le hs (hfinite i)
    rw [← Set.Finite.coe_toFinset (hfinite i), Set.encard_coe_eq_coe_finsetCard] at hbound
    exact (Nat.count_lt_card (hfinite i) hu).trans_le (by exact_mod_cast hbound)
  let f (i : D) : Symbol × (Fin B → Option S) :=
    (input[i.val], fun j => enc (i.val.val + 1) j)
  have heq {i j : D} (h : f i = f j) :
      input[i.val] = input[j.val] ∧ tm.visitSequence (tm.initCfg input) (i.val.val + 1) =
        tm.visitSequence (tm.initCfg input) (j.val.val + 1) := by
    refine ⟨congrArg Prod.fst h, funext fun n => ?_⟩
    by_cases hn : n < B
    · have he := congrArg (Option.map Subtype.val) (congrFun (congrArg Prod.snd h) ⟨n, hn⟩)
      change (enc (i.val.val + 1) n).map Subtype.val = (enc (j.val.val + 1) n).map Subtype.val at he
      simpa only [henc, Part.of_toOption] using congrArg Part.ofOption he
    · rw [Part.eq_none_iff'.mpr (fun hd => hn (hindex i hd)),
        Part.eq_none_iff'.mpr (fun hd => hn (hindex j hd))]
  have hsig : Fintype.card (Symbol × (Fin B → Option S)) ≤
      Fintype.card Symbol * (B + 1) ^ B := by
    simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_option]
    gcongr
    omega
  obtain ⟨v, hv⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card f (n := 2) (by
    change 2 * Fintype.card Symbol * (B + 1) ^ B + 1 < input.length at hlen
    calc Fintype.card (Symbol × (Fin B → Option S)) * 2
      _ ≤ (Fintype.card Symbol * (B + 1) ^ B) * 2 := Nat.mul_le_mul_right 2 hsig
      _ = 2 * Fintype.card Symbol * (B + 1) ^ B := by ring
      _ < Fintype.card D := by omega)
  let eD := (Finset.univ.filter (fun i => f i = v)).orderEmbOfCardLe
    (show 3 ≤ (Finset.univ.filter (fun i => f i = v)).card by omega)
  let e : Fin 3 ↪o Fin input.length := eD.trans (OrderEmbedding.subtype _)
  have he (i : Fin 3) : f (eD i) = v := by
    have hmem : eD i ∈ Finset.univ.filter (fun i => f i = v) :=
      Finset.orderEmbOfCardLe_mem _ _ i
    exact (Finset.mem_filter.mp hmem).2
  have hab : (e 0).val + 1 < (e 1).val + 1 :=
    Nat.add_lt_add_right (e.strictMono (by decide)) 1
  have hbc : (e 1).val + 1 < (e 2).val + 1 :=
    Nat.add_lt_add_right (e.strictMono (by decide)) 1
  have hab' := heq ((he 0).trans (he 1).symm)
  have hbc' := heq ((he 1).trans (he 2).symm)
  have cut {i j : Fin input.length} (hij : i.val + 1 < j.val + 1)
      (hij' : input[i] = input[j] ∧ tm.visitSequence (tm.initCfg input) (i.val + 1) =
        tm.visitSequence (tm.initCfg input) (j.val + 1))
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
        hij'.2 hpos
  by_cases hpos : (tm.runFrom (tm.initCfg input) t).inputPos.val ≤ (e 0).val + 1 ∨
      (e 1).val + 1 ≤ (tm.runFrom (tm.initCfg input) t).inputPos.val
  · exact cut hab hab' hpos
  · exact cut hbc hbc' (Or.inl (by omega))

end Turing.MultiTapeTM
