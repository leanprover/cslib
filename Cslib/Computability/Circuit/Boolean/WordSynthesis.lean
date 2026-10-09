/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Cslib.Computability.Circuit.Boolean.Complexity
public import Cslib.Computability.Circuit.Boolean.FiniteSynthesis
public import Cslib.Foundations.Data.BitString
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring

/-!
# Circuit synthesis for words

A word is observed through indicators for its length and for each optional indexed symbol up
to a capacity. `WordSynthesis` bundles a length bound with a synthesis of these observations
from available functions. Word operations are its closure rules: each reads the observations
of its arguments and produces those of its result, with a gate count polynomial in the
capacities. How words are laid out on wires is left to
`Cslib.Computability.Circuit.Boolean.Encoding`, so no rule here mentions a codec.
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

variable {n : ℕ}

namespace Word

variable {capacity : ℕ} {f g : (Fin n → Bool) → BitString}

/-- Indicators for a word's length and optional indexed symbols, including the right boundary. -/
def observations (f : (Fin n → Bool) → BitString) (capacity : ℕ) : Set (BooleanFunction n) :=
  Boolean.observations (fun w (i : Fin (capacity + 1)) => decide (w.length = i.val)) f ∪
    Boolean.observations (fun w (ib : Fin (capacity + 1) × Option Bool) =>
      decide (w[ib.1.val]? = ib.2)) f

/-- The observations as one indexed family, for extracting a circuit. -/
theorem observations_eq_range : observations f capacity = Set.range (Sum.elim
    (fun (i : Fin (capacity + 1)) x => decide ((f x).length = i.val))
    (fun (ib : Fin (capacity + 1) × Option Bool) x => decide ((f x)[ib.1.val]? = ib.2))) :=
  (Set.Sum.elim_range _ _).symm

theorem length_mem_observations (i : Fin (capacity + 1)) :
    (fun x => decide ((f x).length = i.val)) ∈ observations f capacity :=
  Set.mem_union_left _ ⟨i, rfl⟩

theorem symbol_mem_observations (i : Fin (capacity + 1)) (b : Option Bool) :
    (fun x => decide ((f x)[i.val]? = b)) ∈ observations f capacity :=
  Set.mem_union_right _ ⟨(i, b), rfl⟩

/-- Access an available length indicator. -/
theorem synthesis_length (i : Fin (capacity + 1)) :
    Synthesis interpretation (observations f capacity)
      {fun x => decide ((f x).length = i.val)} 0 :=
  Synthesis.of_mem (length_mem_observations i)

/-- Access an available symbol indicator. -/
theorem synthesis_symbol (i : Fin (capacity + 1)) (b : Option Bool) :
    Synthesis interpretation (observations f capacity) {fun x => decide ((f x)[i.val]? = b)} 0 :=
  Synthesis.of_mem (symbol_mem_observations i b)

/-- An out-of-range symbol is a constant; an in-range symbol is already available. -/
theorem synthesis_getElem (hf : ∀ x, (f x).length ≤ capacity) (i : ℕ) (b : Option Bool) :
    Synthesis interpretation (observations f capacity) {fun x => decide ((f x)[i]? = b)} 1 := by
  by_cases hi : i ≤ capacity
  · exact (synthesis_symbol ⟨i, by lia⟩ b).mono_cost (Nat.zero_le _)
  · refine (Synthesis.const (decide (none = b))).congr fun x => ?_
    rw [List.getElem?_eq_none (by have := hf x; lia)]

/-- Test any natural length, including values beyond the capacity. -/
theorem synthesis_length_eq (hf : ∀ x, (f x).length ≤ capacity) (i : ℕ) :
    Synthesis interpretation (observations f capacity) {fun x => decide ((f x).length = i)} 1 := by
  by_cases hi : i ≤ capacity
  · exact (synthesis_length ⟨i, by lia⟩).mono_cost (Nat.zero_le _)
  · refine (Synthesis.const false).congr fun x => ?_
    rw [eq_comm, decide_eq_false_iff_not]
    have := hf x
    lia

/-- Any predicate of the length is a lookup on the length indicators. -/
theorem synthesis_length_op (hf : ∀ x, (f x).length ≤ capacity) (op : ℕ → Bool) :
    Synthesis interpretation (observations f capacity) {fun x => op (f x).length}
      (capacity + 2) := by
  simpa using Synthesis.of_indicators
    (f := fun x => (⟨(f x).length, by have := hf x; lia⟩ : Fin (capacity + 1)))
    (fun i => op i.val) (fun i => synthesis_length i)

/-- Assemble the observations using a common bound for each indicator. -/
theorem synthesis_observations {s : Set (BooleanFunction n)} {cost : ℕ}
    (hlen : ∀ i : Fin (capacity + 1),
      Synthesis interpretation s {fun x => decide ((f x).length = i.val)} cost)
    (hbit : ∀ (i : Fin (capacity + 1)) (b : Option Bool),
      Synthesis interpretation s {fun x => decide ((f x)[i.val]? = b)} cost) :
    Synthesis interpretation s (observations f capacity) (4 * (capacity + 1) * cost) := by
  have h := (Boolean.synthesis_observations
      (fun w (i : Fin (capacity + 1)) => decide (w.length = i.val)) f hlen).union
    (Boolean.synthesis_observations
      (fun w (ib : Fin (capacity + 1) × Option Bool) => decide (w[ib.1.val]? = ib.2)) f
      fun ib => hbit ib.1 ib.2)
  unfold observations
  convert h using 1
  simp only [Fintype.card_fin, Fintype.card_prod, Fintype.card_option, Fintype.card_bool]
  ring

/-- A constant word has constant indicators. -/
theorem synthesis_const {s : Set (BooleanFunction n)} (value : BitString) :
    Synthesis interpretation s (observations (fun _ => value) value.length)
      (4 * (value.length + 1)) := by
  simpa using synthesis_observations (f := fun _ => value) (capacity := value.length)
    (cost := 1) (fun i => Synthesis.const _) (fun i b => Synthesis.const _)

/-- Concatenation uses the first word's length to select each output observation. -/
theorem synthesis_append {m k : ℕ} (hf : ∀ x, (f x).length ≤ m) (hg : ∀ x, (g x).length ≤ k) :
    Synthesis interpretation (observations f m ∪ observations g k)
      (observations (fun x => f x ++ g x) (m + k))
      (4 * (m + k + 1) * (3 * (m + 1) + 1)) := by
  let s := observations f m ∪ observations g k
  have select (branch : ℕ → BooleanFunction n)
      (hb : ∀ j ∈ Finset.range (m + 1), Synthesis interpretation s {branch j} 1) :
      Synthesis interpretation s {fun x => branch (f x).length x} (3 * (m + 1) + 1) := by
    simpa [Nat.mul_comm] using Synthesis.select (Finset.range (m + 1))
      (fun x => (f x).length) branch (fun x => by simp only [Finset.mem_range]; have := hf x; lia)
      (fun j hj => (synthesis_length (f := f) ⟨j, Finset.mem_range.mp hj⟩).mono_sources
        Set.subset_union_left) hb
  apply synthesis_observations
  · intro i
    refine (select (fun j x => decide (j ≤ i.val) && decide ((g x).length = i.val - j))
      (fun j _ => by
        by_cases hj : j ≤ i.val
        · simpa [hj] using (synthesis_length_eq hg (i.val - j)).mono_sources Set.subset_union_right
        · simpa [hj] using Synthesis.const (s := s) false)).congr fun x => ?_
    simp only [List.length_append]
    lia
  · intro i b
    refine (select (fun j x => if i.val < j then decide ((f x)[i.val]? = b)
      else decide ((g x)[i.val - j]? = b)) (fun j _ => by
        split
        · exact (synthesis_getElem hf i.val b).mono_sources Set.subset_union_left
        · exact (synthesis_getElem hg (i.val - j) b).mono_sources Set.subset_union_right)).congr
      fun x => ?_
    by_cases hi : i.val < (f x).length <;> simp [List.getElem?_append, hi]

/-- Reversal selects the source index using the word's actual length. -/
theorem synthesis_reverse (hf : ∀ x, (f x).length ≤ capacity) :
    Synthesis interpretation (observations f capacity)
      (observations (fun x => (f x).reverse) capacity)
      (4 * (capacity + 1) * (3 * (capacity + 1) + 1)) := by
  apply synthesis_observations
  · intro i
    simpa only [List.length_reverse] using (synthesis_length (f := f) i).mono_cost (Nat.zero_le _)
  · intro i b
    have h := Synthesis.select (Finset.range (capacity + 1)) (fun x => (f x).length)
      (fun len x => if i.val < len then decide ((f x)[len - 1 - i.val]? = b)
        else decide (none = b)) (fun x => by simp only [Finset.mem_range]; have := hf x; lia)
      (fun j hj => synthesis_length ⟨j, Finset.mem_range.mp hj⟩)
      (fun j _ => by
        split
        · exact synthesis_getElem hf (j - 1 - i.val) b
        · exact Synthesis.const (decide (none = b)))
    refine (h.congr fun x => ?_).mono_cost (by simp [Nat.mul_comm])
    by_cases hi : i.val < (f x).length
    · simp [hi, List.getElem?_eq_getElem (by lia : (f x).length - 1 - i.val < (f x).length)]
    · simp [hi]

/-- Bitwise mapping changes the three possible optional symbols by a fixed lookup. -/
theorem synthesis_map (op : Bool → Bool) :
    Synthesis interpretation (observations f capacity)
      (observations (fun x => (f x).map op) capacity) (4 * (capacity + 1) * 4) := by
  apply synthesis_observations
  · intro i
    simpa only [List.length_map] using (synthesis_length (f := f) i).mono_cost (Nat.zero_le _)
  · intro i b
    simpa only [List.getElem?_map, Fintype.card_option, Fintype.card_bool] using
      Synthesis.of_indicators (fun symbol : Option Bool => decide (symbol.map op = b))
        (fun symbol => synthesis_symbol i symbol)

/-- A conditional selects every observation by its condition. -/
theorem synthesis_ite {c : BooleanFunction n} {m k : ℕ}
    (hf : ∀ x, (f x).length ≤ m) (hg : ∀ x, (g x).length ≤ k) :
    Synthesis interpretation ({c} ∪ observations f m ∪ observations g k)
      (observations (fun x => if c x then f x else g x) (max m k))
      (4 * (max m k + 1) * 6) := by
  have hc : Synthesis interpretation ({c} ∪ observations f m ∪ observations g k) {c} 0 :=
    Synthesis.of_mem (Set.mem_union_left _ (Set.mem_union_left _ rfl))
  have hsf : observations f m ⊆ {c} ∪ observations f m ∪ observations g k :=
    Set.subset_union_right.trans Set.subset_union_left
  apply synthesis_observations
  · intro i
    refine (hc.ite ((synthesis_length_eq hf i.val).mono_sources hsf)
      ((synthesis_length_eq hg i.val).mono_sources Set.subset_union_right)).congr fun x => ?_
    cases c x <;> simp
  · intro i b
    refine (hc.ite ((synthesis_getElem hf i.val b).mono_sources hsf)
      ((synthesis_getElem hg i.val b).mono_sources Set.subset_union_right)).congr fun x => ?_
    cases c x <;> simp

/-- A prefix of fixed length keeps the symbols below it. -/
theorem synthesis_take (hf : ∀ x, (f x).length ≤ capacity) (k : ℕ) :
    Synthesis interpretation (observations f capacity)
      (observations (fun x => (f x).take k) k) (4 * (k + 1) * (capacity + 2)) := by
  apply synthesis_observations
  · intro i
    simpa only [List.length_take] using
      synthesis_length_op hf fun len => decide (min k len = i.val)
  · intro i b
    by_cases hi : i.val < k
    · simpa only [List.getElem?_take_of_lt hi] using
        (synthesis_getElem hf i.val b).mono_cost (by lia)
    · simpa only [List.getElem?_take_eq_none (by lia : k ≤ i.val)] using
        (Synthesis.const (decide (none = b))).mono_cost (by lia)

/-- Dropping a fixed prefix shifts the symbols. -/
theorem synthesis_drop (hf : ∀ x, (f x).length ≤ capacity) (k : ℕ) :
    Synthesis interpretation (observations f capacity)
      (observations (fun x => (f x).drop k) capacity) (4 * (capacity + 1) * (capacity + 2)) := by
  apply synthesis_observations
  · intro i
    simpa only [List.length_drop] using synthesis_length_op hf fun len => decide (len - k = i.val)
  · intro i b
    simpa only [List.getElem?_drop] using (synthesis_getElem hf (k + i.val) b).mono_cost (by lia)

/-- A bitwise binary operation combines the optional symbols at each index. -/
theorem synthesis_zipWith (op : Bool → Bool → Bool) {m k : ℕ}
    (hf : ∀ x, (f x).length ≤ m) (hg : ∀ x, (g x).length ≤ k) :
    Synthesis interpretation (observations f m ∪ observations g k)
      (observations (fun x => List.zipWith op (f x) (g x)) (min m k))
      (4 * (min m k + 1) * ((m + 1) * (k + 1) * 2 + 37)) := by
  let s := observations f m ∪ observations g k
  have hlen (i : ℕ) : Synthesis interpretation s
      {fun x => decide (min (f x).length (g x).length = i)} ((m + 1) * (k + 1) * 2 + 1) := by
    have h := Synthesis.of_indicators
      (f := fun x => ((⟨(f x).length, by have := hf x; lia⟩ : Fin (m + 1)),
        (⟨(g x).length, by have := hg x; lia⟩ : Fin (k + 1))))
      (fun p => decide (min p.1.val p.2.val = i)) fun p => by
        refine (((synthesis_length (f := f) p.1).mono_sources Set.subset_union_left).and
          ((synthesis_length (f := g) p.2).mono_sources Set.subset_union_right)).congr fun x => ?_
        simp [Prod.ext_iff, Fin.ext_iff]
    simpa [Fintype.card_prod, Fintype.card_fin] using h
  have hsym (i : ℕ) (b : Option Bool) : Synthesis interpretation s
      {fun x => decide ((List.zipWith op (f x) (g x))[i]? = b)} 37 := by
    have h := Synthesis.of_indicators (f := fun x => ((f x)[i]?, (g x)[i]?))
      (fun p => decide ((match p.1, p.2 with
        | some a, some b' => some (op a b')
        | _, _ => none) = b)) fun p => by
        refine (((synthesis_getElem hf i p.1).mono_sources Set.subset_union_left).and
          ((synthesis_getElem hg i p.2).mono_sources Set.subset_union_right)).congr fun x => ?_
        simp [Prod.ext_iff]
    refine (h.congr fun x => ?_).mono_cost (by simp)
    rw [List.getElem?_zipWith]
    cases (f x)[i]? <;> cases (g x)[i]? <;> rfl
  apply synthesis_observations
  · intro i
    simpa only [List.length_zipWith] using (hlen i.val).mono_cost (by lia)
  · intro i b
    exact (hsym i.val b).mono_cost (by lia)

/-- Two words are equal when their optional symbols agree at every index up to the
capacities. -/
theorem synthesis_eq {m k : ℕ} (hf : ∀ x, (f x).length ≤ m) (hg : ∀ x, (g x).length ≤ k) :
    Synthesis interpretation (observations f m ∪ observations g k)
      {fun x => decide (f x = g x)} ((max m k + 1) * 14 + 1) := by
  have hsym (i : ℕ) : Synthesis interpretation (observations f m ∪ observations g k)
      {fun x => decide ((f x)[i]? = (g x)[i]?)} 13 := by
    have h := Synthesis.exists_mem (Finset.univ : Finset (Option Bool))
      (fun b x => decide ((f x)[i]? = b) && decide ((g x)[i]? = b)) (fun _ => 3)
      fun b _ => ((synthesis_getElem hf i b).mono_sources Set.subset_union_left).and
        ((synthesis_getElem hg i b).mono_sources Set.subset_union_right)
    refine (h.congr fun x => ?_).mono_cost (by simp)
    rw [decide_eq_decide]
    simp only [Finset.mem_univ, true_and, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨fun ⟨_, hb, hb'⟩ => hb.trans hb'.symm, fun h => ⟨_, h, rfl⟩⟩
  have h := Synthesis.forall_mem (Finset.range (max m k + 1))
    (fun i x => decide ((f x)[i]? = (g x)[i]?)) (fun _ => 13) fun i _ => hsym i
  refine (h.congr fun x => ?_).mono_cost (by simp)
  rw [decide_eq_decide]
  constructor
  · intro h
    apply List.ext_getElem?
    intro i
    by_cases hi : i < max m k + 1
    · simpa using h i (Finset.mem_range.mpr hi)
    · rw [List.getElem?_eq_none (by have := hf x; lia),
        List.getElem?_eq_none (by have := hg x; lia)]
  · intro h i _
    simp [h]

end Word

/-- A word function fitting a capacity, with its observations synthesized from `s` within a
gate budget. -/
structure WordSynthesis (s : Set (BooleanFunction n)) (f : (Fin n → Bool) → BitString)
    (capacity cost : ℕ) : Prop where
  /-- The word fits the capacity. -/
  length_le : ∀ x, (f x).length ≤ capacity
  /-- Its length and symbol indicators are available within the budget. -/
  synthesis : Synthesis interpretation s (Word.observations f capacity) cost

namespace WordSynthesis

variable {s : Set (BooleanFunction n)} {f g : (Fin n → Bool) → BitString} {m k a b : ℕ}

theorem mono_sources (h : WordSynthesis s f m a) {s' : Set (BooleanFunction n)} (hs : s ⊆ s') :
    WordSynthesis s' f m a :=
  ⟨h.length_le, h.synthesis.mono_sources hs⟩

theorem mono_cost (h : WordSynthesis s f m a) (hab : a ≤ b) : WordSynthesis s f m b :=
  ⟨h.length_le, h.synthesis.mono_cost hab⟩

theorem congr (h : WordSynthesis s f m a) (hfg : ∀ x, f x = g x) : WordSynthesis s g m a :=
  funext hfg ▸ h

/-- Re-derive every indicator at a larger capacity with one gate each. -/
theorem mono_capacity (h : WordSynthesis s f m a) (hmk : m ≤ k) :
    WordSynthesis s f k (a + 4 * (k + 1)) :=
  ⟨fun x => (h.length_le x).trans hmk, by
    simpa only [Nat.mul_one] using h.synthesis.trans ((Word.synthesis_observations
      (fun i => Word.synthesis_length_eq h.length_le i.val)
      (fun i b => Word.synthesis_getElem h.length_le i.val b)).mono_sources
        Set.subset_union_right)⟩

theorem const (value : BitString) :
    WordSynthesis s (fun _ => value) value.length (4 * (value.length + 1)) :=
  ⟨fun _ => le_rfl, Word.synthesis_const value⟩

theorem append (hf : WordSynthesis s f m a) (hg : WordSynthesis s g k b) :
    WordSynthesis s (fun x => f x ++ g x) (m + k)
      (a + b + 4 * (m + k + 1) * (3 * (m + 1) + 1)) :=
  ⟨fun x => by
    simpa only [List.length_append] using Nat.add_le_add (hf.length_le x) (hg.length_le x),
    (hf.synthesis.union hg.synthesis).trans
      ((Word.synthesis_append hf.length_le hg.length_le).mono_sources Set.subset_union_right)⟩

theorem reverse (hf : WordSynthesis s f m a) :
    WordSynthesis s (fun x => (f x).reverse) m (a + 4 * (m + 1) * (3 * (m + 1) + 1)) :=
  ⟨fun x => by simpa only [List.length_reverse] using hf.length_le x,
    hf.synthesis.trans
      ((Word.synthesis_reverse hf.length_le).mono_sources Set.subset_union_right)⟩

theorem map (op : Bool → Bool) (hf : WordSynthesis s f m a) :
    WordSynthesis s (fun x => (f x).map op) m (a + 4 * (m + 1) * 4) :=
  ⟨fun x => by simpa only [List.length_map] using hf.length_le x,
    hf.synthesis.trans ((Word.synthesis_map op).mono_sources Set.subset_union_right)⟩

theorem ite {c : BooleanFunction n} {d : ℕ} (hc : Synthesis interpretation s {c} d)
    (hf : WordSynthesis s f m a) (hg : WordSynthesis s g k b) :
    WordSynthesis s (fun x => if c x then f x else g x) (max m k)
      (d + a + b + 4 * (max m k + 1) * 6) :=
  ⟨fun x => by
    show (if c x then f x else g x).length ≤ max m k
    split
    · exact (hf.length_le x).trans (le_max_left _ _)
    · exact (hg.length_le x).trans (le_max_right _ _),
    ((hc.union hf.synthesis).union hg.synthesis).trans
      ((Word.synthesis_ite hf.length_le hg.length_le).mono_sources Set.subset_union_right)⟩

theorem take (k : ℕ) (hf : WordSynthesis s f m a) :
    WordSynthesis s (fun x => (f x).take k) k (a + 4 * (k + 1) * (m + 2)) :=
  ⟨fun x => by simpa only [List.length_take] using Nat.min_le_left k _,
    hf.synthesis.trans ((Word.synthesis_take hf.length_le k).mono_sources Set.subset_union_right)⟩

theorem drop (k : ℕ) (hf : WordSynthesis s f m a) :
    WordSynthesis s (fun x => (f x).drop k) m (a + 4 * (m + 1) * (m + 2)) :=
  ⟨fun x => by simpa only [List.length_drop] using (Nat.sub_le _ _).trans (hf.length_le x),
    hf.synthesis.trans ((Word.synthesis_drop hf.length_le k).mono_sources Set.subset_union_right)⟩

theorem zipWith (op : Bool → Bool → Bool) (hf : WordSynthesis s f m a)
    (hg : WordSynthesis s g k b) :
    WordSynthesis s (fun x => List.zipWith op (f x) (g x)) (min m k)
      (a + b + 4 * (min m k + 1) * ((m + 1) * (k + 1) * 2 + 37)) :=
  ⟨fun x => by
    simpa only [List.length_zipWith] using min_le_min (hf.length_le x) (hg.length_le x),
    (hf.synthesis.union hg.synthesis).trans
      ((Word.synthesis_zipWith op hf.length_le hg.length_le).mono_sources
        Set.subset_union_right)⟩

/-- Equality of two synthesized words. -/
theorem eq (hf : WordSynthesis s f m a) (hg : WordSynthesis s g k b) :
    Synthesis interpretation s {fun x => decide (f x = g x)} (a + b + ((max m k + 1) * 14 + 1)) :=
  (hf.synthesis.union hg.synthesis).trans
    ((Word.synthesis_eq hf.length_le hg.length_le).mono_sources Set.subset_union_right)

/-- Any predicate of the length of a synthesized word. -/
theorem length_op (hf : WordSynthesis s f m a) (op : ℕ → Bool) :
    Synthesis interpretation s {fun x => op (f x).length} (a + (m + 2)) :=
  hf.synthesis.trans ((Word.synthesis_length_op hf.length_le op).mono_sources
    Set.subset_union_right)

/-- Any optional symbol of a synthesized word. -/
theorem getElem (hf : WordSynthesis s f m a) (i : ℕ) (b : Option Bool) :
    Synthesis interpretation s {fun x => decide ((f x)[i]? = b)} (a + 1) :=
  hf.synthesis.trans ((Word.synthesis_getElem hf.length_le i b).mono_sources
    Set.subset_union_right)

end WordSynthesis
end Cslib.Circuits.Boolean
