/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Cslib.Computability.Circuit.Boolean.WordSynthesis
public import Cslib.Foundations.Data.BitString.Encoding
public import Cslib.Foundations.Data.Polynomial.Growth
import Mathlib.Tactic.Ring

/-!
# Circuits for the length-prefixed encoding

Circuits read and write the frames of `Cslib.Foundations.Data.BitString.Encoding`. Reading a
frame yields the word observations of its decoding: any predicate of the logarithmic-width
header has a quadratic gate bound, and each payload symbol is selected by the header. Writing
packs word observations into a frame. These are the only constructions that depend on the wire
layout; everything else works with observations.
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Encoding

open BitString.Encoding

variable {n capacity : ℕ} {f : (Fin n → Bool) → BitString}

/-- Gates for a predicate of the header of a frame of capacity `n`. -/
def headerCost (n : ℕ) : ℕ := 4 * (n + 1) ^ 2 + 1

/-- Gates for an optional symbol of the word held by a frame of capacity `n`. -/
def symbolCost (n : ℕ) : ℕ := 8 * (n + 1) ^ 2 + 8

/-- Gates for the word observations of a frame of capacity `n`, up to `capacity`. -/
def observationsCost (n capacity : ℕ) : ℕ := 4 * (capacity + 1) * symbolCost n

/-- Gates for packing word observations into a frame of the given capacity. -/
def encodeCost (capacity : ℕ) : ℕ := width capacity * (capacity + 2)

@[fun_prop] theorem polynomiallyBounded_symbolCost {a : ℕ → ℕ} (ha : PolynomiallyBounded a) :
    PolynomiallyBounded fun n => symbolCost (a n) := by
  unfold symbolCost
  fun_prop

@[fun_prop] theorem polynomiallyBounded_observationsCost {a b : ℕ → ℕ}
    (ha : PolynomiallyBounded a) (hb : PolynomiallyBounded b) :
    PolynomiallyBounded fun n => observationsCost (a n) (b n) := by
  unfold observationsCost
  fun_prop

@[fun_prop] theorem polynomiallyBounded_encodeCost {a : ℕ → ℕ} (ha : PolynomiallyBounded a) :
    PolynomiallyBounded fun n => encodeCost (a n) :=
  (show PolynomiallyBounded fun n => 2 * a n * (a n + 2) by fun_prop).mono fun n =>
    Nat.mul_le_mul_right _ (width_le _)

private theorem header_values_le (n : ℕ) : 2 ^ n.size ≤ 2 * (n + 1) := by
  by_cases h : n.size = 0
  · simp only [h, pow_zero]
    lia
  · have hpred : n.size - 1 < n.size := by lia
    have := Nat.lt_size.mp hpred
    have heq : n.size = n.size - 1 + 1 := by lia
    rw [heq, pow_succ]
    lia

/-- Any predicate of the logarithmic-width header has a quadratic gate bound. -/
theorem synthesis_header (n : ℕ) (op : ℕ → Bool) :
    Synthesis interpretation (inputs (width n)) {fun x => op (header x)} (headerCost n) := by
  have h := Synthesis.of_indicators
    (fun bits : Fin n.size → Bool => op (BitVec.ofBoolListLE (List.ofFn bits)).toNat)
    (fun bits => synthesis_minterm (Fin.castAdd n) bits)
  apply h.mono_cost
  simp only [Fintype.card_pi, Fintype.card_bool, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  have hs : n.size ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
  calc
    _ ≤ 2 * (n + 1) * (2 * (n + 1)) + 1 := Nat.add_le_add_right
      (Nat.mul_le_mul (header_values_le n) (by lia : 2 * n.size + 1 + 1 ≤ 2 * (n + 1))) 1
    _ = _ := by unfold headerCost; ring

/-- Read an optional payload symbol, respecting the length header. -/
theorem synthesis_symbol (n i : ℕ) (b : Option Bool) :
    Synthesis interpretation (inputs (width n)) {fun x => decide ((decode x)[i]? = b)}
      (symbolCost n) := by
  have hb : Synthesis interpretation (inputs (width n))
      {fun x => decide ((List.ofFn (data x))[i]? = b)} 1 := by
    by_cases hi : i < n
    · have hx : Synthesis interpretation (inputs (width n))
          {fun x => x ((⟨i, hi⟩ : Fin n).natAdd n.size)} 0 := Synthesis.of_mem ⟨_, rfl⟩
      cases b with
      | none => simpa [List.getElem?_ofFn, hi] using Synthesis.const (n := width n) false
      | some b =>
        cases b
        · simpa [List.getElem?_ofFn, data, hi] using hx.not
        · simpa [List.getElem?_ofFn, data, hi] using
            hx.mono_cost (Nat.zero_le 1)
    · simpa [List.getElem?_ofFn, hi] using Synthesis.const (n := width n) (decide (none = b))
  have h := (synthesis_header n (fun len => decide (i < len))).ite hb
    (Synthesis.const (decide (none = b)))
  refine (h.congr fun x => ?_).mono_cost (by unfold headerCost symbolCost; lia)
  by_cases hi : i < header x <;> simp [decode, hi]

/-- A frame supplies all word observations of its decoding, up to any capacity. -/
theorem synthesis_observations (n capacity : ℕ) :
    Synthesis interpretation (inputs (width n)) (Word.observations decode capacity)
      (observationsCost n capacity) := by
  unfold observationsCost
  apply Word.synthesis_observations
  · intro i
    simpa only [decode, List.length_take, List.length_ofFn] using
      (synthesis_header n (fun len => decide (min len n = i.val))).mono_cost
        (by unfold headerCost symbolCost; lia)
  · exact fun i b => synthesis_symbol n i.val b

/-- The word held by the input frame, at any capacity at least the frame's own. -/
theorem wordSynthesis (n : ℕ) {capacity : ℕ} (h : n ≤ capacity) :
    WordSynthesis (inputs (width n)) decode capacity (observationsCost n capacity) :=
  ⟨fun x => (length_decode_le x).trans h, synthesis_observations n capacity⟩

/-- Pack word observations into a frame: the header from the length indicators and the
payload from the symbol indicators. -/
theorem synthesis_encode (hf : ∀ x, (f x).length ≤ capacity) :
    Synthesis interpretation (Word.observations f capacity)
      (Set.range fun i x => encode capacity (f x) i) (encodeCost capacity) := by
  have hbit (i : Fin capacity) : Synthesis interpretation (Word.observations f capacity)
      {fun x => (f x)[i.val]?.getD false} 0 := by
    refine (Word.synthesis_symbol (f := f) (capacity := capacity) i.castSucc (some true)).congr
      fun x => ?_
    change decide ((f x)[i.val]? = some true) = (f x)[i.val]?.getD false
    cases (f x)[i.val]? with
    | none => rfl
    | some b => cases b <;> rfl
  have h (i : Fin (width capacity)) : Synthesis interpretation (Word.observations f capacity)
      {fun x => encode capacity (f x) i} (capacity + 2) := by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [encode, Fin.append_left, min_eq_left (hf _)] using
        Word.synthesis_length_op hf (fun len => len.testBit j.val)
    · simpa only [encode, Fin.append_right] using
        (hbit j).mono_cost (Nat.zero_le _)
  simpa [encodeCost] using Synthesis.family _ (fun _ => capacity + 2) h

/-- A synthesized word can be packed into a frame. -/
theorem _root_.Cslib.Circuits.Boolean.WordSynthesis.encode {s : Set (BooleanFunction n)}
    {cost : ℕ} (h : WordSynthesis s f capacity cost) :
    Synthesis interpretation s (Set.range fun i x => encode capacity (f x) i)
      (cost + encodeCost capacity) :=
  h.synthesis.trans ((synthesis_encode h.length_le).mono_sources Set.subset_union_right)

/-- Observe the decoded output of an existing circuit family. -/
theorem synthesis_observations_comp {m : ℕ} (F : (Fin n → Bool) → Frame m) :
    Synthesis interpretation (inputs n) (Word.observations (fun x => decode (F x)) m)
      (complexity interpretation F + observationsCost m m) := by
  have h := Synthesis.of_complexity (I := interpretation) (s := inputs n) F (fun i x => x i)
    (fun i => ⟨i, rfl⟩)
  have hobs := synthesis_observations m m
  rw [Word.observations_eq_range] at hobs
  have ho := hobs.substitute (s := inputs n ∪ Set.range (fun j x => F x j)) (fun i x => F x i)
    (fun i => Set.mem_union_right _ ⟨i, rfl⟩)
  apply h.trans
  convert ho using 1
  rw [Word.observations_eq_range]
  congr 1
  funext j
  cases j <;> rfl

/-- The decoded output of an existing circuit family, as a synthesized word. -/
theorem wordSynthesis_comp {m : ℕ} (F : (Fin n → Bool) → Frame m) :
    WordSynthesis (inputs n) (fun x => decode (F x)) m
      (complexity interpretation F + observationsCost m m) :=
  ⟨fun _ => length_decode_le _, synthesis_observations_comp F⟩

end Cslib.Circuits.Boolean.Encoding
