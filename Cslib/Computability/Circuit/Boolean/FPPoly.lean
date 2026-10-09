/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Cslib.Computability.Circuit.Boolean.Encoding

/-!
# Polynomial-size circuit functions

`FPPoly f` means that nonuniform De Morgan circuits compute the ordinary word function `f`,
with polynomially bounded output capacity and gate count. A circuit of input capacity `n`
receives a frame holding a word of length at most `n`, as specified by `BitString.Encoding`,
and must produce `f` of that word for every frame: frames whose header exceeds the capacity
or whose unused payload is nonzero included. Correctness on every frame is what lets circuits
compose by plain substitution, since the output frame of one circuit need not be a canonical
encoding to serve as the input of the next. Output capacity is counted in the bound because
output wires are free.

The closure rules are registered with `fun_prop`. Clients work with `List Bool` functions;
they do not need to construct encodings, circuits, or polynomial witnesses. The rules are
proved through `fpPoly_iff_observations`, which exchanges the circuits for word observations
synthesized at every capacity, so each word operation is a closure rule of `WordSynthesis`.

## References

* [Sanjeev Arora and Boaz Barak, *Computational Complexity: A Modern Approach*,
  Section 6.1][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

open BitString.Encoding

/-- Word functions computed by circuits with polynomially bounded capacity and gate count. -/
@[fun_prop] def FPPoly (f : BitString → BitString) : Prop :=
  ∃ bound : ℕ → ℕ, PolynomiallyBounded bound ∧ ∀ n,
    ∃ m, ∃ F : Frame n → Frame m,
      (∀ x, decode (F x) = f (decode x)) ∧ m + complexity interpretation F ≤ bound n

/-- Circuits at every capacity are the same as word observations synthesized at every
capacity, with polynomially bounded capacity and cost. -/
theorem fpPoly_iff_observations {f : BitString → BitString} :
    FPPoly f ↔ ∃ capacity cost : ℕ → ℕ, PolynomiallyBounded capacity ∧
      PolynomiallyBounded cost ∧ ∀ n, WordSynthesis (inputs (width n))
        (fun x : Frame n => f (decode x)) (capacity n) (cost n) := by
  constructor
  · rintro ⟨bound, hb, h⟩
    choose capacity F hF hsize using h
    have hc : PolynomiallyBounded capacity := hb.mono fun n => by have := hsize n; lia
    refine ⟨capacity, fun n => bound n + Encoding.observationsCost (capacity n) (capacity n),
      hc, by fun_prop, fun n => ?_⟩
    refine ((Encoding.wordSynthesis_comp (F n)).congr (hF n)).mono_cost ?_
    have := hsize n
    lia
  · rintro ⟨capacity, cost, hc, hcost, h⟩
    refine ⟨fun n => capacity n + (cost n + Encoding.encodeCost (capacity n)), by fun_prop,
      fun n => ⟨capacity n, fun x => encode (capacity n) (f (decode x)),
        fun x => decode_encode_of_length_le ((h n).length_le x), ?_⟩⟩
    exact Nat.add_le_add_left (complexity_le_iff.mpr (h n).encode.exists_circuit_outputs) _

namespace FPPoly

variable {f g : BitString → BitString}

/-- Observable output lengths have a polynomial bound, even though output wiring is free. -/
theorem exists_length_le (hf : FPPoly f) :
    ∃ bound : ℕ → ℕ, PolynomiallyBounded bound ∧ ∀ x, (f x).length ≤ bound x.length := by
  obtain ⟨bound, hb, h⟩ := hf
  refine ⟨bound, hb, fun x => ?_⟩
  obtain ⟨m, F, hF, hs⟩ := h x.length
  have hl := length_decode_le (F (encode x.length x))
  rw [hF, decode_encode_of_length_le le_rfl] at hl
  lia

/-- Constant output words have constant size. -/
@[fun_prop] theorem const (value : BitString) : FPPoly (fun _ => value) :=
  fpPoly_iff_observations.mpr
    ⟨_, _, by fun_prop, by fun_prop, fun _ => WordSynthesis.const value⟩

/-- Identity is free wiring with linear output capacity. -/
@[fun_prop] theorem id : FPPoly (fun x => x) :=
  ⟨fun n => n, by fun_prop, fun n => ⟨n, fun x => x ∘ _root_.id, fun _ => rfl,
    by rw [complexity_wiring, add_zero]⟩⟩

/-- Circuit substitution preserves polynomial growth because output capacity is bounded. -/
@[fun_prop] theorem comp (hf : FPPoly f) (hg : FPPoly g) : FPPoly (fun x => f (g x)) := by
  obtain ⟨bound, hb, hg⟩ := hg
  obtain ⟨boundf, hbf, hf⟩ := hf
  obtain ⟨p, hp, hpb, hfp⟩ := hbf.exists_monotone
  refine ⟨fun n => bound n + p (bound n), by fun_prop, fun n => ?_⟩
  obtain ⟨m, G, hG, hsG⟩ := hg n
  obtain ⟨k, F, hF, hsF⟩ := hf m
  refine ⟨k, F ∘ G, fun x => by rw [Function.comp_apply, hF, hG], ?_⟩
  have := complexity_comp_le (I := interpretation) G F
  have := hfp m
  have := hp (show m ≤ bound n by lia)
  lia

/-- Concatenation packs the two words using their observations. -/
@[fun_prop] theorem append (hf : FPPoly f) (hg : FPPoly g) :
    FPPoly (fun x => f x ++ g x) := by
  rw [fpPoly_iff_observations] at *
  obtain ⟨m, a, hm, ha, hf⟩ := hf
  obtain ⟨k, b, hk, hb, hg⟩ := hg
  exact ⟨_, _, by fun_prop, by fun_prop, fun n => (hf n).append (hg n)⟩

/-- Reversal uses the word's actual length to reverse its payload. -/
@[fun_prop] theorem reverse : FPPoly List.reverse :=
  fpPoly_iff_observations.mpr
    ⟨_, _, by fun_prop, by fun_prop, fun n => (Encoding.wordSynthesis n le_rfl).reverse⟩

/-- Applying a fixed Boolean function to every bit preserves polynomial circuit size. -/
@[fun_prop] theorem map (op : Bool → Bool) : FPPoly (List.map op) :=
  fpPoly_iff_observations.mpr
    ⟨_, _, by fun_prop, by fun_prop, fun n => (Encoding.wordSynthesis n le_rfl).map op⟩

/-- A prefix of fixed length. -/
@[fun_prop] theorem take (k : ℕ) : FPPoly (List.take k) :=
  fpPoly_iff_observations.mpr
    ⟨_, _, by fun_prop, by fun_prop, fun n => (Encoding.wordSynthesis n le_rfl).take k⟩

/-- Dropping a prefix of fixed length. -/
@[fun_prop] theorem drop (k : ℕ) : FPPoly (List.drop k) :=
  fpPoly_iff_observations.mpr
    ⟨_, _, by fun_prop, by fun_prop, fun n => (Encoding.wordSynthesis n le_rfl).drop k⟩

/-- A fixed bitwise binary operation on two words. -/
@[fun_prop] theorem zipWith (op : Bool → Bool → Bool) (hf : FPPoly f) (hg : FPPoly g) :
    FPPoly (fun x => List.zipWith op (f x) (g x)) := by
  rw [fpPoly_iff_observations] at *
  obtain ⟨m, a, hm, ha, hf⟩ := hf
  obtain ⟨k, b, hk, hb, hg⟩ := hg
  exact ⟨_, _, by fun_prop, by fun_prop, fun n => (hf n).zipWith op (hg n)⟩

end FPPoly
end Cslib.Circuits.Boolean
