/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Cslib.Computability.Circuit.Boolean.FPPoly

/-!
# P/poly

`PPoly f` says that the Boolean function `f` on finite bit strings is computed by nonuniform
De Morgan circuits of polynomial size. It bounds the existing circuit complexity of each
fixed-length restriction using `PolynomiallyBounded`. There is no computability requirement
on the choice of circuits at different lengths.

A circuit on frames serves every input length up to its capacity: `complexity_decode_le`
decodes the frame once and selects, by the decoded length, among the circuits for each exact
length. This relates `PPoly` to the frame-based `FPPoly`, so predicates inherit the word
closure rules, and a P/poly bit can in turn be assembled into an FP/poly output word.

Closure rules are registered with `fun_prop` so clients can reason about ordinary Lean
functions without constructing circuits or choosing polynomial bounds.

## References

* [Sanjeev Arora and Boaz Barak, *Computational Complexity: A Modern Approach*,
  Section 6.1][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

open BitString.Encoding

/-- A predicate is in P/poly when its fixed-length circuit complexity grows polynomially. -/
@[fun_prop] def PPoly (f : BitString → Bool) : Prop :=
  PolynomiallyBounded fun n =>
    complexity interpretation (single fun x : Fin n → Bool => f (List.ofFn x))

/-- Frames give the same class as ordinary fixed-length inputs. -/
theorem pPoly_iff_encoded {f : BitString → Bool} :
    PPoly f ↔ PolynomiallyBounded (fun n => complexity interpretation
      (single fun x : Frame n => f (decode x))) := by
  constructor
  · intro hf
    obtain ⟨p, hp, hpb, hfp⟩ := hf.exists_monotone
    have hb : PolynomiallyBounded (fun n =>
        Encoding.observationsCost n n + (n + 1) * (p n + 2) + 1) := by fun_prop
    exact hb.mono fun n => Encoding.complexity_decode_le f n (p n)
      (fun m hm => (hfp m).trans (hp hm))
  · intro hf
    apply (PolynomiallyBounded.id.mul (PolynomiallyBounded.const 2) |>.add hf).mono
    intro n
    exact (Encoding.complexity_ofFn_le f n).trans
      (Nat.add_le_add_right (by simpa [Nat.mul_comm] using width_le n) _)

/-- A predicate synthesized on every frame within a polynomial budget is in P/poly. -/
theorem PPoly.of_synthesis {f : BitString → Bool} {cost : ℕ → ℕ} (hc : PolynomiallyBounded cost)
    (h : ∀ n, Synthesis interpretation (inputs (width n)) {fun x : Frame n => f (decode x)}
      (cost n)) : PPoly f :=
  pPoly_iff_encoded.mpr (hc.mono fun n => (h n).complexity_le)

/-- A predicate is in P/poly exactly when its singleton-valued version is in FP/poly. -/
theorem pPoly_iff_fpPoly {f : BitString → Bool} : PPoly f ↔ FPPoly (fun x => [f x]) := by
  rw [pPoly_iff_encoded]
  constructor
  · intro hf
    refine ⟨fun n => complexity interpretation
      (single fun x : Frame n => f (decode x)) + 3,
      hf.add (PolynomiallyBounded.const 3), fun n =>
        ⟨1, fun x => encode 1 [f (decode x)], fun x => decode_encode_of_length_le le_rfl, ?_⟩⟩
    have h := complexity_comp_le (I := interpretation)
      (single fun x : Frame n => f (decode x))
      (fun x : Fin 1 → Bool => encode 1 (List.ofFn x))
    have hb := Encoding.complexity_encode_ofFn_le 1 1
    simp only [width, Nat.size_one] at hb
    have heq : (fun x : Fin 1 → Bool => encode 1 (List.ofFn x)) ∘
        (single fun x : Frame n => f (decode x)) =
        fun x => encode 1 [f (decode x)] := by
      funext x
      simp [Function.comp_apply, List.ofFn_succ, single_apply]
    rw [heq] at h
    calc
      _ ≤ 1 + (complexity interpretation
          (single fun x : Frame n => f (decode x)) + 2) :=
        Nat.add_le_add_left (h.trans (Nat.add_le_add_left hb _)) 1
      _ = _ := by lia
  · intro hf
    rw [fpPoly_iff_observations] at hf
    obtain ⟨capacity, cost, _, hs, h⟩ := hf
    apply (hs.add (PolynomiallyBounded.const 1)).mono
    intro n
    simpa using ((h n).getElem 0 (some true)).complexity_le

namespace PPoly

variable {f g : BitString → Bool}

/-- Constant functions have constant-size circuits, including on the empty input. -/
@[fun_prop] theorem const (b : Bool) : PPoly (fun _ => b) :=
  (PolynomiallyBounded.const 1).mono fun _ => (Synthesis.const b).complexity_le

/-- Any fixed Boolean binary operation preserves polynomial circuit size. This is not a
`fun_prop` rule: an arbitrary `op` applied to two arguments does not unify with a concrete
expression, so the rules below instantiate it for each operation. -/
theorem comp₂ (hf : PPoly f) (hg : PPoly g) (op : Bool → Bool → Bool) :
    PPoly (fun x => op (f x) (g x)) := by
  let h := single (fun x : Fin 2 → Bool => op (x 0) (x 1))
  apply ((hf.add hg).add (PolynomiallyBounded.const (complexity interpretation h))).mono
  intro n
  let F := single (fun x : Fin n → Bool => f (List.ofFn x))
  let G := single (fun x : Fin n → Bool => g (List.ofFn x))
  have hcomp := complexity_comp_le (I := interpretation) (fun x => Fin.append (F x) (G x)) h
  exact hcomp.trans (Nat.add_le_add_right (complexity_append_le F G) _)

/-- Postcomposing with any fixed Boolean function preserves P/poly. -/
@[fun_prop] theorem comp (hf : PPoly f) (op : Bool → Bool) :
    PPoly (fun x => op (f x)) :=
  hf.comp₂ hf (fun a _ => op a)

/-- P/poly is closed under intersection. -/
@[fun_prop] theorem and (hf : PPoly f) (hg : PPoly g) :
    PPoly (fun x => f x && g x) := hf.comp₂ hg Bool.and

/-- P/poly is closed under union. -/
@[fun_prop] theorem or (hf : PPoly f) (hg : PPoly g) :
    PPoly (fun x => f x || g x) := hf.comp₂ hg Bool.or

/-- P/poly is closed under symmetric difference. -/
@[fun_prop] theorem xor (hf : PPoly f) (hg : PPoly g) :
    PPoly (fun x => f x ^^ g x) := hf.comp₂ hg Bool.xor

/-- P/poly is closed under Boolean equality. -/
@[fun_prop] theorem beq (hf : PPoly f) (hg : PPoly g) :
    PPoly (fun x => f x == g x) := hf.comp₂ hg (· == ·)

/-- A Boolean recognizer can follow any FP/poly transformation. -/
@[fun_prop] theorem comp_fpPoly (hf : PPoly f) {g : BitString → BitString} (hg : FPPoly g) :
    PPoly (fun x => f (g x)) :=
  pPoly_iff_fpPoly.mpr ((pPoly_iff_fpPoly.mp hf).comp hg)

/-- Boolean conditionals preserve P/poly. -/
@[fun_prop] theorem ite {h : BitString → Bool} (hf : PPoly f) (hg : PPoly g) (hh : PPoly h) :
    PPoly (fun x => if f x then g x else h x) := by
  convert (hf.and hg).or ((hf.comp Bool.not).and hh) using 1
  ext x
  cases f x <;> simp

/-- Reading a bit, with a default for out-of-range indices, costs at most one gate. -/
@[fun_prop] theorem getElem (i : ℕ) (fallback : Bool) :
    PPoly (fun x => x[i]?.getD fallback) := by
  apply (PolynomiallyBounded.const 1).mono
  intro n
  by_cases hi : i < n
  · have h : Synthesis interpretation (inputs n) {fun x => x ⟨i, hi⟩} 0 :=
      Synthesis.of_mem ⟨⟨i, hi⟩, rfl⟩
    simpa [List.getElem?_ofFn, hi] using h.complexity_le.trans (Nat.zero_le 1)
  · simpa [List.getElem?_ofFn, hi] using
      (Synthesis.const (n := n) fallback).complexity_le

/-- Testing every bit against a fixed predicate is in P/poly. -/
@[fun_prop] theorem all (op : Bool → Bool) : PPoly (fun x => x.all op) := by
  have hall : PPoly (fun x => x.all _root_.id) := by
    apply (PolynomiallyBounded.id.add (PolynomiallyBounded.const 1)).mono
    intro n
    have h := Synthesis.forall_mem (s := inputs n) Finset.univ
      (fun i (x : Fin n → Bool) => x i) (fun _ => 0)
      (fun i _ => Synthesis.of_mem ⟨i, rfl⟩)
    convert h.complexity_le using 2
    · congr 1
      ext x
      exact Bool.eq_iff_iff.mpr (by simp)
    · simp
  simpa using hall.comp_fpPoly (FPPoly.map op)

/-- Testing whether some bit satisfies a fixed predicate is in P/poly. -/
@[fun_prop] theorem any (op : Bool → Bool) : PPoly (fun x => x.any op) := by
  simpa [← List.any_eq_not_all_not] using (all (fun b => !op b)).comp Bool.not

end PPoly

/-- A P/poly bit can be used as an FP/poly output word. -/
@[fun_prop] theorem PPoly.singleton {f : BitString → Bool} (hf : PPoly f) :
    FPPoly (fun x => [f x]) := pPoly_iff_fpPoly.mp hf

/-- Prepend a P/poly bit to an FP/poly output word. -/
@[fun_prop] theorem PPoly.cons {f : BitString → Bool} {g : BitString → BitString}
    (hf : PPoly f) (hg : FPPoly g) : FPPoly (fun x => f x :: g x) :=
  hf.singleton.append hg

namespace FPPoly

variable {f g : BitString → BitString}

/-- Reading an output bit of an FP/poly function is in P/poly. -/
@[fun_prop] theorem getElem (hf : FPPoly f) (i : ℕ) (fallback : Bool) :
    PPoly (fun x => (f x)[i]?.getD fallback) :=
  (PPoly.getElem i fallback).comp_fpPoly hf

/-- A P/poly condition selects between two FP/poly words. -/
@[fun_prop] theorem ite {c : BitString → Bool} (hc : PPoly c) (hf : FPPoly f) (hg : FPPoly g) :
    FPPoly (fun x => if c x then f x else g x) := by
  rw [pPoly_iff_encoded] at hc
  rw [fpPoly_iff_observations] at *
  obtain ⟨m, a, hm, ha, hf⟩ := hf
  obtain ⟨k, b, hk, hb, hg⟩ := hg
  exact ⟨_, _, by fun_prop, by fun_prop, fun n =>
    WordSynthesis.ite (Synthesis.of_complexity_single _) (hf n) (hg n)⟩

/-- Testing the output length against a fixed value is in P/poly. -/
@[fun_prop] theorem length_eq (hf : FPPoly f) (k : ℕ) :
    PPoly (fun x => decide ((f x).length = k)) := by
  rw [fpPoly_iff_observations] at hf
  obtain ⟨m, a, hm, ha, hf⟩ := hf
  exact PPoly.of_synthesis (by fun_prop) fun n => (hf n).length_op fun len => decide (len = k)

/-- Bounding the output length by a fixed value is in P/poly. -/
@[fun_prop] theorem length_le (hf : FPPoly f) (k : ℕ) :
    PPoly (fun x => decide ((f x).length ≤ k)) := by
  rw [fpPoly_iff_observations] at hf
  obtain ⟨m, a, hm, ha, hf⟩ := hf
  exact PPoly.of_synthesis (by fun_prop) fun n => (hf n).length_op fun len => decide (len ≤ k)

/-- Equality of two FP/poly words is in P/poly. -/
@[fun_prop] theorem eq (hf : FPPoly f) (hg : FPPoly g) : PPoly (fun x => decide (f x = g x)) := by
  rw [fpPoly_iff_observations] at hf hg
  obtain ⟨m, a, hm, ha, hf⟩ := hf
  obtain ⟨k, b, hk, hb, hg⟩ := hg
  exact PPoly.of_synthesis (by fun_prop) fun n => (hf n).eq (hg n)

/-- Boolean equality of two FP/poly words is in P/poly. -/
@[fun_prop] theorem beq (hf : FPPoly f) (hg : FPPoly g) : PPoly (fun x => f x == g x) := by
  simpa only [Bool.beq_eq_decide_eq] using hf.eq hg

end FPPoly
end Cslib.Circuits.Boolean
