/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/
module

public import Cslib.Init
public import Mathlib.Data.Nat.Count
public import Mathlib.Data.WSeq.Defs

/-!
# Filtering streams into weak sequences

Filtering a stream produces a computable weak sequence, with a waiting step for each omitted
value. These lemmas describe `filterMap` and identify each emitted entry by counting earlier
outputs, without assuming that another output exists.
-/

@[expose] public section

namespace Stream'.WSeq

variable {α β : Type*}

/-- Filtering a weak sequence maps its output steps and preserves its waiting steps. -/
lemma filterMap_eq_map (f : α → Option β) (s : WSeq α) :
    filterMap f s = Seq.map (fun o => o.bind f) s := by
  unfold filterMap
  dsimp only [WSeq] at *
  apply Seq.coinduction2 s
  intro s
  rw [Seq.corec_eq]
  induction s using Seq.recOn with
  | nil => simp only [Seq.destruct_nil, Seq.map_nil, Seq.BisimO, Seq.omap]
  | cons a s =>
    cases a <;> simp only [Seq.destruct_cons, Seq.map_cons, Seq.BisimO, Option.bind]
    all_goals exact ⟨rfl, s, rfl, rfl⟩

/-- Filtering a stream produces one output or waiting step per stream element. -/
lemma filterMap_ofStream (f : α → Option β) (s : Stream' α) :
    filterMap f (ofStream s) = Seq.ofStream (s.map f) := by
  rw [filterMap_eq_map]
  rfl

/-- A waiting step delays every lookup by one computation step. -/
@[simp]
lemma get?_think (s : WSeq α) (n : ℕ) : get? (think s) n = (get? s n).think := by
  rw [get?, dropn_think, head_think]
  rfl

/-- The first entry of a sequence with an output at its head is available immediately. -/
@[simp]
lemma get?_cons_zero (a : α) (s : WSeq α) : get? (cons a s) 0 = Computation.pure (some a) := by
  rw [get?, drop, head_cons]

/-- Looking past an output at the head reduces the lookup index by one. -/
@[simp]
lemma get?_cons_succ (a : α) (s : WSeq α) (n : ℕ) : get? (cons a s) (n + 1) = get? s n := by
  rw [get?, dropn_cons]
  rfl

/-- Expose one computation step of a stream of optional outputs. -/
private lemma ofStream_unfold (f : Stream' (Option α)) :
    (Seq.ofStream f : WSeq α) = match f.head with
      | none => think (Seq.ofStream f.tail)
      | some a => cons a (Seq.ofStream f.tail) := by
  conv_lhs => rw [← Stream'.eta f, Seq.ofStream_cons]
  cases f.head <;> rfl

/-- A lookup either waits, returns the head, or continues with the remaining outputs. -/
private lemma get?_ofStream_eq (f : Stream' (Option α)) (n : ℕ) :
    get? (Seq.ofStream f : WSeq α) n = match f.head with
      | none => (get? (Seq.ofStream f.tail : WSeq α) n).think
      | some a => match n with
        | 0 => Computation.pure (some a)
        | n + 1 => get? (Seq.ofStream f.tail : WSeq α) n := by
  rw [ofStream_unfold]
  cases f.head with
  | none => exact get?_think _ _
  | some a =>
    cases n with
    | zero => exact get?_cons_zero _ _
    | succ n => exact get?_cons_succ _ _ _

/-- A result of looking up an entry comes from the corresponding output of the stream. -/
private lemma get?_ofStream_sound (f : Stream' (Option α)) (n m : ℕ) {o : Option α}
    (h : (get? (Seq.ofStream f : WSeq α) n).val.get m = some o) :
    ∃ t a, f.get t = some a ∧ Nat.count (fun t => (f.get t).isSome) t = n ∧ o = some a := by
  rw [get?_ofStream_eq] at h
  cases hf : f.head with
  | none =>
    simp only [hf] at h
    cases m with
    | zero => cases h
    | succ m =>
      obtain ⟨t, a, ht, hn, rfl⟩ := get?_ofStream_sound f.tail n m h
      refine ⟨t + 1, a, ht, ?_, rfl⟩
      rw [Nat.count_succ']
      change Nat.count (fun t => (f.tail.get t).isSome) t +
        (if f.head.isSome then 1 else 0) = n
      simpa [hf] using hn
  | some a =>
    cases n with
    | zero =>
      simp only [hf] at h
      change some (some a) = some o at h
      have ho : o = some a := (Option.some.inj h).symm
      exact ⟨0, a, hf, Nat.count_zero _, ho⟩
    | succ n =>
      simp only [hf] at h
      obtain ⟨t, b, ht, hn, rfl⟩ := get?_ofStream_sound f.tail n m h
      refine ⟨t + 1, b, ht, ?_, rfl⟩
      rw [Nat.count_succ']
      change Nat.count (fun t => (f.tail.get t).isSome) t +
        (if f.head.isSome then 1 else 0) = n + 1
      simp only [hf, Option.isSome_some, ite_true, hn]
termination_by n + m

/-- Every output of the stream occurs at the index counting its earlier outputs. -/
private lemma get?_ofStream_complete (f : Stream' (Option α)) {t : ℕ} {a : α}
    (h : f.get t = some a) :
    some a ∈ get? (Seq.ofStream f : WSeq α)
      (Nat.count (fun t => (f.get t).isSome) t) := by
  induction t generalizing f with
  | zero =>
    rw [get?_ofStream_eq, Nat.count_zero]
    change some a ∈ (match f.get 0 with
      | none => _
      | some a => Computation.pure (some a))
    rw [h]
    exact Computation.ret_mem _
  | succ t ih =>
    have hc : Nat.count (fun t => (f.get t).isSome) (t + 1) =
        Nat.count (fun t => (f.tail.get t).isSome) t + if f.head.isSome then 1 else 0 :=
      Nat.count_succ' _ t
    rw [hc, get?_ofStream_eq]
    cases hf : f.head with
    | none =>
      simpa only [hf, Option.isSome_none, Bool.false_eq_true, ite_false, Nat.add_zero] using
        Computation.think_mem (ih f.tail h)
    | some b =>
      simpa only [hf, Option.isSome_some, ite_true] using
        ih f.tail h

/-- Looking up a filtered stream skips omitted values and preserves the order of its outputs. -/
lemma mem_get?_filterMap_ofStream {f : α → Option β} {s : Stream' α} {n : ℕ} {o : Option β} :
    o ∈ get? (filterMap f (ofStream s)) n ↔ ∃ t a, f (s.get t) = some a ∧
      Nat.count (fun t => (f (s.get t)).isSome) t = n ∧ o = some a := by
  rw [filterMap_ofStream]
  constructor
  · rintro ⟨m, hm⟩
    exact get?_ofStream_sound (s.map f) n m hm.symm
  · rintro ⟨t, a, ht, rfl, rfl⟩
    exact get?_ofStream_complete (s.map f) ht

end Stream'.WSeq
