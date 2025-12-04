/-
Copyright (c) 2025 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou, Fabrizio Montesi
-/

import Cslib.Foundations.Data.OmegaSequence.Defs
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Data.Nat.Lattice

/-!
# ω-sequences a.k.a. infinite sequences

Most code below is adapted from Mathlib.Data.Stream.Init.
-/

namespace Cslib

open Nat Function Option

namespace ωSequence

universe u v w
variable {α : Type u} {β : Type v} {δ : Type w}
variable (m n : ℕ) (x y : List α) (a b : ωSequence α)

instance [Inhabited α] : Inhabited (ωSequence α) :=
  ⟨ωSequence.const default⟩

@[simp, scoped grind =]
protected theorem eta (s : ωSequence α) : head s ::ω tail s = s := by
  apply DFunLike.ext
  intro i; cases i <;> rfl

/-- Alias for `ωSequence.eta` to match `List` API. -/
alias cons_head_tail := ωSequence.eta

@[ext, grind ext]
protected theorem ext {s₁ s₂ : ωSequence α} : (∀ n, s₁ n = s₂ n) → s₁ = s₂ := by
  apply DFunLike.ext

@[simp, scoped grind =]
theorem get_fun (f : ℕ → α) (n : ℕ) : ωSequence.mk f n = f n :=
  rfl

@[simp, scoped grind =]
theorem get_zero_cons (a : α) (s : ωSequence α) : (a ::ω s) 0 = a :=
  rfl

@[simp, scoped grind =]
theorem head_cons (a : α) (s : ωSequence α) : head (a ::ω s) = a :=
  rfl

@[simp, scoped grind =]
theorem tail_cons (a : α) (s : ωSequence α) : tail (a ::ω s) = s :=
  rfl

@[simp, scoped grind =]
theorem get_drop (n m : ℕ) (s : ωSequence α) : (drop m s) n = s (m + n) := by
  rw [Nat.add_comm]
  rfl

theorem tail_eq_drop (s : ωSequence α) : tail s = drop 1 s :=
  rfl

@[simp, scoped grind =]
theorem drop_drop (n m : ℕ) (s : ωSequence α) : drop n (drop m s) = drop (m + n) s := by
  ext; simp [Nat.add_assoc]

@[simp, scoped grind =]
theorem get_tail {n : ℕ} {s : ωSequence α} : s.tail n = s (n + 1) := rfl

@[simp, scoped grind =]
theorem tail_drop' {i : ℕ} {s : ωSequence α} : tail (drop i s) = s.drop (i + 1) := by
  ext; simp [Nat.add_comm, Nat.add_left_comm]

@[simp, scoped grind =]
theorem drop_tail' {i : ℕ} {s : ωSequence α} : drop i (tail s) = s.drop (i + 1) := rfl

theorem tail_drop (n : ℕ) (s : ωSequence α) : tail (drop n s) = drop n (tail s) := by simp

theorem get_succ (n : ℕ) (s : ωSequence α) : s (succ n) = (tail s) n :=
  rfl

@[simp, scoped grind =]
theorem get_succ_cons (n : ℕ) (s : ωSequence α) (x : α) : (x ::ω s) n.succ = s n :=
  rfl

@[simp, scoped grind =]
lemma get_cons_append_zero {a : α} {x : List α} {s : ωSequence α} :
    (a :: x ++ω s) 0 = a := rfl

@[simp, scoped grind =]
lemma append_eq_cons {a : α} {as : ωSequence α} : [a] ++ω as = a ::ω as := rfl

@[simp, scoped grind =] theorem drop_zero {s : ωSequence α} : s.drop 0 = s := rfl

theorem drop_succ (n : ℕ) (s : ωSequence α) : drop (succ n) s = drop n (tail s) :=
  rfl

theorem head_drop (a : ωSequence α) (n : ℕ) : (a.drop n).head = a n := by simp

theorem cons_injective2 : Function.Injective2 (cons : α → ωSequence α → ωSequence α) :=
fun x y s t h =>
  ⟨by rw [← get_zero_cons x s, h, get_zero_cons],
    ωSequence.ext fun n => by rw [← get_succ_cons n s x, h, get_succ_cons]⟩

theorem cons_injective_left (s : ωSequence α) : Function.Injective fun x => cons x s :=
  cons_injective2.left _

theorem cons_injective_right (x : α) : Function.Injective (cons x) :=
  cons_injective2.right _

section Map

variable (f : α → β)

theorem drop_map (n : ℕ) (s : ωSequence α) : drop n (map f s) = map f (drop n s) :=
  ωSequence.ext fun _ => rfl

@[simp, scoped grind =]
theorem get_map (n : ℕ) (s : ωSequence α) : (map f s) n = f (s n) :=
  rfl

theorem tail_map (s : ωSequence α) : tail (map f s) = map f (tail s) := rfl

@[simp, scoped grind =]
theorem head_map (s : ωSequence α) : head (map f s) = f (head s) :=
  rfl

theorem map_eq (s : ωSequence α) : map f s = f (head s) ::ω map f (tail s) := by
  rw [← ωSequence.eta (map f s), tail_map, head_map]

theorem map_cons (a : α) (s : ωSequence α) : map f (a ::ω s) = f a ::ω map f s := by
  rw [← ωSequence.eta (map f (a ::ω s)), map_eq]; rfl

@[simp, scoped grind =]
theorem map_id (s : ωSequence α) : map id s = s :=
  rfl

@[simp, scoped grind =]
theorem map_map (g : β → δ) (f : α → β) (s : ωSequence α) : map g (map f s) = map (g ∘ f) s :=
  rfl

@[simp, scoped grind =]
theorem map_tail (s : ωSequence α) : map f (tail s) = tail (map f s) :=
  rfl

end Map

section Zip

variable (f : α → β → δ)

theorem drop_zip (n : ℕ) (s₁ : ωSequence α) (s₂ : ωSequence β) :
    drop n (zip f s₁ s₂) = zip f (drop n s₁) (drop n s₂) :=
  ωSequence.ext fun _ => rfl

@[simp, scoped grind =]
theorem get_zip (n : ℕ) (s₁ : ωSequence α) (s₂ : ωSequence β) :
    (zip f s₁ s₂) n = f (s₁ n) (s₂ n) :=
  rfl

theorem head_zip (s₁ : ωSequence α) (s₂ : ωSequence β) :
    head (zip f s₁ s₂) = f (head s₁) (head s₂) :=
  rfl

theorem tail_zip (s₁ : ωSequence α) (s₂ : ωSequence β) :
    tail (zip f s₁ s₂) = zip f (tail s₁) (tail s₂) :=
  rfl

theorem zip_eq (s₁ : ωSequence α) (s₂ : ωSequence β) :
    zip f s₁ s₂ = f (head s₁) (head s₂) ::ω zip f (tail s₁) (tail s₂) := by
  rw [← ωSequence.eta (zip f s₁ s₂)]; rfl

end Zip

theorem const_eq (a : α) : const a = a ::ω const a := by
  apply ωSequence.ext; intro n
  cases n <;> rfl

@[simp, scoped grind =]
theorem tail_const (a : α) : tail (const a) = const a :=
  suffices tail (a ::ω const a) = const a by rwa [← const_eq] at this
  rfl

@[simp, scoped grind =]
theorem map_const (f : α → β) (a : α) : map f (const a) = const (f a) :=
  rfl

@[simp, scoped grind =]
theorem get_const (n : ℕ) (a : α) : (const a) n = a :=
  rfl

@[simp, scoped grind =]
theorem drop_const (n : ℕ) (a : α) : drop n (const a) = const a :=
  ωSequence.ext fun _ => rfl

@[simp, scoped grind =]
theorem head_iterate (f : α → α) (a : α) : head (iterate f a) = a :=
  rfl

theorem get_iterate (f : α → α) (a : α) (n : ℕ) :
    iterate f a n = f^[n] a :=
  rfl

theorem get_succ_iterate' (n : ℕ) (f : α → α) (a : α) :
    iterate f a (succ n) = f (iterate f a n) := by
  rw [get_iterate, succ_eq_add_one, add_comm, Function.iterate_add_apply]
  rfl

theorem tail_iterate (f : α → α) (a : α) : tail (iterate f a) = iterate f (f a) := by
  ext n
  rw [get_tail]
  induction n with
  | zero => rfl
  | succ n ih => rw [get_succ_iterate', ih, get_succ_iterate']

theorem iterate_eq (f : α → α) (a : α) : iterate f a = a ::ω iterate f (f a) := by
  rw [← ωSequence.eta (iterate f a)]
  rw [tail_iterate]; rfl

@[simp, scoped grind =]
theorem get_zero_iterate (f : α → α) (a : α) : (iterate f a) 0 = a :=
  rfl

theorem get_succ_iterate (n : ℕ) (f : α → α) (a : α) :
    iterate f a (succ n) = iterate f (f a) n := by
  rw [get_succ n (iterate f a), tail_iterate]

@[simp, scoped grind =]
theorem iterate_id (a : α) : iterate id a = const a := by
  ext n; simp [get_iterate]

theorem map_iterate (f : α → α) (a : α) : iterate f (f a) = map f (iterate f a) := by
  ext n; rw [get_map, ← get_succ_iterate, get_succ_iterate']

@[simp, scoped grind =]
theorem nil_append_ωSequence (s : ωSequence α) : appendωSequence [] s = s :=
  rfl

theorem cons_append_ωSequence (a : α) (l : List α) (s : ωSequence α) :
    appendωSequence (a :: l) s = a ::ω appendωSequence l s :=
  rfl

@[simp, scoped grind =]
theorem append_append_ωSequence : ∀ (l₁ l₂ : List α) (s : ωSequence α),
    l₁ ++ l₂ ++ω s = l₁ ++ω (l₂ ++ω s)
  | [], _, _ => rfl
  | List.cons a l₁, l₂, s => by
    rw [List.cons_append, cons_append_ωSequence, cons_append_ωSequence, append_append_ωSequence l₁]

lemma get_append_left (h : n < x.length) : (x ++ω a) n = x[n] := by
  induction x generalizing n with
  | nil => simp at h
  | cons b x ih =>
    rcases n with (_ | n)
    · simp
    · simp [ih n (by simpa using h), cons_append_ωSequence]

@[simp, scoped grind =]
lemma get_append_right : (x ++ω a) (x.length + n) = a n := by
  induction x <;> simp [Nat.succ_add, *, cons_append_ωSequence]

theorem get_append_right' {xl : List α} {xs : ωSequence α} {k : ℕ} (h : xl.length ≤ k) :
    (xl ++ω xs) k = xs (k - xl.length) := by
  obtain ⟨n, rfl⟩ := show ∃ n, k = xl.length + n by use (k - xl.length); omega
  simp only [Nat.add_sub_cancel_left]; apply get_append_right

@[simp, scoped grind =]
lemma get_append_length : (x ++ω a) x.length = a 0 := get_append_right 0 x a

lemma append_right_injective (h : x ++ω a = x ++ω b) : a = b := by
  ext n; replace h := congr_arg (fun a ↦ a (x.length + n)) h; simpa using h

@[simp, scoped grind =]
lemma append_right_inj : x ++ω a = x ++ω b ↔ a = b :=
  ⟨append_right_injective x a b, by simp +contextual⟩

lemma append_left_injective (h : x ++ω a = y ++ω b) (hl : x.length = y.length) : x = y := by
  apply List.ext_getElem hl
  intros
  rw [← get_append_left, ← get_append_left, h]

theorem append_left_right_injective (l1 l2 : List α) (s1 s2 : ωSequence α)
    (h1 : l1 ++ω s1 = l2 ++ω s2) (h2 : l1.length = l2.length) : l1 = l2 ∧ s1 = s2 := by
  have h3 := append_left_injective l1 l2 s1 s2 h1 h2
  grind

theorem map_append_ωSequence (f : α → β) :
    ∀ (l : List α) (s : ωSequence α), map f (l ++ω s) = List.map f l ++ω map f s
  | [], _ => rfl
  | List.cons a l, s => by
    rw [cons_append_ωSequence, List.map_cons, map_cons,
      cons_append_ωSequence, map_append_ωSequence f l]

theorem drop_append_ωSequence : ∀ (l : List α) (s : ωSequence α), drop l.length (l ++ω s) = s
  | [], s => rfl
  | List.cons a l, s => by
    rw [List.length_cons, drop_succ, cons_append_ωSequence, tail_cons, drop_append_ωSequence l s]

theorem append_ωSequence_head_tail (s : ωSequence α) : [head s] ++ω tail s = s := by
  simp

@[simp, scoped grind =]
theorem take_zero (s : ωSequence α) : take 0 s = [] :=
  rfl

-- This lemma used to be simp, but we removed it from the simp set because:
-- 1) It duplicates the (often large) `s` term, resulting in large tactic states.
-- 2) It conflicts with the very useful `dropLast_take` lemma below (causing nonconfluence).
theorem take_succ (n : ℕ) (s : ωSequence α) : take (succ n) s = head s :: take n (tail s) :=
  rfl

@[simp, scoped grind =]
theorem take_succ_cons {a : α} (n : ℕ) (s : ωSequence α) :
    take (n+1) (a ::ω s) = a :: take n s := rfl

theorem take_succ' {s : ωSequence α} : ∀ n, s.take (n+1) = s.take n ++ [s n]
  | 0 => rfl
  | n+1 => by rw [take_succ, take_succ' n, ← List.cons_append, ← take_succ, get_tail]

@[simp, scoped grind =]
theorem take_one {xs : ωSequence α} :
    xs.take 1 = [xs 0] := by
  simp [take_succ]

@[simp, scoped grind =]
theorem length_take (n : ℕ) (s : ωSequence α) : (take n s).length = n := by
  induction n generalizing s <;> simp [*, take_succ]

@[simp, scoped grind =]
theorem take_take {s : ωSequence α} : ∀ {m n}, (s.take n).take m = s.take (min n m)
  | 0, n => by rw [Nat.min_zero, List.take_zero, take_zero]
  | m, 0 => by rw [Nat.zero_min, take_zero, List.take_nil]
  | m+1, n+1 => by rw [take_succ, List.take_succ_cons, Nat.succ_min_succ, take_succ, take_take]

@[simp, scoped grind =]
theorem concat_take_get {n : ℕ} {s : ωSequence α} : s.take n ++ [s n] = s.take (n + 1) :=
  (take_succ' n).symm

theorem getElem?_take {s : ωSequence α} : ∀ {k n}, k < n → (s.take n)[k]? = s k
  | 0, _+1, _ => by simp only [length_take, zero_lt_succ, List.getElem?_eq_getElem]; rfl
  | k+1, n+1, h => by
    rw [take_succ, List.getElem?_cons_succ, getElem?_take (Nat.lt_of_succ_lt_succ h), get_succ k s]

theorem getElem?_take_succ (n : ℕ) (s : ωSequence α) :
    (take (succ n) s)[n]? = some (s n) :=
  getElem?_take (Nat.lt_succ_self n)

@[simp, scoped grind =]
theorem dropLast_take {n : ℕ} {xs : ωSequence α} :
    (ωSequence.take n xs).dropLast = ωSequence.take (n-1) xs := by
  cases n with
  | zero => simp
  | succ n => rw [take_succ', List.dropLast_concat, Nat.add_one_sub_one]

@[simp, scoped grind =]
theorem append_take_drop (n : ℕ) (s : ωSequence α) : appendωSequence (take n s) (drop n s) = s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>rw [take_succ, drop_succ, cons_append_ωSequence, ih (tail s), ωSequence.eta]

lemma append_take : x ++ (a.take n) = (x ++ω a).take (x.length + n) := by
  induction x <;> simp [take, Nat.add_comm, cons_append_ωSequence, *]

@[simp, scoped grind =]
lemma take_get (h : m < (a.take n).length) : (a.take n)[m] = a m := by
  nth_rw 2 [← append_take_drop n a]; rw [get_append_left]

theorem take_append_of_le_length (h : n ≤ x.length) :
    (x ++ω a).take n = x.take n := by
  apply List.ext_getElem (by simp [h])
  intro _ _ _; rw [List.getElem_take, take_get, get_append_left]

lemma take_add : a.take (m + n) = a.take m ++ (a.drop m).take n := by
  apply append_left_injective _ _ (a.drop (m + n)) ((a.drop m).drop n) <;>
    simp [- drop_drop]

@[gcongr] lemma take_prefix_take_left (h : m ≤ n) : a.take m <+: a.take n := by
  rw [(by simp [h] : a.take m = (a.take n).take m)]
  apply List.take_prefix

@[simp, scoped grind =]
lemma take_prefix : a.take m <+: a.take n ↔ m ≤ n :=
  ⟨fun h ↦ by simpa using h.length_le, take_prefix_take_left m n a⟩

lemma map_take (f : α → β) : (a.take n).map f = (a.map f).take n := by
  apply List.ext_getElem <;> simp

lemma take_drop : (a.drop m).take n = (a.take (m + n)).drop m := by
  apply List.ext_getElem <;> simp

lemma drop_append_of_le_length (h : n ≤ x.length) :
    (x ++ω a).drop n = x.drop n ++ω a := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le h
  ext k; rcases lt_or_ge k m with _ | hk
  · rw [get_drop, get_append_left, get_append_left, List.getElem_drop]; simpa [hm]
  · obtain ⟨p, rfl⟩ := Nat.exists_eq_add_of_le hk
    have hm' : m = (x.drop n).length := by simp [hm]
    simp_rw [get_drop, ← Nat.add_assoc, ← hm, get_append_right, hm', get_append_right]

theorem drop_append_of_ge_length {xl : List α} {xs : ωSequence α} {n : ℕ} (h : xl.length ≤ n) :
    (xl ++ω xs).drop n = xs.drop (n - xl.length) := by
  ext k; simp (disch := omega) only [get_drop, get_append_right']
  congr; omega

-- Take theorem reduces a proof of equality of infinite ω-sequences to an
-- induction over all their finite approximations.
theorem take_theorem (s₁ s₂ : ωSequence α) (h : ∀ n : ℕ, take n s₁ = take n s₂) : s₁ = s₂ := by
  ext n
  induction n with
  | zero => simpa [take] using h 1
  | succ n =>
    have h₁ : some (s₁ (succ n)) = some (s₂ (succ n)) := by
      rw [← getElem?_take_succ, ← getElem?_take_succ, h (succ (succ n))]
    injection h₁

theorem extract_eq_drop_take {xs : ωSequence α} {m n : ℕ} :
    xs.extract m n = take (n - m) (xs.drop m) := by
  rfl

theorem extract_eq_ofFn {xs : ωSequence α} {m n : ℕ} :
    xs.extract m n = List.ofFn (fun k : Fin (n - m) ↦ xs (m + k)) := by
  ext k; cases Decidable.em (k < n - m) <;>
  grind [extract_eq_drop_take, getElem?_take]

theorem extract_eq_extract {xs xs' : ωSequence α} {m n m' n' : ℕ}
    (h : xs.extract m n = xs'.extract m' n') :
    n - m = n' - m' ∧ ∀ k < n - m, xs (m + k) = xs' (m' + k) := by
  simp only [extract_eq_ofFn, List.ofFn_inj', Sigma.mk.injEq] at h
  obtain ⟨h_eq, h_fun⟩ := h
  rw [← h_eq] at h_fun
  simp_all [funext_iff, Fin.forall_iff]

theorem extract_eq_take {xs : ωSequence α} {n : ℕ} :
    xs.extract 0 n = xs.take n := by
  simp [extract_eq_drop_take]

@[simp, scoped grind =]
theorem append_extract_drop {xs : ωSequence α} {n : ℕ} :
    (xs.extract 0 n) ++ω (xs.drop n) = xs := by
  simp [extract_eq_take, append_take_drop]

theorem extract_apppend_right_right {xl : List α} {xs : ωSequence α} {m n : ℕ} (h : xl.length ≤ m) :
    (xl ++ω xs).extract m n = xs.extract (m - xl.length) (n - xl.length) := by
  grind [extract_eq_drop_take, drop_append_of_ge_length]

theorem extract_append_zero_right {xl : List α} {xs : ωSequence α} {n : ℕ} (h : xl.length ≤ n) :
    (xl ++ω xs).extract 0 n = xl ++ (xs.extract 0 (n - xl.length)) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = xl.length + k := ⟨n - xl.length, by omega⟩
  simp [extract_eq_take, ← append_take]

theorem extract_drop {xs : ωSequence α} {k m n : ℕ} :
    (xs.drop k).extract m n = xs.extract (k + m) (k + n) := by
  grind [extract_eq_drop_take]

@[simp, scoped grind =]
theorem length_extract {xs : ωSequence α} {m n : ℕ} :
    (xs.extract m n).length = n - m := by
  simp [extract_eq_drop_take]

@[simp, scoped grind =]
theorem extract_eq_nil {xs : ωSequence α} {n : ℕ} :
    xs.extract n n = [] := by
  simp [extract_eq_drop_take]

@[simp, scoped grind =]
theorem extract_eq_nil_iff {xs : ωSequence α} {m n : ℕ} :
    xs.extract m n = [] ↔ m ≥ n := by
  rw [← List.length_eq_zero_iff]
  grind [extract_eq_drop_take]

@[simp, scoped grind =]
theorem get_extract {xs : ωSequence α} {m n k : ℕ} (h : k < n - m) :
    (xs.extract m n)[k]'(by simp [h]) = xs (m + k) := by
  simp [extract_eq_drop_take]

theorem append_extract_extract {xs : ωSequence α} {k m n : ℕ} (h_km : k ≤ m) (h_mn : m ≤ n) :
    (xs.extract k m) ++ (xs.extract m n) = xs.extract k n := by
  have : n - k = (m - k) + (n - m) := by grind
  grind [extract_eq_drop_take, take_add]

theorem extract_succ_right {xs : ωSequence α} {m n : ℕ} (h_mn : m ≤ n) :
    xs.extract m (n + 1) = xs.extract m n ++ [xs n] := by
  rw [← append_extract_extract h_mn] <;>
  grind [extract_eq_drop_take, add_tsub_cancel_left]

@[simp, scoped grind =]
theorem extract_lu_extract_lu {xs : ωSequence α} {m n i j : ℕ} (h : j ≤ n - m) :
    (xs.extract m n).extract i j = xs.extract (m + i) (m + j) := by
  ext k
  cases Decidable.em (k < j - i) <;> grind [extract_eq_ofFn]

@[scoped grind =]
theorem extract_0u_extract_lu {xs : ωSequence α} {n i j : ℕ} (h : j ≤ n) :
    (xs.extract 0 n).extract i j = xs.extract i j := by
  grind

@[scoped grind =]
theorem extract_0u_extract_l {xs : ωSequence α} {n i : ℕ} :
    (xs.extract 0 n).extract i = xs.extract i n := by
  grind

end ωSequence

end Cslib
