/-
Copyright (c) 2025-present Ching-Tsun Chou All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/
import Cslib.Foundations.Data.OmegaSequence.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-!
# ω-sequences a.k.a. infinite sequences

Most code below is adapted from Mathlib.Data.Stream.Init.
-/

open Nat Function Option

namespace ωSequence

universe u v w
variable {α : Type u} {β : Type v} {δ : Type w}
variable (m n : ℕ) (x y : List α) (a b : ωSequence α)

instance [Inhabited α] : Inhabited (ωSequence α) :=
  ⟨ωSequence.const default⟩

@[simp] protected theorem eta (s : ωSequence α) : head s :: tail s = s :=
  funext fun i => by cases i <;> rfl

/-- Alias for `ωSequence.eta` to match `List` API. -/
alias cons_head_tail := ωSequence.eta

@[ext]
protected theorem ext {s₁ s₂ : ωSequence α} : (∀ n, s₁ n = s₂ n) → s₁ = s₂ :=
  fun h => funext h

@[simp]
theorem get_zero_cons (a : α) (s : ωSequence α) : (a::s) 0 = a :=
  rfl

@[simp]
theorem head_cons (a : α) (s : ωSequence α) : head (a::s) = a :=
  rfl

@[simp]
theorem tail_cons (a : α) (s : ωSequence α) : tail (a::s) = s :=
  rfl

@[simp]
theorem get_drop (n m : ℕ) (s : ωSequence α) : (drop m s) n = s (m + n) := by
  rw [Nat.add_comm]
  rfl

theorem tail_eq_drop (s : ωSequence α) : tail s = drop 1 s :=
  rfl

@[simp]
theorem drop_drop (n m : ℕ) (s : ωSequence α) : drop n (drop m s) = drop (m + n) s := by
  ext; simp [Nat.add_assoc]

@[simp] theorem get_tail {n : ℕ} {s : ωSequence α} : s.tail n = s (n + 1) := rfl

@[simp] theorem tail_drop' {i : ℕ} {s : ωSequence α} : tail (drop i s) = s.drop (i + 1) := by
  ext; simp [Nat.add_comm, Nat.add_left_comm]

@[simp] theorem drop_tail' {i : ℕ} {s : ωSequence α} : drop i (tail s) = s.drop (i + 1) := rfl

theorem tail_drop (n : ℕ) (s : ωSequence α) : tail (drop n s) = drop n (tail s) := by simp

theorem get_succ (n : ℕ) (s : ωSequence α) : s (succ n) = (tail s) n :=
  rfl

@[simp]
theorem get_succ_cons (n : ℕ) (s : ωSequence α) (x : α) : (x :: s) n.succ = s n :=
  rfl

@[simp] lemma get_cons_append_zero {a : α} {x : List α} {s : ωSequence α} :
    (a :: x ++ω s) 0 = a := rfl

@[simp] lemma append_eq_cons {a : α} {as : ωSequence α} : [a] ++ω as = a :: as := rfl

@[simp] theorem drop_zero {s : ωSequence α} : s.drop 0 = s := rfl

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

theorem all_def (p : α → Prop) (s : ωSequence α) : All p s = ∀ n, p (s n) :=
  rfl

theorem any_def (p : α → Prop) (s : ωSequence α) : Any p s = ∃ n, p (s n) :=
  rfl

@[simp]
theorem mem_cons (a : α) (s : ωSequence α) : a ∈ a::s :=
  Exists.intro 0 rfl

theorem mem_cons_of_mem {a : α} {s : ωSequence α} (b : α) : a ∈ s → a ∈ b::s := fun ⟨n, h⟩ =>
  Exists.intro (succ n) (by rw [get_succ n (b :: s), tail_cons, h])

theorem eq_or_mem_of_mem_cons {a b : α} {s : ωSequence α} : (a ∈ b::s) → a = b ∨ a ∈ s :=
    fun ⟨n, h⟩ => by
  rcases n with - | n'
  · left
    exact h
  · right
    rw [get_succ n' (b :: s), tail_cons] at h
    exact ⟨n', h⟩

theorem mem_of_get_eq {n : ℕ} {s : ωSequence α} {a : α} : a = s n → a ∈ s := fun h =>
  Exists.intro n h

theorem mem_iff_exists_get_eq {s : ωSequence α} {a : α} : a ∈ s ↔ ∃ n, a = s n where
  mp := by simp [Membership.mem, any_def]
  mpr h := mem_of_get_eq h.choose_spec

section Map

variable (f : α → β)

theorem drop_map (n : ℕ) (s : ωSequence α) : drop n (map f s) = map f (drop n s) :=
  ωSequence.ext fun _ => rfl

@[simp]
theorem get_map (n : ℕ) (s : ωSequence α) : (map f s) n = f (s n) :=
  rfl

theorem tail_map (s : ωSequence α) : tail (map f s) = map f (tail s) := rfl

@[simp]
theorem head_map (s : ωSequence α) : head (map f s) = f (head s) :=
  rfl

theorem map_eq (s : ωSequence α) : map f s = f (head s)::map f (tail s) := by
  rw [← ωSequence.eta (map f s), tail_map, head_map]

theorem map_cons (a : α) (s : ωSequence α) : map f (a::s) = f a::map f s := by
  rw [← ωSequence.eta (map f (a::s)), map_eq]; rfl

@[simp]
theorem map_id (s : ωSequence α) : map id s = s :=
  rfl

@[simp]
theorem map_map (g : β → δ) (f : α → β) (s : ωSequence α) : map g (map f s) = map (g ∘ f) s :=
  rfl

@[simp]
theorem map_tail (s : ωSequence α) : map f (tail s) = tail (map f s) :=
  rfl

theorem mem_map {a : α} {s : ωSequence α} : a ∈ s → f a ∈ map f s := fun ⟨n, h⟩ =>
  Exists.intro n (by rw [get_map, h])

theorem exists_of_mem_map {f} {b : β} {s : ωSequence α} : b ∈ map f s → ∃ a, a ∈ s ∧ f a = b :=
  fun ⟨n, h⟩ => ⟨s n, ⟨n, rfl⟩, h.symm⟩

end Map

section Zip

variable (f : α → β → δ)

theorem drop_zip (n : ℕ) (s₁ : ωSequence α) (s₂ : ωSequence β) :
    drop n (zip f s₁ s₂) = zip f (drop n s₁) (drop n s₂) :=
  ωSequence.ext fun _ => rfl

@[simp]
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
    zip f s₁ s₂ = f (head s₁) (head s₂)::zip f (tail s₁) (tail s₂) := by
  rw [← ωSequence.eta (zip f s₁ s₂)]; rfl

@[simp]
theorem get_enum (s : ωSequence α) (n : ℕ) : (enum s) n = (n, s n) :=
  rfl

theorem enum_eq_zip (s : ωSequence α) : enum s = zip Prod.mk nats s :=
  rfl

end Zip

@[simp]
theorem mem_const (a : α) : a ∈ const a :=
  Exists.intro 0 rfl

theorem const_eq (a : α) : const a = a::const a := by
  apply ωSequence.ext; intro n
  cases n <;> rfl

@[simp]
theorem tail_const (a : α) : tail (const a) = const a :=
  suffices tail (a::const a) = const a by rwa [← const_eq] at this
  rfl

@[simp]
theorem map_const (f : α → β) (a : α) : map f (const a) = const (f a) :=
  rfl

@[simp]
theorem get_const (n : ℕ) (a : α) : (const a) n = a :=
  rfl

@[simp]
theorem drop_const (n : ℕ) (a : α) : drop n (const a) = const a :=
  ωSequence.ext fun _ => rfl

@[simp]
theorem head_iterate (f : α → α) (a : α) : head (iterate f a) = a :=
  rfl

theorem get_succ_iterate' (n : ℕ) (f : α → α) (a : α) :
    (iterate f a) (succ n) = f ((iterate f a) n) := rfl

theorem tail_iterate (f : α → α) (a : α) : tail (iterate f a) = iterate f (f a) := by
  ext n
  rw [get_tail]
  induction n with
  | zero => rfl
  | succ n ih => rw [get_succ_iterate', ih, get_succ_iterate']

theorem iterate_eq (f : α → α) (a : α) : iterate f a = a::iterate f (f a) := by
  rw [← ωSequence.eta (iterate f a)]
  rw [tail_iterate]; rfl

@[simp]
theorem get_zero_iterate (f : α → α) (a : α) : (iterate f a) 0 = a :=
  rfl

theorem get_succ_iterate (n : ℕ) (f : α → α) (a : α) :
    (iterate f a) (succ n) = (iterate f (f a)) n := by rw [get_succ n (iterate f a), tail_iterate]

section Bisim

variable (R : ωSequence α → ωSequence α → Prop)

/-- equivalence relation -/
local infixl:50 " ~ " => R

/-- ω-sequences `s₁` and `s₂` are defined to be bisimulations if
their heads are equal and tails are bisimulations. -/
def IsBisimulation :=
  ∀ ⦃s₁ s₂⦄, s₁ ~ s₂ →
      head s₁ = head s₂ ∧ tail s₁ ~ tail s₂

theorem get_of_bisim (bisim : IsBisimulation R) {s₁ s₂} :
    ∀ n, s₁ ~ s₂ → s₁ n = s₂ n ∧ drop (n + 1) s₁ ~ drop (n + 1) s₂
  | 0, h => bisim h
  | n + 1, h =>
    match bisim h with
    | ⟨_, trel⟩ => get_of_bisim bisim n trel

-- If two ω-sequences are bisimilar, then they are equal
theorem eq_of_bisim (bisim : IsBisimulation R) {s₁ s₂} : s₁ ~ s₂ → s₁ = s₂ := fun r =>
  ωSequence.ext fun n => And.left (get_of_bisim R bisim n r)

end Bisim

theorem bisim_simple (s₁ s₂ : ωSequence α) :
    head s₁ = head s₂ → s₁ = tail s₁ → s₂ = tail s₂ → s₁ = s₂ := fun hh ht₁ ht₂ =>
  eq_of_bisim (fun s₁ s₂ => head s₁ = head s₂ ∧ s₁ = tail s₁ ∧ s₂ = tail s₂)
    (fun s₁ s₂ ⟨h₁, h₂, h₃⟩ => by rw [← h₂, ← h₃] ; grind)
    (And.intro hh (And.intro ht₁ ht₂))

theorem coinduction {s₁ s₂ : ωSequence α} :
    head s₁ = head s₂ →
      (∀ (β : Type u) (fr : ωSequence α → β),
      fr s₁ = fr s₂ → fr (tail s₁) = fr (tail s₂)) → s₁ = s₂ :=
  fun hh ht =>
  eq_of_bisim
    (fun s₁ s₂ =>
      head s₁ = head s₂ ∧
        ∀ (β : Type u) (fr : ωSequence α → β), fr s₁ = fr s₂ → fr (tail s₁) = fr (tail s₂))
    (fun s₁ s₂ h =>
      have h₁ : head s₁ = head s₂ := And.left h
      have h₂ : head (tail s₁) = head (tail s₂) := And.right h α (@head α) h₁
      have h₃ :
        ∀ (β : Type u) (fr : ωSequence α → β),
          fr (tail s₁) = fr (tail s₂) → fr (tail (tail s₁)) = fr (tail (tail s₂)) :=
        fun β fr => And.right h β fun s => fr (tail s)
      And.intro h₁ (And.intro h₂ h₃))
    (And.intro hh ht)

@[simp]
theorem iterate_id (a : α) : iterate id a = const a :=
  coinduction rfl fun β fr ch => by rw [tail_iterate, tail_const]; exact ch

theorem map_iterate (f : α → α) (a : α) : iterate f (f a) = map f (iterate f a) := by
  funext n
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold map iterate
    rw [map] at ih
    simp [ih]

section Corec

theorem corec_def (f : α → β) (g : α → α) (a : α) : corec f g a = map f (iterate g a) :=
  rfl

theorem corec_eq (f : α → β) (g : α → α) (a : α) : corec f g a = f a :: corec f g (g a) := by
  rw [corec_def, map_eq, head_iterate, tail_iterate]; rfl

theorem corec_id_id_eq_const (a : α) : corec id id a = const a := by
  rw [corec_def, map_id, iterate_id]

theorem corec_id_f_eq_iterate (f : α → α) (a : α) : corec id f a = iterate f a :=
  rfl

end Corec

section Corec'

theorem corec'_eq (f : α → β × α) (a : α) : corec' f a = (f a).1 :: corec' f (f a).2 :=
  corec_eq _ _ _

end Corec'

theorem unfolds_eq (g : α → β) (f : α → α) (a : α) : unfolds g f a = g a :: unfolds g f (f a) := by
  unfold unfolds; rw [corec_eq]

theorem get_unfolds_head_tail (n : ℕ) (s : ωSequence α) : (unfolds head tail s) n = s n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => rw [get_succ n (unfolds head tail s), get_succ n s, unfolds_eq, tail_cons, ih]

theorem unfolds_head_eq : ∀ s : ωSequence α, unfolds head tail s = s := fun s =>
  ωSequence.ext fun n => get_unfolds_head_tail n s

theorem interleave_eq (s₁ s₂ : ωSequence α) : s₁ ⋈ s₂ = head s₁::head s₂::(tail s₁ ⋈ tail s₂) := by
  let t := tail s₁ ⋈ tail s₂
  change s₁ ⋈ s₂ = head s₁::head s₂::t
  unfold interleave; unfold corecOn; rw [corec_eq]; dsimp; rw [corec_eq]; rfl

theorem tail_interleave (s₁ s₂ : ωSequence α) : tail (s₁ ⋈ s₂) = s₂ ⋈ tail s₁ := by
  unfold interleave corecOn; rw [corec_eq]; rfl

theorem interleave_tail_tail (s₁ s₂ : ωSequence α) : tail s₁ ⋈ tail s₂ = tail (tail (s₁ ⋈ s₂)) := by
  rw [interleave_eq s₁ s₂]; rfl

theorem get_interleave_left : ∀ (n : ℕ) (s₁ s₂ : ωSequence α),
    (s₁ ⋈ s₂) (2 * n) = s₁ n
  | 0, _, _ => rfl
  | n + 1, s₁, s₂ => by
    change (s₁ ⋈ s₂) (succ (succ (2 * n))) = s₁ (succ n)
    rw [get_succ (2 * n).succ (s₁ ⋈ s₂), get_succ (2 * n) (s₁ ⋈ s₂).tail,
      interleave_eq, tail_cons, tail_cons]
    rw [get_interleave_left n (tail s₁) (tail s₂)]
    rfl

theorem get_interleave_right : ∀ (n : ℕ) (s₁ s₂ : ωSequence α),
    (s₁ ⋈ s₂) (2 * n + 1) = s₂ n
  | 0, _, _ => rfl
  | n + 1, s₁, s₂ => by
    change (s₁ ⋈ s₂) (succ (succ (2 * n + 1))) = s₂ (succ n)
    rw [get_succ (2 * n + 1).succ (s₁ ⋈ s₂), get_succ (2 * n + 1) (s₁ ⋈ s₂).tail,
      interleave_eq, tail_cons, tail_cons, get_interleave_right n (tail s₁) (tail s₂)]
    rfl

theorem mem_interleave_left {a : α} {s₁ : ωSequence α} (s₂ : ωSequence α) : a ∈ s₁ → a ∈ s₁ ⋈ s₂ :=
  fun ⟨n, h⟩ => Exists.intro (2 * n) (by rw [h, get_interleave_left])

theorem mem_interleave_right {a : α} {s₁ : ωSequence α} (s₂ : ωSequence α) : a ∈ s₂ → a ∈ s₁ ⋈ s₂ :=
  fun ⟨n, h⟩ => Exists.intro (2 * n + 1) (by rw [h, get_interleave_right])

theorem odd_eq (s : ωSequence α) : odd s = even (tail s) :=
  rfl

@[simp]
theorem head_even (s : ωSequence α) : head (even s) = head s :=
  rfl

theorem tail_even (s : ωSequence α) : tail (even s) = even (tail (tail s)) := by
  unfold even
  rw [corec_eq]
  rfl

theorem even_cons_cons (a₁ a₂ : α) (s : ωSequence α) : even (a₁::a₂::s) = a₁::even s := by
  unfold even
  rw [corec_eq]; rfl

theorem even_tail (s : ωSequence α) : even (tail s) = odd s :=
  rfl

theorem even_interleave (s₁ s₂ : ωSequence α) : even (s₁ ⋈ s₂) = s₁ :=
  eq_of_bisim (fun s₁' s₁ => ∃ s₂, s₁' = even (s₁ ⋈ s₂))
    (fun s₁' s₁ ⟨s₂, h₁⟩ => by
      rw [h₁]
      constructor
      · rfl
      · exact ⟨tail s₂, by rw [interleave_eq, even_cons_cons, tail_cons]⟩)
    (Exists.intro s₂ rfl)

theorem interleave_even_odd (s₁ : ωSequence α) : even s₁ ⋈ odd s₁ = s₁ :=
  eq_of_bisim (fun s' s => s' = even s ⋈ odd s)
    (fun s' s (h : s' = even s ⋈ odd s) => by
      rw [h]; constructor
      · rfl
      · simp [odd_eq, odd_eq, tail_interleave, tail_even])
    rfl

theorem get_even : ∀ (n : ℕ) (s : ωSequence α), (even s) n = s (2 * n)
  | 0, _ => rfl
  | succ n, s => by
    change (even s) (succ n) = s (succ (succ (2 * n)))
    rw [get_succ n s.even, get_succ (2 * n).succ s, tail_even, get_even n]; rfl

theorem get_odd : ∀ (n : ℕ) (s : ωSequence α), (odd s) n = s (2 * n + 1) := fun n s => by
  rw [odd_eq, get_even]; rfl

theorem mem_of_mem_even (a : α) (s : ωSequence α) : a ∈ even s → a ∈ s := fun ⟨n, h⟩ =>
  Exists.intro (2 * n) (by rw [h, get_even])

theorem mem_of_mem_odd (a : α) (s : ωSequence α) : a ∈ odd s → a ∈ s := fun ⟨n, h⟩ =>
  Exists.intro (2 * n + 1) (by rw [h, get_odd])

@[simp] theorem nil_append_ωSequence (s : ωSequence α) : appendωSequence [] s = s :=
  rfl

theorem cons_append_ωSequence (a : α) (l : List α) (s : ωSequence α) :
    appendωSequence (a::l) s = a::appendωSequence l s :=
  rfl

@[simp] theorem append_append_ωSequence : ∀ (l₁ l₂ : List α) (s : ωSequence α),
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

@[simp] lemma get_append_right : (x ++ω a) (x.length + n) = a n := by
  induction x <;> simp [Nat.succ_add, *, cons_append_ωSequence]

theorem get_append_right' {xl : List α} {xs : ωSequence α} {k : ℕ} (h : xl.length ≤ k) :
    (xl ++ω xs) k = xs (k - xl.length) := by
  obtain ⟨n, rfl⟩ := show ∃ n, k = xl.length + n by use (k - xl.length) ; omega
  simp only [Nat.add_sub_cancel_left] ; apply get_append_right

@[simp] lemma get_append_length : (x ++ω a) x.length = a 0 := get_append_right 0 x a

lemma append_right_injective (h : x ++ω a = x ++ω b) : a = b := by
  ext n; replace h := congr_arg (fun a ↦ a (x.length + n)) h; simpa using h

@[simp] lemma append_right_inj : x ++ω a = x ++ω b ↔ a = b :=
  ⟨append_right_injective x a b, by simp +contextual⟩

lemma append_left_injective (h : x ++ω a = y ++ω b) (hl : x.length = y.length) : x = y := by
  apply List.ext_getElem hl
  intros
  rw [← get_append_left, ← get_append_left, h]

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

theorem mem_append_ωSequence_right : ∀ {a : α} (l : List α) {s : ωSequence α}, a ∈ s → a ∈ l ++ω s
  | _, [], _, h => h
  | a, List.cons _ l, s, h =>
    have ih : a ∈ l ++ω s := mem_append_ωSequence_right l h
    mem_cons_of_mem _ ih

theorem mem_append_ωSequence_left : ∀ {a : α} {l : List α} (s : ωSequence α), a ∈ l → a ∈ l ++ω s
  | _, [], _, h => absurd h List.not_mem_nil
  | a, List.cons b l, s, h =>
    Or.elim (List.eq_or_mem_of_mem_cons h) (fun aeqb : a = b => Exists.intro 0 aeqb)
      fun ainl : a ∈ l => mem_cons_of_mem b (mem_append_ωSequence_left s ainl)

@[simp]
theorem take_zero (s : ωSequence α) : take 0 s = [] :=
  rfl

-- This lemma used to be simp, but we removed it from the simp set because:
-- 1) It duplicates the (often large) `s` term, resulting in large tactic states.
-- 2) It conflicts with the very useful `dropLast_take` lemma below (causing nonconfluence).
theorem take_succ (n : ℕ) (s : ωSequence α) : take (succ n) s = head s::take n (tail s) :=
  rfl

@[simp] theorem take_succ_cons {a : α} (n : ℕ) (s : ωSequence α) :
    take (n+1) (a::s) = a :: take n s := rfl

theorem take_succ' {s : ωSequence α} : ∀ n, s.take (n+1) = s.take n ++ [s n]
  | 0 => rfl
  | n+1 => by rw [take_succ, take_succ' n, ← List.cons_append, ← take_succ, get_tail]

@[simp]
theorem take_one {xs : ωSequence α} :
    xs.take 1 = [xs 0] := by
  simp only [take_succ, take_zero]

@[simp]
theorem take_one' {xs : ωSequence α} :
    xs.take 1 = [xs 0] := by
  apply take_one

@[simp]
theorem length_take (n : ℕ) (s : ωSequence α) : (take n s).length = n := by
  induction n generalizing s <;> simp [*, take_succ]

@[simp]
theorem take_take {s : ωSequence α} : ∀ {m n}, (s.take n).take m = s.take (min n m)
  | 0, n => by rw [Nat.min_zero, List.take_zero, take_zero]
  | m, 0 => by rw [Nat.zero_min, take_zero, List.take_nil]
  | m+1, n+1 => by rw [take_succ, List.take_succ_cons, Nat.succ_min_succ, take_succ, take_take]

@[simp] theorem concat_take_get {n : ℕ} {s : ωSequence α} : s.take n ++ [s n] = s.take (n + 1) :=
  (take_succ' n).symm

theorem getElem?_take {s : ωSequence α} : ∀ {k n}, k < n → (s.take n)[k]? = s k
  | 0, _+1, _ => by simp only [length_take, zero_lt_succ, List.getElem?_eq_getElem]; rfl
  | k+1, n+1, h => by
    rw [take_succ, List.getElem?_cons_succ, getElem?_take (Nat.lt_of_succ_lt_succ h), get_succ k s]

theorem getElem?_take_succ (n : ℕ) (s : ωSequence α) :
    (take (succ n) s)[n]? = some (s n) :=
  getElem?_take (Nat.lt_succ_self n)

@[simp] theorem dropLast_take {n : ℕ} {xs : ωSequence α} :
    (ωSequence.take n xs).dropLast = ωSequence.take (n-1) xs := by
  cases n with
  | zero => simp
  | succ n => rw [take_succ', List.dropLast_concat, Nat.add_one_sub_one]

@[simp]
theorem append_take_drop (n : ℕ) (s : ωSequence α) : appendωSequence (take n s) (drop n s) = s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>rw [take_succ, drop_succ, cons_append_ωSequence, ih (tail s), ωSequence.eta]

lemma append_take : x ++ (a.take n) = (x ++ω a).take (x.length + n) := by
  induction x <;> simp [take, Nat.add_comm, cons_append_ωSequence, *]

@[simp] lemma take_get (h : m < (a.take n).length) : (a.take n)[m] = a m := by
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

@[simp] lemma take_prefix : a.take m <+: a.take n ↔ m ≤ n :=
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
  ext k ; simp (disch := omega) only [get_drop, get_append_right']
  congr ; omega

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

protected theorem cycle_g_cons (a : α) (a₁ : α) (l₁ : List α) (a₀ : α) (l₀ : List α) :
    ωSequence.cycleG (a, a₁::l₁, a₀, l₀) = (a₁, l₁, a₀, l₀) :=
  rfl

theorem cycle_eq : ∀ (l : List α) (h : l ≠ []), cycle l h = l ++ω cycle l h
  | [], h => absurd rfl h
  | List.cons a l, _ =>
    have gen (l' a') : corec ωSequence.cycleF ωSequence.cycleG (a', l', a, l) =
        (a'::l') ++ω corec ωSequence.cycleF ωSequence.cycleG (a, l, a, l) := by
      induction l' generalizing a' with
      | nil => rw [corec_eq]; rfl
      | cons a₁ l₁ ih => rw [corec_eq, ωSequence.cycle_g_cons, ih a₁]; rfl
    gen l a

theorem mem_cycle {a : α} {l : List α} : ∀ h : l ≠ [], a ∈ l → a ∈ cycle l h := fun h ainl => by
  rw [cycle_eq]; exact mem_append_ωSequence_left _ ainl

@[simp]
theorem cycle_singleton (a : α) : cycle [a] (by simp) = const a :=
  coinduction rfl fun β fr ch => by rwa [cycle_eq, const_eq]

theorem tails_eq (s : ωSequence α) : tails s = tail s::tails (tail s) := by
  unfold tails; rw [corec_eq]; rfl

@[simp]
theorem get_tails (n : ℕ) (s : ωSequence α) : (tails s) n = drop n (tail s) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => rw [get_succ n s.tails, drop_succ, tails_eq, tail_cons, ih]

theorem tails_eq_iterate (s : ωSequence α) : tails s = iterate tail (tail s) :=
  rfl

theorem inits_core_eq (l : List α) (s : ωSequence α) :
    initsCore l s = l::initsCore (l ++ [head s]) (tail s) := by
    unfold initsCore corecOn
    rw [corec_eq]

theorem tail_inits (s : ωSequence α) :
    tail (inits s) = initsCore [head s, head (tail s)] (tail (tail s)) := by
    unfold inits
    rw [inits_core_eq]; rfl

theorem inits_tail (s : ωSequence α) : inits (tail s) = initsCore [head (tail s)] (tail (tail s)) :=
  rfl

theorem cons_get_inits_core (a : α) (n : ℕ) (l : List α) (s : ωSequence α) :
    (a :: (initsCore l s) n) = (initsCore (a :: l) s) n := by
  induction n generalizing l s with
  | zero => rfl
  | succ n ih =>
    rw [get_succ n (initsCore l s), inits_core_eq, tail_cons, ih, inits_core_eq (a :: l) s]
    rfl

@[simp]
theorem get_inits (n : ℕ) (s : ωSequence α) : (inits s) n = take (succ n) s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    rw [get_succ n s.inits, take_succ, ← ih, tail_inits, inits_tail, cons_get_inits_core]

theorem inits_eq (s : ωSequence α) :
    inits s = [head s]::map (List.cons (head s)) (inits (tail s)) := by
  apply ωSequence.ext; intro n
  induction' n with n _
  · rfl
  · rw [get_inits, get_succ n ([s.head] :: map (List.cons s.head) s.tail.inits),
      tail_cons, get_map, get_inits]
    rfl

theorem zip_inits_tails (s : ωSequence α) : zip appendωSequence (inits s) (tails s) = const s := by
  apply ωSequence.ext; intro n
  rw [get_zip, get_inits, get_tails, get_const, take_succ, cons_append_ωSequence, append_take_drop,
    ωSequence.eta]

theorem identity (s : ωSequence α) : pure id ⊛ s = s :=
  rfl

theorem composition (g : ωSequence (β → δ)) (f : ωSequence (α → β)) (s : ωSequence α) :
    pure comp ⊛ g ⊛ f ⊛ s = g ⊛ (f ⊛ s) :=
  rfl

theorem homomorphism (f : α → β) (a : α) : pure f ⊛ pure a = pure (f a) :=
  rfl

theorem interchange (fs : ωSequence (α → β)) (a : α) :
    fs ⊛ pure a = (pure fun f : α → β => f a) ⊛ fs :=
  rfl

theorem map_eq_apply (f : α → β) (s : ωSequence α) : map f s = pure f ⊛ s :=
  rfl

theorem get_nats (n : ℕ) : nats n = n :=
  rfl

theorem nats_eq : nats = cons 0 (map succ nats) := by
  apply ωSequence.ext; intro n
  induction' n with n _
  · rfl
  rw [get_succ n nats] ; rfl

theorem extract_eq_drop_take {xs : ωSequence α} {m n : ℕ} :
    xs.extract m n = take (n - m) (xs.drop m) := by
  rfl

theorem extract_eq_ofFn {xs : ωSequence α} {m n : ℕ} :
    xs.extract m n = List.ofFn (fun k : Fin (n - m) ↦ xs (m + k)) := by
  ext k x ; rcases (show k < n - m ∨ ¬ k < n - m by omega) with h_k | h_k
    <;> simp (disch := omega) [extract_eq_drop_take, getElem?_take, get_drop]
    <;> aesop

theorem extract_eq_extract {xs xs' : ωSequence α} {m n m' n' : ℕ}
    (h : xs.extract m n = xs'.extract m' n') :
    n - m = n' - m' ∧ ∀ k < n - m, xs (m + k) = xs' (m' + k) := by
  simp only [extract_eq_ofFn, List.ofFn_inj', Sigma.mk.injEq] at h
  obtain ⟨h_eq, h_fun⟩ := h
  rw [← h_eq] at h_fun ; simp only [heq_eq_eq, funext_iff, Fin.forall_iff] at h_fun
  simp only [← h_eq, true_and] ; intro k h_k ; simp only [h_fun k h_k]

theorem extract_eq_take {xs : ωSequence α} {n : ℕ} :
    xs.extract 0 n = xs.take n := by
  simp only [extract_eq_drop_take, Nat.sub_zero, drop_zero]

theorem append_extract_drop {xs : ωSequence α} {n : ℕ} :
    (xs.extract 0 n) ++ω (xs.drop n) = xs := by
  simp only [extract_eq_take, append_take_drop]

theorem extract_apppend_right_right {xl : List α} {xs : ωSequence α} {m n : ℕ} (h : xl.length ≤ m) :
    (xl ++ω xs).extract m n = xs.extract (m - xl.length) (n - xl.length) := by
  have h1 : n - xl.length - (m - xl.length) = n - m := by omega
  simp (disch := omega) only [extract_eq_drop_take, drop_append_of_ge_length, h1]

theorem extract_append_zero_right {xl : List α} {xs : ωSequence α} {n : ℕ} (h : xl.length ≤ n) :
    (xl ++ω xs).extract 0 n = xl ++ (xs.extract 0 (n - xl.length)) := by
  obtain ⟨k, rfl⟩ := show ∃ k, n = xl.length + k by use (n - xl.length) ; omega
  simp only [extract_eq_take, ← append_take, Nat.add_sub_cancel_left]

theorem extract_drop {xs : ωSequence α} {k m n : ℕ} :
    (xs.drop k).extract m n = xs.extract (k + m) (k + n) := by
  have h1 : k + n - (k + m) = n - m := by omega
  simp only [extract_eq_drop_take, drop_drop, h1]

theorem length_extract {xs : ωSequence α} {m n : ℕ} :
    (xs.extract m n).length = n - m := by
  simp only [extract_eq_drop_take, length_take]

theorem extract_eq_nil {xs : ωSequence α} {n : ℕ} :
    xs.extract n n = [] := by
  simp only [extract_eq_drop_take, Nat.sub_self, take_zero]

theorem extract_eq_nil_iff {xs : ωSequence α} {m n : ℕ} :
    xs.extract m n = [] ↔ m ≥ n := by
  simp only [extract_eq_drop_take, ← List.length_eq_zero_iff, length_take, ge_iff_le]
  omega

theorem get_extract {xs : ωSequence α} {m n k : ℕ} (h : k < n - m) :
    (xs.extract m n)[k]'(by simp only [length_extract, h]) = xs (m + k) := by
  simp only [extract_eq_drop_take, take_get, get_drop]

theorem append_extract_extract {xs : ωSequence α} {k m n : ℕ} (h_km : k ≤ m) (h_mn : m ≤ n) :
    (xs.extract k m) ++ (xs.extract m n) = xs.extract k n := by
  have h1 : n - k = (m - k) + (n - m) := by omega
  have h2 : k + (m - k) = m := by omega
  simp only [extract_eq_drop_take, h1, take_add, drop_drop, h2]

theorem extract_succ_right {xs : ωSequence α} {m n : ℕ} (h_mn : m ≤ n) :
    xs.extract m (n + 1) = xs.extract m n ++ [xs n] := by
  rw [← append_extract_extract h_mn (show n ≤ n + 1 by omega)] ; congr
  simp only [extract_eq_drop_take, Nat.add_sub_cancel_left, take_one, get_drop, Nat.add_zero]

theorem extract_extract2' {xs : ωSequence α} {m n i j : ℕ} (h : j ≤ n - m) :
    (xs.extract m n).extract i j = xs.extract (m + i) (m + j) := by
  ext k x ; rcases (show k < j - i ∨ ¬ k < j - i by omega) with h_k | h_k
    <;> simp [extract_eq_ofFn, h_k]
  · simp [(show i + k < n - m by omega), (show k < m + j - (m + i) by omega), Nat.add_assoc]
  · simp only [(show ¬k < m + j - (m + i) by omega), IsEmpty.forall_iff]

theorem extract_extract2 {xs : ωSequence α} {n i j : ℕ} (h : j ≤ n) :
    (xs.extract 0 n).extract i j = xs.extract i j := by
  simp only [extract_extract2' (show j ≤ n - 0 by omega), Nat.zero_add]

theorem extract_extract1 {xs : ωSequence α} {n i : ℕ} :
    (xs.extract 0 n).extract i = xs.extract i n := by
  simp only [length_extract, extract_extract2 (show n ≤ n by omega), Nat.sub_zero]

end ωSequence
