import Mathlib.Data.Multiset.Functor
import Mathlib.Data.PFun
import Mathlib.Logic.Relation
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Finset.Functor
import Mathlib.Data.Set.Functor

/-! # Computable catalogue of a relation

Define the predicate `Relation.Catalogues`, which expresses that `f : α → γ`, where `γ` has a
`Membership β γ` instance, takes `a : α` to a container containing exactly its descendents.

This notion interacts nicely with `Relation.Comp` in the case where `γ` has the form `m β`, and
`m` is a monad whose structure interacts reasonably with the membership. We abstract this situation
as a typeclass `MonadMem`, whose fields generalize (for example) the results
`List.mem_singleton` (for `pure`) and `List.mem_flatMap` (for `bind`).
-/

universe u v

class LawfulEmptyCollection (α γ : Type*) [Membership α γ] extends EmptyCollection γ where
  notMem_empty (a : α) : a ∉ (∅ : γ)

namespace LawfulEmptyCollection

attribute [simp] notMem_empty

@[implicit_reducible]
def of_setLike {α γ : Type*} [SetLike γ α] [EmptyCollection γ]
    (h : (∅ : γ) = (∅ : Set α)) : LawfulEmptyCollection α γ where
  notMem_empty a := by simp [← SetLike.mem_coe, h]

lemma coe_empty {α γ : Type*} [SetLike γ α] [LawfulEmptyCollection α γ] :
  (∅ : γ) = (∅ : Set α) := by ext; simp

instance (α : Type*) : LawfulEmptyCollection α (Set α) where
  notMem_empty := Set.notMem_empty

instance (α : Type*) : LawfulEmptyCollection α (List α) where
  notMem_empty _ := List.not_mem_nil

instance (α : Type*) : LawfulEmptyCollection α (Multiset α) where
  notMem_empty := Multiset.notMem_zero

instance (α : Type*) : LawfulEmptyCollection α (Finset α) where
  notMem_empty := Finset.notMem_empty

scoped instance (α : Type*) : LawfulEmptyCollection α (Option α) where
  emptyCollection := Option.none
  notMem_empty := Option.not_mem_none

scoped instance (α : Type*) : LawfulEmptyCollection α (Part α) where
  emptyCollection := Part.none
  notMem_empty := Part.notMem_none

end LawfulEmptyCollection

class MonadMem (m : Type u → Type v) [Pure m] [Bind m] where
  instMembership (α : Type u) : Membership α (m α) := by infer_instance
  mem_pure_iff {α : Type u} {a b : α} : b ∈ (pure a : m α) ↔ b = a
  mem_bind_iff {α β : Type u} {c : m α} {f : α → m β} {b : β} : b ∈ (c >>= f) ↔ ∃ a ∈ c, b ∈ f a

namespace MonadMem

attribute [simp] MonadMem.mem_pure_iff MonadMem.mem_bind_iff
attribute [instance_reducible, instance] MonadMem.instMembership

variable {α β : Type u} {m : Type u → Type v} [Pure m] [Bind m] [MonadMem m]

instance : Membership α (m α) := instMembership α

instance : MonadMem List where
  mem_pure_iff := List.mem_singleton
  mem_bind_iff := List.mem_flatMap

instance : MonadMem Multiset where
  mem_pure_iff := Multiset.mem_singleton
  mem_bind_iff := Multiset.mem_bind

instance : MonadMem Part where
  mem_pure_iff := Part.mem_some_iff
  mem_bind_iff := Part.mem_bind_iff

instance : MonadMem Option where
  mem_pure_iff := by simp [Eq.comm]
  mem_bind_iff := Option.mem_bind_iff

instance [(P : Prop) → Decidable P] : MonadMem Finset where
  mem_pure_iff := Finset.mem_singleton
  mem_bind_iff := Finset.mem_sup

attribute [scoped instance] Set.monad

scoped instance : MonadMem Set where
  mem_pure_iff := Set.mem_singleton_iff
  mem_bind_iff := by simp

alias ⟨eq_of_mem_pure, mem_pure_of_eq⟩ := mem_pure_iff

alias ⟨exists_of_mem_bind, _⟩ := mem_bind_iff

lemma mem_pure_self (a : α) : a ∈ (pure a : m α) := mem_pure_of_eq rfl

lemma mem_bind {c : m α} {f : α → m β} {a : α} (ha : a ∈ c) {b : β} (hb : b ∈ f a) :
    b ∈ c >>= f := mem_bind_iff.mpr ⟨a, ha, hb⟩

section Lawful

variable {m : Type u → Type v} [Monad m] [LawfulMonad m] [MonadMem m]

@[simp] lemma mem_map {f : α → β} {c : m α} {b : β} :
    b ∈ f <$> c ↔ ∃ a ∈ c, b = f a := by
  simp_rw [← bind_pure_comp, mem_bind_iff, mem_pure_iff]

alias ⟨exists_of_mem_map, _⟩ := mem_map

lemma mem_map_of_mem (f : α → β) {a : α} {c : m α} (h : a ∈ c) :
    f a ∈ f <$> c := mem_map.mpr ⟨a, h, rfl⟩

lemma forall_mem_map {f : α → β} {c : m α} {P : β → Prop} :
    (∀ b ∈ f <$> c, P b) ↔ ∀ a ∈ c, P (f a) := by grind [mem_map]

lemma exists_mem_map {f : α → β} {c : m α} {P : β → Prop} :
    (∃ b ∈ f <$> c, P b) ↔ ∃ a ∈ c, P (f a) := by grind [mem_map]

end Lawful

protected def filter [EmptyCollection (m α)] (c : m α) (p : α → Bool) : m α :=
    c >>= fun a ↦ if p a then pure a else ∅

@[simp] lemma mem_filter [LawfulEmptyCollection α (m α)] {a : α} {c : m α} {p : α → Bool} :
    a ∈ MonadMem.filter c p ↔ a ∈ c ∧ p a := by
  rw [MonadMem.filter, mem_bind_iff]
  constructor
  · intro ⟨a', hmem, ha'⟩
    split_ifs at ha' <;> simp_all
  · intro ⟨hmem, ha⟩
    use a, hmem
    simp [ha]

lemma mem_of_mem_filter [LawfulEmptyCollection α (m α)] {a : α} {c : m α} {p : α → Bool}
    (h : a ∈ MonadMem.filter c p) : a ∈ c := (mem_filter.mp h).1

lemma pred_of_mem_filter [LawfulEmptyCollection α (m α)] {a : α} {c : m α} {p : α → Bool}
    (h : a ∈ MonadMem.filter c p) : p a = true := (mem_filter.mp h).2

lemma mem_filter_of_mem [LawfulEmptyCollection α (m α)] {a : α} {c : m α} {p : α → Bool}
  (hmem : a ∈ c) (ha : p a) : a ∈ MonadMem.filter c p := mem_filter.mpr ⟨hmem, ha⟩

end MonadMem

open List Function MonadMem

namespace Relation

variable {α β : Type u} {m : Type u → Type v}

def Catalogues {γ : Type*} [Membership β γ] (f : α → γ) (r : α → β → Prop) := ∀ a b, b ∈ f a ↔ r a b

namespace Catalogues

lemma rel_of_mem {γ : Type*} [Membership β γ] {f : α → γ} {r : α → β → Prop} (h : Catalogues f r)
  (hab : b ∈ f a) : r a b := (h a b).mp hab

lemma mem_of_rel {γ : Type*} [Membership β γ] {f : α → γ} {r : α → β → Prop} (h : Catalogues f r)
    (hab : r a b) : b ∈ f a := (h a b).mpr hab

protected lemma comp [Pure m] [Bind m] [MonadMem m] {f : α → m β} {g : β → m γ} {r : α → β → Prop}
    {s : β → γ → Prop} (h : Catalogues f r) (h' : Catalogues g s) :
    Catalogues (α := α) (f · >>= g) (Comp r s) := by
  intro a c
  simp [h a, (h' · c), Comp]

open SetRel in
lemma _root_.PFun.catalogues_graph (f : α →. β) : Catalogues f (· ~[f.graph'] ·) := by
  intro a b
  simp [PFun.graph']

variable [Pure m] [Bind m] [MonadMem m] {f : α → m α} {r : α → α → Prop}

lemma mem_iterate_of_reflTransGen (h : Catalogues f r) (hab : ReflTransGen r a b) :
    ∃ n, b ∈ (· >>= f)^[n] (pure a) := by
  induction hab with
  | refl => use 0; simp
  | @tail b c _ htr ih =>
    obtain ⟨n, hn⟩ := ih
    use n + 1
    simp only [iterate_succ', comp_apply, mem_bind_iff]
    use b, hn, h.mem_of_rel htr

lemma reflTransGen_of_mem_iterate (h : Catalogues f r) {n : ℕ} {l : m α}
    (hb : b ∈ (· >>= f)^[n] l) : ∃ a ∈ l, ReflTransGen r a b := by
  induction n generalizing l with
  | zero => use b, by simpa using hb
  | succ n ih =>
    rw [iterate_succ, comp_apply] at hb
    obtain ⟨a', ha', hrel⟩ := ih hb
    obtain ⟨a, hal, ha⟩ := mem_bind_iff.mp ha'
    use a, hal, hrel.head (h.rel_of_mem ha)

lemma reflTransGen_iff (h : Catalogues f r) :
    ReflTransGen r a b ↔ ∃ n, b ∈ (· >>= f)^[n] (pure a) :=
  ⟨h.mem_iterate_of_reflTransGen, fun ⟨n, hn⟩ ↦ by simpa using h.reflTransGen_of_mem_iterate hn⟩

end Catalogues

end Relation
