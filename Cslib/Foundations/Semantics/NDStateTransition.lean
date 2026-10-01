/-
Copyright (c) 2025 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/

module

public import Mathlib.Computability.StateTransition
public import Cslib.Foundations.Relation.Confluence
public import Mathlib.Data.List.Basic

/-! # Non-deterministic state transisions

- Can we generalise `f : σ → Option σ` and `f : σ → List σ` to any monadic codomain?
-/

@[expose] public section

variable {α β γ σ : Type*}

namespace PFun

lemma mem_comp {f : α →. β} {g : β →. γ} {x : α} {y : β} {z : γ} (hxy : y ∈ f x) (hyz : z ∈ g y) :
    z ∈ g.comp f x := Part.mem_bind hxy hyz

@[simp] lemma mem_comp_iff {f : α →. β} {g : β →. γ} {x : α} {z : γ} :
    z ∈ g.comp f x ↔ ∃ y ∈ f x, z ∈ g y := Part.mem_bind_iff

lemma mem_dom_of_comp {f : α →. β} {g : β →. γ} {x : α} (h : x ∈ (g.comp f).Dom) : x ∈ f.Dom :=
  Part.Dom.of_bind h

lemma mem_dom_of_mem_comp {f : α →. β} {g : β →. γ} {x : α} {z : γ} (h : z ∈ g.comp f x) :
    x ∈ f.Dom := mem_dom_of_comp <| (mem_dom _ _).mpr ⟨z, h⟩

variable {f : α →. β ⊕ α} {a : α} {b : β}

theorem notMem_dom_fix (h : a ∉ f.Dom) : a ∉ f.fix.Dom := by
  contrapose h
  exact dom_of_mem_fix (Part.get_mem h)

theorem fix_fwd_eq_none (h : a ∉ f.Dom) : f.fix a = Part.none := by
  rw [Part.eq_none_iff']
  exact notMem_dom_fix h

variable {f : α →. α} {n : ℕ}

protected def iterate (f : α →. α) (n : ℕ) : α →. α := f.comp^[n] (.id α)

lemma iterate_zero (f : α →. α) : f.iterate 0 = PFun.id α := rfl

lemma iterate_succ : f.iterate (n + 1) = f.comp (f.iterate n) := by
  simp_rw [PFun.iterate, Function.iterate_succ', Function.comp_apply]

lemma iterate_one : f.iterate 1 = f := by rw [f.iterate_succ, f.iterate_zero, f.comp_id]

lemma iterate_comp_right_eq {g : β →. α} : (f.iterate n).comp g = f.comp^[n] g := by
  induction n with
  | zero => simp [f.iterate_zero]
  | succ n ih => rw [f.iterate_succ, PFun.comp_assoc, ih, Function.iterate_succ',
    Function.comp_apply]

lemma iterate_succ' : f.iterate (n + 1) = (f.iterate n).comp f := by
  rw [f.iterate_comp_right_eq, PFun.iterate, Function.iterate_succ, Function.comp_apply, f.comp_id]

lemma iterate_add {n m : ℕ} : f.iterate (n + m) = (f.iterate n).comp (f.iterate m) := by
  rw [f.iterate_comp_right_eq]
  simp [PFun.iterate, Function.iterate_add]

lemma iterate_coe (f : α → α) (n : ℕ) : (f : α →. α).iterate n = f^[n] := by
  induction n with
  | zero => simp [iterate_zero]
  | succ n ih => simp [coe_comp, iterate_succ', ih]

lemma mem_iterate_coe_iff {x y : α} {f : α → α} {n : ℕ} :
    y ∈ (f : α →. α).iterate n x ↔ y = f^[n] x := by
  simp [iterate_coe]

lemma iterate_id (n : ℕ) : (PFun.id α).iterate n = .id α := by
  rw [← coe_id, iterate_coe, Function.iterate_id, coe_id]

lemma mem_dom_of_mem_iterate_succ {x y : α} {f : α →. α} {n : ℕ} (h : y ∈ f.iterate (n + 1) x) :
    x ∈ f.Dom := mem_dom_of_mem_comp (f.iterate_succ' ▸ h)

lemma iterate_succ_apply_of_mem_dom {x : α} (h : x ∈ f.Dom) {n : ℕ} :
    f.iterate (n + 1) x = f.iterate n (f.fn x h) := by
  rw [iterate_succ', comp_apply, h.bind (f.iterate n), fn]

end PFun

namespace Cslib

universe u

variable {α β γ σ : Type*} {f : σ →. σ} {p : σ → Bool}

open Part PFun Sum

def iterFind (f : σ →. σ) (p : σ → Bool) : σ →. σ :=
  PFun.fix fun (x : σ) ↦ if p x then Part.some (inl x) else (f x).map inr

lemma iterFind_stop {x : σ} (h : p x = true) : x ∈ iterFind f p x :=
  fix_stop <| by simp [h]

lemma mem_iterFind_iff_of_true {x y : σ} (h : p x = true) : y ∈ iterFind f p x ↔ y = x := by
  grind [Part.mem_eq, iterFind_stop]

grind_pattern mem_iterFind_iff_of_true => y ∈ iterFind f p x where
  guard p x = true

alias ⟨eq_of_mem_iterFind_of_true, _⟩ := mem_iterFind_iff_of_true

attribute [local implicit_reducible] PFun

lemma iterFind_fwd_none {x : σ} (hx : p x = false) (hf : f x = Part.none) :
    iterFind f p x = Part.none := by
  apply fix_fwd_eq_none
  simp_all

lemma dom_of_mem_iterFind {x y : σ} (hx : p x = false) (hx' : y ∈ iterFind f p x) :
    x ∈ f.Dom := by
  contrapose hx'
  rw [PFun.Dom, Set.mem_ofPred, ← Part.eq_none_iff'] at hx'
  simp [iterFind_fwd_none hx hx']

lemma mem_dom_of_mem_dom_iterFind {x : σ} (hx : p x = false) (hx' : x ∈ (iterFind f p).Dom) :
    x ∈ f.Dom := by
  obtain ⟨y, hx'⟩ := PFun.mem_dom _ _ |>.mp hx'
  exact dom_of_mem_iterFind hx hx'

lemma iterFind_fwd_eq {x : σ} (hx : p x = false) : iterFind f p x = (f x).bind (iterFind f p) := by
  obtain (hf | ⟨y, hf⟩) := (f x).eq_none_or_eq_some
  · simp_all [iterFind_fwd_none hx hf]
  · rw [hf, Part.bind_some]
    apply fix_fwd_eq
    simp_all

lemma iterFind_fwd_eq_comp {x : σ} (hx : p x = false) :
  iterFind f p x = (iterFind f p).comp f x := iterFind_fwd_eq hx

lemma iterFind_fwd {x y : σ} (h : y ∈ iterFind f p x) (hx : p x = false) :
    y ∈ (f x).bind (iterFind f p) := iterFind_fwd_eq hx ▸ h

grind_pattern iterFind_fwd => y ∈ iterFind f p x where
  guard p x = false

lemma iterFind_fwd_get {x y : σ} (h : y ∈ iterFind f p x) (hx : p x = false) :
    y ∈ iterFind f p (f.fn x <| dom_of_mem_iterFind hx h) := by
  convert iterFind_fwd h hx
  have : Part.some (f.fn x (dom_of_mem_iterFind hx h)) = f x :=
    Part.some_get <| dom_of_mem_iterFind hx h
  grind [Part.bind_eq_bind, Part.bind_some]

@[grind →]
lemma iterFind_fwd_of_mem {x y z : σ} (h : z ∈ iterFind f p x) (hx : p x = false) (hy : y ∈ f x) :
  z ∈ iterFind f p y := Part.bind_of_mem hy (iterFind f p) ▸ iterFind_fwd h hx

/-- Recursion principle for `iterFind`. -/
@[elab_as_elim]
def iterFindRec {y : σ} {C : σ → Sort u} {x : σ} (h : y ∈ iterFind f p x)
    (stop : (x : σ) → p x = true → y ∈ iterFind f p x → C x)
    (fwd : (x : σ) → p x = false → y ∈ iterFind f p x →
      ((x' : σ) → x' ∈ f x → C x') → C x) : C x :=
  PFun.fixInduction h <| fun x' hmem ih ↦
    match hx' : p x' with
    | true => stop x' hx' hmem
    | false => fwd x' hx' hmem fun x'' heq ↦ ih x'' <| by simpa [hx']

lemma iterFindRec_true {y : σ} {C : σ → Sort u} {x : σ} (h : y ∈ iterFind f p x)
    (stop : (x : σ) → p x = true → y ∈ iterFind f p x → C x)
    (fwd : (x : σ) → p x = false → y ∈ iterFind f p x → ((x' : σ) → x' ∈ f x → C x') → C x)
    (hx : p x = true) : iterFindRec h stop fwd = stop x hx h := by
  grind [iterFindRec, fixInduction_spec]

lemma iterFindRec_false {y : σ} {C : σ → Sort u} {x : σ} (h : y ∈ iterFind f p x)
    (stop : (x : σ) → p x = true → y ∈ iterFind f p x → C x)
    (fwd : (x : σ) → p x = false → y ∈ iterFind f p x → ((x' : σ) → x' ∈ f x → C x') → C x)
    (hx : p x = false) : iterFindRec h stop fwd =
      fwd x hx h (fun x' heq ↦ iterFindRec (x := x') (by grind) stop fwd) := by
  grind [iterFindRec, fixInduction_spec]

@[grind .]
lemma iterFind_spec {x y : σ} (h : y ∈ iterFind f p x) : p y :=
  iterFindRec h (by grind) fun x hx hmem ih ↦
    ih (f.fn x (dom_of_mem_iterFind hx hmem)) (Part.get_mem _)

@[grind =]
lemma mem_iterFind_self_iff (x : σ) : x ∈ iterFind f p x ↔ p x = true :=
  ⟨iterFind_spec, iterFind_stop⟩

lemma exists_minimal_mem_iterate_of_mem_iterFind {x y : σ} (h : y ∈ iterFind f p x) :
    ∃ n, y ∈ f.iterate n x ∧ ∀ m < n, ∀ y' ∈ f.iterate m x, p y' = false := by
  refine iterFindRec h ?_ ?_
  · intro x hx hmem
    obtain rfl := eq_of_mem_iterFind_of_true hx hmem
    use 0
    simp [iterate_zero]
  · intro x hx hmem ih
    have hdom : x ∈ f.Dom := dom_of_mem_iterFind hx hmem
    obtain ⟨n, hn_mem, hmin⟩ := ih (f.fn x hdom) (Part.get_mem hdom)
    use n + 1
    constructor
    · rw [iterate_succ']
      exact PFun.mem_comp (Part.get_mem hdom) hn_mem
    · rintro (_ | m) hle y' hy'
      · simp_all [iterate_zero]
      · exact hmin m (by lia) y' (iterate_succ_apply_of_mem_dom hdom ▸ hy')

lemma exists_mem_iterate_of_mem_iterFind {x y : σ} (h : y ∈ iterFind f p x) :
    ∃ n, y ∈ f.iterate n x := by
  obtain ⟨n, hn, -⟩ := exists_minimal_mem_iterate_of_mem_iterFind h
  exact ⟨n, hn⟩

lemma mem_iterFind_apply_iff {x y : σ} :
    y ∈ iterFind f p x ↔
      p y = true ∧ ∃ n, y ∈ f.iterate n x ∧ ∀ m < n, ∀ y' ∈ f.iterate m x, p y' = false := by
  refine ⟨by grind [exists_minimal_mem_iterate_of_mem_iterFind], ?_⟩
  intro ⟨hy, n, hmem, hmin⟩
  induction n generalizing x with
  | zero => simp_all [iterate_zero, mem_iterFind_self_iff]
  | succ n ih =>
    have hdom : x ∈ f.Dom := mem_dom_of_mem_iterate_succ hmem
    rw [iterFind_fwd_eq_comp (hmin 0 (by lia) _ (Part.mem_some x))]
    refine mem_comp (Part.get_mem hdom) <| ih (iterate_succ_apply_of_mem_dom hdom ▸ hmem) ?_
    intro m hm y' hy'
    exact hmin (m + 1) (by lia) y' (iterate_succ_apply_of_mem_dom hdom ▸ hy')

end Cslib

open Function List

abbrev Function.RelEval (f : α → List β) (a : α) (b : β) : Prop := b ∈ f a

lemma List.mem_bind {α β : Type u} {l : List α} {f : α → List β} {b : β} :
    b ∈ (l >>= f) ↔ ∃ a ∈ l, b ∈ f a := by simp

namespace Relation

def Catalogues (f : α → List β) (r : α → β → Prop) := ∀ a b, b ∈ f a ↔ r a b

namespace Catalogues

variable {f : α → List β} {r : α → β → Prop}

lemma rel_of_mem (h : Catalogues f r) (hab : b ∈ f a) : r a b := (h a b).mp hab

lemma mem_of_rel (h : Catalogues f r) (hab : r a b) : b ∈ f a := (h a b).mpr hab

lemma comp {f : α → List β} {g : β → List γ} {r : α → β → Prop} {s : β → γ → Prop}
    (h : Catalogues f r) (h' : Catalogues g s) : Catalogues (f · |>.flatMap g) (Comp r s) := by
  intro a c
  simp [mem_flatMap, h a, (h' · c), Comp]

variable {f : α → List α} {r : α → α → Prop}

lemma mem_iterate_of_reflTransGen (h : Catalogues f r) (hab : ReflTransGen r a b) :
    ∃ n, b ∈ (· >>= f)^[n] [a] := by
  induction hab with
  | refl => use 0; simp
  | @tail b c _ htr ih =>
    obtain ⟨n, hn⟩ := ih
    use n + 1
    simp only [iterate_succ', comp_apply, mem_bind]
    use b, hn, h.mem_of_rel htr

lemma reflTransGen_of_mem_iterate (h : Catalogues f r) {n : ℕ} {l : List α}
    (hb : b ∈ (· >>= f)^[n] l) : ∃ a ∈ l, ReflTransGen r a b := by
  induction n generalizing l with
  | zero => use b, by simpa using hb
  | succ n ih =>
    rw [iterate_succ, comp_apply] at hb
    obtain ⟨a', ha', hrel⟩ := ih hb
    obtain ⟨a, hal, ha⟩ := mem_bind.mp ha'
    use a, hal, hrel.head (h.rel_of_mem ha)

lemma reflTransGen_iff (h : Catalogues f r) :
    ReflTransGen r a b ↔ ∃ n, b ∈ (· >>= f)^[n] [a] :=
  ⟨h.mem_iterate_of_reflTransGen, fun ⟨n, hn⟩ ↦ by simpa using h.reflTransGen_of_mem_iterate hn⟩

end Catalogues

end Relation
