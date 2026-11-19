/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Dimensional.SetRel
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Max
public import Mathlib.Order.Filter.Ultrafilter.Basic

@[expose] public section

universe u

namespace Cslib.RelationAlgebra

namespace RelationalBasis

inductive Node (β : Type u) : Type u where
  | left
  | right
  | wit (u v : Node β) (a b : β)

variable {β : Type u}

namespace Node

def depth : Node β → ℕ
  | left => 0
  | right => 0
  | wit u v _ _ => max u.depth v.depth + 1

theorem depth_lt_depth_wit_left (u v : Node β) (a b : β) : u.depth < (wit u v a b).depth :=
  Nat.lt_succ_of_le (le_max_left _ _)

theorem depth_lt_depth_wit_right (u v : Node β) (a b : β) : v.depth < (wit u v a b).depth :=
  Nat.lt_succ_of_le (le_max_right _ _)

end Node

abbrev Requirement (β : Type u) := Node β × Node β × β × β

namespace Requirement

def wit (r : Requirement β) : Node β := .wit r.1 r.2.1 r.2.2.1 r.2.2.2

theorem wit_injective : Function.Injective (wit : Requirement β → Node β) := by
  rintro ⟨u, v, a, b⟩ ⟨u', v', a', b'⟩ h
  simpa [wit] using h

theorem fst_ne_wit (r r' : Requirement β) (h : r.wit.depth ≤ r'.wit.depth) : r.1 ≠ r'.wit :=
  fun h' => absurd (h' ▸ Node.depth_lt_depth_wit_left r.1 r.2.1 r.2.2.1 r.2.2.2) (not_lt.mpr h)

theorem snd_ne_wit (r r' : Requirement β) (h : r.wit.depth ≤ r'.wit.depth) : r.2.1 ≠ r'.wit :=
  fun h' => absurd (h' ▸ Node.depth_lt_depth_wit_right r.1 r.2.1 r.2.2.1 r.2.2.2) (not_lt.mpr h)

end Requirement

variable [NonAssocRelationAlgebra β] (B : Set (ℕ → ℕ → β))

abbrev Network := {m : ℕ → ℕ → β // m ∈ B} × (Node β → ℕ)

variable {B}

def Network.label (c : Network B) (u v : Node β) : β := c.1.1 (c.2 u) (c.2 v)

variable (B)

def initial (p₀ : β) : Set (Network B) := {c | c.label .left .right = p₀}

def saturated (r : Requirement β) : Set (Network B) :=
  {c | c.label r.1 r.2.1 ≤ r.2.2.1 * r.2.2.2 →
    c.label r.1 r.wit ≤ r.2.2.1 ∧ c.label r.wit r.2.1 ≤ r.2.2.2}

variable {B}

theorem exists_mem_initial_forall_mem_saturated [IsAtomic β] (hB : IsRelationalBasis B) {p₀ : β}
    (hp₀ : IsAtom p₀) (R : Finset (Requirement β)) :
    ∃ c : Network B, c ∈ initial B p₀ ∧ ∀ r ∈ R, c ∈ saturated B r := by
  classical
  refine Finset.induction_on_max_value (fun r : Requirement β => r.wit.depth) R ?_ ?_
  · obtain ⟨m, hm, i, j, -, hij⟩ := hB.exists_apply_eq hp₀
    exact ⟨(⟨m, hm⟩, fun x => match x with | .left => i | _ => j), hij, by simp⟩
  intro r R hr hmax ⟨⟨⟨m, hm⟩, f⟩, h₀, hR⟩
  by_cases hle : m (f r.1) (f r.2.1) ≤ r.2.2.1 * r.2.2.2
  swap
  · refine ⟨(⟨m, hm⟩, f), h₀, fun r' hr' => ?_⟩
    rcases Finset.mem_insert.mp hr' with rfl | hr'
    · exact fun h => absurd h hle
    · exact hR r' hr'
  have hatom := (hB.isBasicMatrix hm).isAtom (f r.1) (f r.2.1)
  obtain ⟨a', ha', ha'a, h₁⟩ := exists_atom_le_mul_left hatom hle
  obtain ⟨b', hb', hb'b, h₂⟩ := exists_atom_le_mul_right hatom h₁
  -- an index that is not used by any node mentioned so far
  obtain ⟨k, hkl, hkr, hku, hkv, hkR⟩ : ∃ k, f .left < k ∧ f .right < k ∧ f r.1 < k ∧
      f r.2.1 < k ∧ ∀ r' ∈ R, f r'.1 < k ∧ f r'.2.1 < k ∧ f r'.wit < k := by
    refine ⟨1 + f .left + f .right + f r.1 + f r.2.1 + ∑ r' ∈ R, (f r'.1 + f r'.2.1 + f r'.wit),
      by omega, by omega, by omega, by omega, fun r' hr' => ?_⟩
    have := Finset.single_le_sum (f := fun r' : Requirement β => f r'.1 + f r'.2.1 + f r'.wit)
      (fun _ _ => Nat.zero_le _) hr'
    omega
  obtain ⟨m', hm', e₁, e₂, hag⟩ := hB.exists_apply_eq_apply_eq hm (k := k) hku.ne hkv.ne ha' hb' h₂
  have key : ∀ x y : Node β, x ≠ r.wit → y ≠ r.wit → f x < k → f y < k →
      Network.label (B := B) (⟨m', hm'⟩, Function.update f r.wit k) x y = m (f x) (f y) := by
    intro x y hx hy hfx hfy
    simp only [Network.label, Function.update_of_ne hx, Function.update_of_ne hy]
    exact (hag _ _ hfx.ne' hfy.ne').symm
  have hu := r.fst_ne_wit r le_rfl
  have hv := r.snd_ne_wit r le_rfl
  refine ⟨(⟨m', hm'⟩, Function.update f r.wit k), ?_, fun r' hr' => ?_⟩
  · exact (key _ _ (by simp [Requirement.wit]) (by simp [Requirement.wit]) hkl hkr).trans h₀
  · rcases Finset.mem_insert.mp hr' with rfl | hr'
    · intro _
      simp only [Network.label, Function.update_of_ne hu, Function.update_of_ne hv,
        Function.update_self, e₁, e₂]
      exact ⟨ha'a, hb'b⟩
    · have hne : r'.wit ≠ r.wit := fun h => hr (Requirement.wit_injective h ▸ hr')
      have hu' := r'.fst_ne_wit r (hmax r' hr')
      have hv' := r'.snd_ne_wit r (hmax r' hr')
      obtain ⟨hku', hkv', hkw'⟩ := hkR r' hr'
      have := hR r' hr'
      simp only [saturated, Set.mem_ofPred_eq, key _ _ hu' hv' hku' hkv',
        key _ _ hu' hne hku' hkw', key _ _ hne hv' hkw' hkv'] at this ⊢
      exact this

theorem exists_ultrafilter [IsAtomic β] (hB : IsRelationalBasis B) {p₀ : β} (hp₀ : IsAtom p₀) :
    ∃ 𝒰 : Ultrafilter (Network B), initial B p₀ ∈ 𝒰 ∧ ∀ r, saturated B r ∈ 𝒰 := by
  classical
  obtain ⟨𝒰, h𝒰⟩ := Ultrafilter.exists_ultrafilter_of_finite_inter_nonempty
    (insert (initial B p₀) (Set.range (saturated B))) fun T hT => by
      have h : ∀ s : Set (Network B), ∃ r : Requirement β,
          s ∈ T → s = initial B p₀ ∨ s = saturated B r := by
        intro s
        by_cases hs : s ∈ T
        · rcases hT hs with rfl | ⟨r, rfl⟩
          · exact ⟨(.left, .left, p₀, p₀), fun _ => .inl rfl⟩
          · exact ⟨r, fun _ => .inr rfl⟩
        · exact ⟨(.left, .left, p₀, p₀), fun h => absurd h hs⟩
      choose g hg using h
      obtain ⟨c, hc₀, hc⟩ := exists_mem_initial_forall_mem_saturated hB hp₀ (T.image g)
      refine ⟨c, Set.mem_sInter.mpr fun s hs => ?_⟩
      rcases hg s hs with rfl | h
      · exact hc₀
      · exact h ▸ hc (g s) (Finset.mem_image_of_mem g hs)
  exact ⟨𝒰, h𝒰 (Set.mem_insert _ _), fun r => h𝒰 (Set.mem_insert_of_mem _ ⟨r, rfl⟩)⟩

section Label

variable (hB : IsRelationalBasis B) (c : Network B) (u v w : Node β)

include hB

theorem isAtom_label : IsAtom (c.label u v) := (hB.isBasicMatrix c.1.2).isAtom _ _

theorem label_self_le_one : c.label u u ≤ 1 := (hB.isBasicMatrix c.1.2).le_one _

theorem star_label : star (c.label u v) = c.label v u := (hB.isBasicMatrix c.1.2).star_apply _ _

theorem label_le_mul : c.label u w ≤ c.label u v * c.label v w :=
  (hB.isBasicMatrix c.1.2).le_mul _ _ _

end Label

theorem _root_.IsAtom.le_sup_iff_of_booleanAlgebra {α : Type*} [BooleanAlgebra α] {a x y : α}
    (ha : IsAtom a) : a ≤ x ⊔ y ↔ a ≤ x ∨ a ≤ y := by
  refine ⟨fun h => ?_, fun h => h.elim le_sup_of_le_left le_sup_of_le_right⟩
  by_contra hxy
  rw [not_or, ha.not_le_iff_disjoint, ha.not_le_iff_disjoint] at hxy
  exact ha.not_le_iff_disjoint.mpr (disjoint_sup_right.mpr hxy) h

def Holds (𝒰 : Ultrafilter (Network B)) (e : β) (u v : Node β) : Prop :=
  ∀ᶠ c in (𝒰 : Filter (Network B)), c.label u v ≤ e

section Holds

variable (hB : IsRelationalBasis B) {𝒰 : Ultrafilter (Network B)} {x y e : β} {u v w u' v' : Node β}

theorem Holds.mono (h : Holds 𝒰 x u v) (hxy : x ≤ y) : Holds 𝒰 y u v :=
  Filter.Eventually.mono h fun _ hc => hc.trans hxy

theorem holds_inf : Holds 𝒰 (x ⊓ y) u v ↔ Holds 𝒰 x u v ∧ Holds 𝒰 y u v := by
  simp only [Holds, le_inf_iff, Filter.eventually_and]

theorem holds_top : Holds 𝒰 ⊤ u v := Filter.Eventually.of_forall fun _ => le_top

include hB

theorem holds_sup : Holds 𝒰 (x ⊔ y) u v ↔ Holds 𝒰 x u v ∨ Holds 𝒰 y u v := by
  simp only [Holds, (isAtom_label hB _ u v).le_sup_iff_of_booleanAlgebra,
    Ultrafilter.eventually_or]

theorem not_holds_bot : ¬ Holds 𝒰 ⊥ u v := fun h =>
  let ⟨c, hc⟩ := h.exists
  (isAtom_label hB c u v).ne_bot (le_bot_iff.mp hc)

theorem holds_star : Holds 𝒰 (star e) u v ↔ Holds 𝒰 e v u := by
  simp only [Holds, le_star_iff, star_label hB]

theorem holds_one_self : Holds 𝒰 1 u u :=
  Filter.Eventually.of_forall fun c => label_self_le_one hB c u

theorem Holds.mul (h₁ : Holds 𝒰 x u v) (h₂ : Holds 𝒰 y v w) : Holds 𝒰 (x * y) u w := by
  filter_upwards [h₁, h₂] with c h₁ h₂
  exact (label_le_mul hB c u v w).trans (mul_le_mul' h₁ h₂)

theorem Holds.symm (h : Holds 𝒰 1 u v) : Holds 𝒰 1 v u :=
  (holds_star hB).mp (by rwa [star_one])

theorem Holds.trans (h₁ : Holds 𝒰 1 u v) (h₂ : Holds 𝒰 1 v w) : Holds 𝒰 1 u w :=
  mul_one (1 : β) ▸ h₁.mul hB h₂

theorem Holds.congr (h : Holds 𝒰 e u v) (hu : Holds 𝒰 1 u' u) (hv : Holds 𝒰 1 v v') :
    Holds 𝒰 e u' v' := by
  simpa using (hu.mul hB h).mul hB hv

omit hB in
theorem Holds.exists_of_mul (h𝒰 : ∀ r, saturated B r ∈ 𝒰) (h : Holds 𝒰 (x * y) u v) :
    ∃ w, Holds 𝒰 x u w ∧ Holds 𝒰 y w v := by
  refine ⟨.wit u v x y, ?_, ?_⟩
  · filter_upwards [h, h𝒰 (u, v, x, y)] with c hc hs using (hs hc).1
  · filter_upwards [h, h𝒰 (u, v, x, y)] with c hc hs using (hs hc).2

end Holds

def setoid (hB : IsRelationalBasis B) (𝒰 : Ultrafilter (Network B)) : Setoid (Node β) where
  r := Holds 𝒰 1
  iseqv := ⟨fun _ => holds_one_self hB, Holds.symm hB, Holds.trans hB⟩

def quotientRel (hB : IsRelationalBasis B) (𝒰 : Ultrafilter (Network B)) (e : β) :
    SetRel (Quotient (setoid hB 𝒰)) (Quotient (setoid hB 𝒰)) :=
  {q | ∃ u v, Quotient.mk _ u = q.1 ∧ Quotient.mk _ v = q.2 ∧ Holds 𝒰 e u v}

theorem mk_mem_quotientRel (hB : IsRelationalBasis B) {𝒰 : Ultrafilter (Network B)} {e : β}
    {u v : Node β} :
    (Quotient.mk (setoid hB 𝒰) u, Quotient.mk (setoid hB 𝒰) v) ∈ quotientRel hB 𝒰 e ↔
      Holds 𝒰 e u v := by
  refine ⟨fun ⟨u', v', hu, hv, h⟩ => ?_, fun h => ⟨u, v, rfl, rfl, h⟩⟩
  exact h.congr hB (Holds.symm hB (Quotient.exact hu)) (Quotient.exact hv)

def hom (hB : IsRelationalBasis B) (𝒰 : Ultrafilter (Network B))
    (h𝒰 : ∀ r, saturated B r ∈ 𝒰) :
    RelationAlgebraHom β (SetRel (Quotient (setoid hB 𝒰)) (Quotient (setoid hB 𝒰))) where
  toFun := quotientRel hB 𝒰
  map_sup' x y := by
    ext ⟨q₁, q₂⟩
    induction q₁ using Quotient.ind
    induction q₂ using Quotient.ind
    simp [mk_mem_quotientRel, holds_sup hB]
  map_inf' x y := by
    ext ⟨q₁, q₂⟩
    induction q₁ using Quotient.ind
    induction q₂ using Quotient.ind
    simp [mk_mem_quotientRel, holds_inf]
  map_top' := by
    ext ⟨q₁, q₂⟩
    induction q₁ using Quotient.ind
    induction q₂ using Quotient.ind
    simp [mk_mem_quotientRel, holds_top]
  map_bot' := by
    ext ⟨q₁, q₂⟩
    induction q₁ using Quotient.ind
    induction q₂ using Quotient.ind
    simp [mk_mem_quotientRel, not_holds_bot hB]
  map_one' := by
    ext ⟨q₁, q₂⟩
    induction q₁ using Quotient.ind
    induction q₂ using Quotient.ind
    rw [mk_mem_quotientRel, SetRel.mem_one, Quotient.eq]
    rfl
  map_mul' x y := by
    ext ⟨q₁, q₂⟩
    induction q₁ using Quotient.ind
    induction q₂ using Quotient.ind
    rw [mk_mem_quotientRel, SetRel.mem_mul]
    constructor
    · intro h
      obtain ⟨w, h₁, h₂⟩ := h.exists_of_mul h𝒰
      exact ⟨Quotient.mk _ w, mk_mem_quotientRel hB |>.mpr h₁, mk_mem_quotientRel hB |>.mpr h₂⟩
    · rintro ⟨q, h₁, h₂⟩
      induction q using Quotient.ind
      rw [mk_mem_quotientRel] at h₁ h₂
      exact h₁.mul hB h₂
  map_star' e := by
    ext ⟨q₁, q₂⟩
    induction q₁ using Quotient.ind
    induction q₂ using Quotient.ind
    rw [SetRel.mem_star, mk_mem_quotientRel, mk_mem_quotientRel, holds_star hB]

theorem mk_mem_hom (hB : IsRelationalBasis B) {𝒰 : Ultrafilter (Network B)}
    (h𝒰 : ∀ r, saturated B r ∈ 𝒰) {e : β} {u v : Node β} :
    (Quotient.mk (setoid hB 𝒰) u, Quotient.mk (setoid hB 𝒰) v) ∈ hom hB 𝒰 h𝒰 e ↔
      Holds 𝒰 e u v :=
  mk_mem_quotientRel hB

end RelationalBasis

open RelationalBasis in
theorem Dimensional.representable {α : Type u} [RelationAlgebra α] (h : Dimensional α ℕ) :
    Representable α := by
  obtain ⟨β, _, f, hf, _, B, hB⟩ := h
  choose 𝒰 h₀ h𝒰 using fun p : {p : β // IsAtom p} => exists_ultrafilter hB p.2
  let g (p : {p : β // IsAtom p}) := hom hB (𝒰 p) (h𝒰 p)
  -- the homomorphisms `g p` separate the elements of `β`
  have hle : ∀ x y : β, (∀ p, g p x = g p y) → x ≤ y := by
    intro x y hxy
    by_contra hne
    obtain ⟨p, hp, hpxy⟩ := (eq_bot_or_exists_atom_le (x \ y)).resolve_left
      (mt sdiff_eq_bot_iff.mp hne)
    have hmem : (Quotient.mk _ .left, Quotient.mk _ .right) ∈ g ⟨p, hp⟩ p :=
      (mk_mem_hom hB (h𝒰 ⟨p, hp⟩)).mpr (Filter.Eventually.mono (h₀ ⟨p, hp⟩) fun _ hc => hc.le)
    have hx : g ⟨p, hp⟩ p ≤ g ⟨p, hp⟩ x := OrderHomClass.mono _ (hpxy.trans sdiff_le)
    have hy : g ⟨p, hp⟩ p ⊓ g ⟨p, hp⟩ y = ⊥ := by
      rw [← map_inf, (disjoint_sdiff_self_left.mono_left hpxy).eq_bot, map_bot]
    exact (hy.le ⟨hmem, hxy ⟨p, hp⟩ ▸ hx hmem⟩ : _)
  refine ⟨{p : β // IsAtom p}, fun p => Quotient (setoid hB (𝒰 p)),
    ⟨⟨(RelationAlgebraHom.pi g).comp f, fun a b hab => hf ?_⟩⟩⟩
  have hpi : ∀ p, g p (f a) = g p (f b) := fun p => congrFun hab p
  exact le_antisymm (hle _ _ hpi) (hle _ _ fun p => (hpi p).symm)

theorem dimensional_nat_iff_representable {α : Type u} [RelationAlgebra α] :
    Dimensional α ℕ ↔ Representable α :=
  ⟨Dimensional.representable, Representable.dimensional⟩

theorem ra_top_iff_representable {α : Type u} [RelationAlgebra α] : RA α ⊤ ↔ Representable α :=
  ra_top_iff.trans dimensional_nat_iff_representable

end Cslib.RelationAlgebra
