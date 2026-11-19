/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Hom
public import Mathlib.Order.BooleanAlgebra.Set
public import Mathlib.Order.PrimeSeparator

@[expose] public section

universe u

namespace Cslib.RelationAlgebra

structure BoolUltrafilter (α : Type u) [BooleanAlgebra α] where
  carrier : Set α
  top_mem' : ⊤ ∈ carrier
  inf_mem' {a b : α} : a ∈ carrier → b ∈ carrier → a ⊓ b ∈ carrier
  mem_of_le' {a b : α} : a ≤ b → a ∈ carrier → b ∈ carrier
  compl_mem_iff' {a : α} : aᶜ ∈ carrier ↔ a ∉ carrier

namespace BoolUltrafilter

section BooleanAlgebra

variable {α : Type u} [BooleanAlgebra α] {F G L : BoolUltrafilter α} {a b : α}

instance : SetLike (BoolUltrafilter α) α where
  coe := carrier
  coe_injective F G h := by
    cases F
    cases G
    congr

@[ext]
theorem ext (h : ∀ a, a ∈ F ↔ a ∈ G) : F = G := SetLike.ext h

theorem top_mem (F : BoolUltrafilter α) : ⊤ ∈ F := F.top_mem'

theorem inf_mem (ha : a ∈ F) (hb : b ∈ F) : a ⊓ b ∈ F := F.inf_mem' ha hb

theorem mem_of_le (h : a ≤ b) (ha : a ∈ F) : b ∈ F := F.mem_of_le' h ha

theorem compl_mem_iff : aᶜ ∈ F ↔ a ∉ F := F.compl_mem_iff'

theorem bot_notMem (F : BoolUltrafilter α) : ⊥ ∉ F := by
  rw [← compl_mem_iff, compl_bot]
  exact F.top_mem

theorem inf_mem_iff : a ⊓ b ∈ F ↔ a ∈ F ∧ b ∈ F :=
  ⟨fun h => ⟨mem_of_le inf_le_left h, mem_of_le inf_le_right h⟩, fun h => inf_mem h.1 h.2⟩

theorem sup_mem_iff : a ⊔ b ∈ F ↔ a ∈ F ∨ b ∈ F := by
  constructor
  · intro h
    by_contra hc
    rw [not_or, ← compl_mem_iff, ← compl_mem_iff] at hc
    have hab := inf_mem hc.1 hc.2
    rw [← compl_sup, compl_mem_iff] at hab
    exact hab h
  · rintro (h | h)
    exacts [mem_of_le le_sup_left h, mem_of_le le_sup_right h]

theorem eq_of_le (h : ∀ a ∈ F, a ∈ G) : F = G := by
  ext a
  refine ⟨h a, fun ha => by_contra fun hn => ?_⟩
  exact compl_mem_iff.mp (h _ (compl_mem_iff.mpr hn)) ha

protected theorem nonempty (F : BoolUltrafilter α) : (F : Set α).Nonempty := ⟨⊤, F.top_mem⟩

protected theorem directedOn (F : BoolUltrafilter α) : DirectedOn (· ≥ ·) (F : Set α) :=
  fun _ ha _ hb => ⟨_, inf_mem ha hb, inf_le_left, inf_le_right⟩

theorem exists_of_disjoint {X : Set α} (I : Order.Ideal α) (hX : X.Nonempty)
    (hXd : DirectedOn (· ≥ ·) X) (h : ∀ x ∈ X, x ∉ I) :
    ∃ M : BoolUltrafilter α, X ⊆ M ∧ ∀ y ∈ I, y ∉ M := by
  have hF : Order.IsPFilter {y | ∃ x ∈ X, x ≤ y} := by
    refine .of_def (hX.imp fun x hx => ⟨x, hx, le_rfl⟩) ?_
      fun hxy ⟨z, hz, hzx⟩ => ⟨z, hz, hzx.trans hxy⟩
    rintro y ⟨x, hx, hxy⟩ y' ⟨x', hx', hxy'⟩
    obtain ⟨z, hz, hzx, hzx'⟩ := hXd x hx x' hx'
    exact ⟨z, ⟨z, hz, le_rfl⟩, hzx.trans hxy, hzx'.trans hxy'⟩
  have hdisj : Disjoint (hF.toPFilter : Set α) I := by
    rw [Set.disjoint_left]
    rintro y ⟨x, hx, hxy⟩ hy
    exact h x hx (I.lower hxy hy)
  obtain ⟨J, hJ, hIJ, hFJ⟩ := DistribLattice.prime_ideal_of_disjoint_filter_ideal hdisj
  refine ⟨⟨{a | a ∉ J}, hJ.toIsProper.top_notMem, fun ha hb h => (hJ.mem_or_mem h).elim ha hb,
    fun hab ha hb => ha (J.lower hab hb), ?_⟩, fun x hx => ?_, fun y hy => not_not.mpr (hIJ hy)⟩
  · exact ⟨fun h hn => hJ.mem_or_compl_mem.elim hn h,
      fun h hc => h (hJ.toIsProper.notMem_of_compl_mem hc)⟩
  · exact Set.disjoint_left.mp hFJ ⟨x, hx, le_rfl⟩

theorem exists_of_forall_mem (g : α → α → α)
    (hsup : ∀ a y y', g a (y ⊔ y') = g a y ⊔ g a y') (hmono : ∀ a a' y, a ≤ a' → g a y ≤ g a' y)
    (hbot : ∀ a, g a ⊥ = ⊥) {F X : Set α} (hF : F.Nonempty) (hFd : DirectedOn (· ≥ ·) F)
    (hX : X.Nonempty) (hXd : DirectedOn (· ≥ ·) X) (h : ∀ a ∈ F, ∀ x ∈ X, g a x ∈ L) :
    ∃ M : BoolUltrafilter α, X ⊆ M ∧ ∀ a ∈ F, ∀ m ∈ M, g a m ∈ L := by
  have hmono' : ∀ a y y', y ≤ y' → g a y ≤ g a y' := fun a y y' hy => by
    rw [← sup_eq_right.mpr hy, hsup]
    exact le_sup_left
  have hI : Order.IsIdeal {y | ∃ a ∈ F, g a y ∉ L} := by
    refine ⟨fun y y' hy ⟨a, ha, hay⟩ => ⟨a, ha, fun h => hay (mem_of_le (hmono' a y' y hy) h)⟩,
      ?_, ?_⟩
    · obtain ⟨a, ha⟩ := hF
      exact ⟨⊥, a, ha, by rw [hbot]; exact L.bot_notMem⟩
    · rintro y ⟨a, ha, hay⟩ y' ⟨a', ha', hay'⟩
      obtain ⟨c, hc, hca, hca'⟩ := hFd a ha a' ha'
      refine ⟨y ⊔ y', ⟨c, hc, ?_⟩, le_sup_left, le_sup_right⟩
      rw [hsup, sup_mem_iff]
      rintro (h | h)
      exacts [hay (mem_of_le (hmono c a y hca) h), hay' (mem_of_le (hmono c a' y' hca') h)]
  obtain ⟨M, hXM, hM⟩ :=
    exists_of_disjoint hI.toIdeal hX hXd fun x hx ⟨a, ha, hax⟩ => hax (h a ha x hx)
  exact ⟨M, hXM, fun a ha m hm => by_contra fun hn => hM m ⟨a, ha, hn⟩ hm⟩

theorem exists_mem_of_ne_bot (h : a ≠ ⊥) : ∃ F : BoolUltrafilter α, a ∈ F := by
  obtain ⟨F, hF, -⟩ := exists_of_disjoint (X := {a}) (Order.Ideal.principal ⊥)
    (Set.singleton_nonempty a) (directedOn_singleton a)
    fun x hx hx' => h (le_bot_iff.mp (hx ▸ Order.Ideal.mem_principal.mp hx'))
  exact ⟨F, hF rfl⟩

end BooleanAlgebra

section NonAssoc

variable {α : Type u} [NonAssocRelationAlgebra α] {F G H E L : BoolUltrafilter α} {a b : α}

instance : Star (BoolUltrafilter α) where
  star F :=
    { carrier := {a | star a ∈ F}
      top_mem' := by simpa using F.top_mem
      inf_mem' := fun ha hb => by simpa using inf_mem ha hb
      mem_of_le' := fun h ha => mem_of_le (star_mono h) ha
      compl_mem_iff' := by simp [compl_mem_iff] }

@[simp]
theorem mem_star : a ∈ star F ↔ star a ∈ F := .rfl

instance : InvolutiveStar (BoolUltrafilter α) where
  star_involutive F := by
    ext
    simp

def Cycle (F G H : BoolUltrafilter α) : Prop := ∀ a ∈ F, ∀ b ∈ G, a * b ∈ H

theorem exists_right {F X : Set α} (hF : F.Nonempty) (hFd : DirectedOn (· ≥ ·) F)
    (hX : X.Nonempty) (hXd : DirectedOn (· ≥ ·) X) (h : ∀ a ∈ F, ∀ x ∈ X, a * x ∈ L) :
    ∃ M : BoolUltrafilter α, X ⊆ M ∧ ∀ a ∈ F, ∀ m ∈ M, a * m ∈ L :=
  exists_of_forall_mem (· * ·) mul_sup (fun _ _ y h => mul_le_mul_left h y) mul_bot hF hFd hX hXd h

theorem exists_left {G X : Set α} (hG : G.Nonempty) (hGd : DirectedOn (· ≥ ·) G)
    (hX : X.Nonempty) (hXd : DirectedOn (· ≥ ·) X) (h : ∀ x ∈ X, ∀ b ∈ G, x * b ∈ L) :
    ∃ M : BoolUltrafilter α, X ⊆ M ∧ ∀ m ∈ M, ∀ b ∈ G, m * b ∈ L := by
  have hbot (b : α) : ⊥ * b = ⊥ := star_injective (by simp)
  obtain ⟨M, hXM, hM⟩ := exists_of_forall_mem (fun b x => x * b) (fun b y y' => sup_mul y y' b)
    (fun _ _ y h => mul_le_mul_right h y) hbot hG hGd hX hXd fun b hb x hx => h x hx b hb
  exact ⟨M, hXM, fun m hm b hb => hM b hb m hm⟩

theorem directedOn_image2_mul (F G : BoolUltrafilter α) :
    DirectedOn (· ≥ ·) (Set.image2 (· * ·) (F : Set α) G) := by
  rintro _ ⟨a, ha, b, hb, rfl⟩ _ ⟨a', ha', b', hb', rfl⟩
  exact ⟨_, ⟨_, inf_mem ha ha', _, inf_mem hb hb', rfl⟩,
    mul_le_mul' inf_le_left inf_le_left, mul_le_mul' inf_le_right inf_le_right⟩

theorem exists_cycle_right {X : Set α} (hX : X.Nonempty) (hXd : DirectedOn (· ≥ ·) X)
    (h : ∀ a ∈ F, ∀ x ∈ X, a * x ∈ L) : ∃ M : BoolUltrafilter α, X ⊆ M ∧ Cycle F M L :=
  exists_right F.nonempty F.directedOn hX hXd h

theorem exists_cycle_left {X : Set α} (hX : X.Nonempty) (hXd : DirectedOn (· ≥ ·) X)
    (h : ∀ x ∈ X, ∀ b ∈ G, x * b ∈ L) : ∃ M : BoolUltrafilter α, X ⊆ M ∧ Cycle M G L :=
  exists_left G.nonempty G.directedOn hX hXd h

theorem exists_cycle_of_mul_mem (h : a * b ∈ H) :
    ∃ F G : BoolUltrafilter α, a ∈ F ∧ b ∈ G ∧ Cycle F G H := by
  obtain ⟨F, hF, hFb⟩ := exists_left (L := H) (G := {b}) (X := {a}) (Set.singleton_nonempty b)
    (directedOn_singleton b) (Set.singleton_nonempty a) (directedOn_singleton a)
    fun x hx y hy => by rwa [hx, hy]
  obtain ⟨G, hG, hFG⟩ := exists_cycle_right (F := F) (L := H) (X := {b})
    (Set.singleton_nonempty b) (directedOn_singleton b) fun x hx y hy => hFb x hx y hy
  exact ⟨F, G, hF rfl, hG rfl, hFG⟩

namespace Cycle

theorem eq_of_one_mem_right (hE : 1 ∈ E) (h : Cycle F E G) : F = G :=
  eq_of_le fun a ha => by simpa using h a ha 1 hE

theorem eq_of_one_mem_left (hE : 1 ∈ E) (h : Cycle E F G) : F = G :=
  eq_of_le fun a ha => by simpa using h 1 hE a ha

protected theorem star (h : Cycle F G H) : Cycle (star G) (star F) (star H) := by
  intro b hb a ha
  rw [mem_star, star_mul]
  exact h _ ha _ hb

theorem star_left (h : Cycle F G H) : Cycle (star F) H G := by
  intro a ha c hc
  by_contra hn
  have hH := mem_of_le (tarski a c) (h (star a) ha _ (compl_mem_iff.mpr hn))
  exact compl_mem_iff.mp hH hc

end Cycle

theorem exists_cycle_one_right (F : BoolUltrafilter α) : ∃ E, 1 ∈ E ∧ Cycle F E F := by
  obtain ⟨E, hE, h⟩ := exists_cycle_right (F := F) (L := F) (X := {1}) (Set.singleton_nonempty 1)
    (directedOn_singleton 1) fun a ha x hx => by rwa [hx, mul_one]
  exact ⟨E, hE rfl, h⟩

theorem exists_cycle_one_left (F : BoolUltrafilter α) : ∃ E, 1 ∈ E ∧ Cycle E F F := by
  obtain ⟨E, hE, h⟩ := exists_cycle_left (G := F) (L := F) (X := {1}) (Set.singleton_nonempty 1)
    (directedOn_singleton 1) fun x hx b hb => by rwa [hx, one_mul]
  exact ⟨E, hE rfl, h⟩

end NonAssoc

end BoolUltrafilter

structure CanonicalExtension (α : Type u) [NonAssocRelationAlgebra α] where
  carrier : Set (BoolUltrafilter α)

namespace CanonicalExtension

open BoolUltrafilter

variable {α : Type u}

section NonAssoc

variable [NonAssocRelationAlgebra α]

variable (α) in
def equivSet : CanonicalExtension α ≃ Set (BoolUltrafilter α) where
  toFun := carrier
  invFun := mk
  left_inv _ := rfl
  right_inv _ := rfl

instance : SetLike (CanonicalExtension α) (BoolUltrafilter α) where
  coe := carrier
  coe_injective := (equivSet α).injective

instance : CompleteAtomicBooleanAlgebra (CanonicalExtension α) :=
  (equivSet α).completeAtomicBooleanAlgebra

instance : IsConcreteLE (CanonicalExtension α) (BoolUltrafilter α) where
  le_iff := .rfl

instance : One (CanonicalExtension α) where
  one := ⟨{F | 1 ∈ F}⟩

instance : Mul (CanonicalExtension α) where
  mul x y := ⟨{H | ∃ F ∈ x, ∃ G ∈ y, Cycle F G H}⟩

instance : Star (CanonicalExtension α) where
  star x := ⟨{F | star F ∈ x}⟩

variable {x y : CanonicalExtension α} {F H : BoolUltrafilter α}

@[ext]
theorem ext (h : ∀ F, F ∈ x ↔ F ∈ y) : x = y := SetLike.ext h

@[simp]
theorem mem_mk {s : Set (BoolUltrafilter α)} : F ∈ (⟨s⟩ : CanonicalExtension α) ↔ F ∈ s := .rfl

@[simp]
theorem mem_sup : F ∈ x ⊔ y ↔ F ∈ x ∨ F ∈ y := .rfl

@[simp]
theorem mem_inf : F ∈ x ⊓ y ↔ F ∈ x ∧ F ∈ y := .rfl

@[simp]
theorem mem_compl : F ∈ xᶜ ↔ F ∉ x := .rfl

@[simp]
theorem mem_top : F ∈ (⊤ : CanonicalExtension α) := trivial

@[simp]
theorem notMem_bot : F ∉ (⊥ : CanonicalExtension α) := id

@[simp]
theorem mem_one : F ∈ (1 : CanonicalExtension α) ↔ 1 ∈ F := .rfl

theorem mem_mul : H ∈ x * y ↔ ∃ F ∈ x, ∃ G ∈ y, Cycle F G H := .rfl

@[simp]
theorem mem_star : F ∈ star x ↔ star F ∈ x := .rfl

instance : NonAssocRelationAlgebra (CanonicalExtension α) where
  one_mul x := by
    ext H
    constructor
    · rintro ⟨E, hE, G, hG, h⟩
      exact h.eq_of_one_mem_left hE ▸ hG
    · intro hH
      obtain ⟨E, hE, h⟩ := exists_cycle_one_left H
      exact ⟨E, hE, H, hH, h⟩
  mul_one x := by
    ext H
    constructor
    · rintro ⟨G, hG, E, hE, h⟩
      exact h.eq_of_one_mem_right hE ▸ hG
    · intro hH
      obtain ⟨E, hE, h⟩ := exists_cycle_one_right H
      exact ⟨H, hH, E, hE, h⟩
  star_involutive x := by
    ext
    simp
  star_mul x y := by
    ext H
    constructor
    · rintro ⟨F, hF, G, hG, h⟩
      exact ⟨star G, by simpa using hG, star F, by simpa using hF, by simpa using h.star⟩
    · rintro ⟨G, hG, F, hF, h⟩
      exact ⟨star F, hF, star G, hG, h.star⟩
  sup_mul x y z := by
    ext H
    simp only [mem_mul, mem_sup]
    grind
  star_sup x y := by
    ext
    simp
  tarski x y := by
    rintro H ⟨F, hF, G, hG, h⟩ hH
    exact hG ⟨star F, hF, H, hH, h.star_left⟩

end NonAssoc

instance [SemiAssocRelationAlgebra α] : SemiAssocRelationAlgebra (CanonicalExtension α) where
  mul_assoc_top x y := by
    ext L
    constructor
    · rintro ⟨H, ⟨F, hF, G, hG, hFGH⟩, K, -, hHKL⟩
      obtain ⟨M, hM, hFML⟩ := exists_cycle_right (F := F) (L := L)
        (X := Set.image2 (· * ·) (G : Set α) {⊤}) (G.nonempty.image2 (Set.singleton_nonempty ⊤))
        (by
          rintro _ ⟨b, hb, _, rfl, rfl⟩ _ ⟨b', hb', _, rfl, rfl⟩
          exact ⟨_, ⟨_, inf_mem hb hb', _, rfl, rfl⟩,
            mul_le_mul_left inf_le_left ⊤, mul_le_mul_left inf_le_right ⊤⟩)
        (by
          rintro a ha _ ⟨b, hb, _, rfl, rfl⟩
          rw [← mul_assoc_top]
          exact hHKL _ (hFGH a ha b hb) ⊤ K.top_mem)
      obtain ⟨K', -, hGK'M⟩ := exists_cycle_right (F := G) (L := M) (X := {⊤})
        (Set.singleton_nonempty ⊤) (directedOn_singleton ⊤)
        fun b hb _ hx => hM ⟨b, hb, _, hx, rfl⟩
      exact ⟨F, hF, M, ⟨G, hG, K', mem_top, hGK'M⟩, hFML⟩
    · rintro ⟨F, hF, M, ⟨G, hG, K, -, hGKM⟩, hFML⟩
      obtain ⟨H, hH, hHL⟩ := exists_left (L := L) (G := {⊤})
        (X := Set.image2 (· * ·) (F : Set α) G) (Set.singleton_nonempty ⊤)
        (directedOn_singleton ⊤) (F.nonempty.image2 G.nonempty) (directedOn_image2_mul F G)
        (by
          rintro _ ⟨a, ha, b, hb, rfl⟩ _ rfl
          rw [mul_assoc_top]
          exact hFML a ha _ (hGKM b hb ⊤ K.top_mem))
      obtain ⟨K', -, hHK'L⟩ := exists_cycle_right (F := H) (L := L) (X := {⊤})
        (Set.singleton_nonempty ⊤) (directedOn_singleton ⊤) fun h hh x hx => hHL h hh x hx
      exact ⟨H, ⟨F, hF, G, hG, fun a ha b hb => hH ⟨a, ha, b, hb, rfl⟩⟩, K', mem_top, hHK'L⟩

instance [RelationAlgebra α] : RelationAlgebra (CanonicalExtension α) where
  mul_assoc x y z := by
    ext L
    constructor
    · rintro ⟨H, ⟨F, hF, G, hG, hFGH⟩, K, hK, hHKL⟩
      obtain ⟨M, hM, hFML⟩ := exists_cycle_right (F := F) (L := L)
        (X := Set.image2 (· * ·) (G : Set α) K) (G.nonempty.image2 K.nonempty)
        (directedOn_image2_mul G K)
        (by
          rintro a ha _ ⟨b, hb, c, hc, rfl⟩
          rw [← mul_assoc]
          exact hHKL _ (hFGH a ha b hb) c hc)
      exact ⟨F, hF, M, ⟨G, hG, K, hK, fun b hb c hc => hM ⟨b, hb, c, hc, rfl⟩⟩, hFML⟩
    · rintro ⟨F, hF, M, ⟨G, hG, K, hK, hGKM⟩, hFML⟩
      obtain ⟨H, hH, hHKL⟩ := exists_cycle_left (G := K) (L := L)
        (X := Set.image2 (· * ·) (F : Set α) G) (F.nonempty.image2 G.nonempty)
        (directedOn_image2_mul F G)
        (by
          rintro _ ⟨a, ha, b, hb, rfl⟩ c hc
          rw [mul_assoc]
          exact hFML a ha _ (hGKM b hb c hc))
      exact ⟨H, ⟨F, hF, G, hG, fun a ha b hb => hH ⟨a, ha, b, hb, rfl⟩⟩, K, hK, hHKL⟩

end CanonicalExtension

open BoolUltrafilter in
def canonicalEmbedding (α : Type u) [NonAssocRelationAlgebra α] :
    RelationAlgebraHom α (CanonicalExtension α) where
  toFun a := ⟨{F | a ∈ F}⟩
  map_sup' a b := by
    ext F
    exact sup_mem_iff
  map_inf' a b := by
    ext F
    exact inf_mem_iff
  map_top' := by
    ext F
    simpa using F.top_mem
  map_bot' := by
    ext F
    simpa using F.bot_notMem
  map_one' := rfl
  map_mul' a b := by
    ext H
    constructor
    · intro h
      obtain ⟨F, G, ha, hb, hc⟩ := exists_cycle_of_mul_mem h
      exact ⟨F, ha, G, hb, hc⟩
    · rintro ⟨F, ha, G, hb, h⟩
      exact h a ha b hb
  map_star' a := rfl

variable {α : Type u} [NonAssocRelationAlgebra α]

@[simp]
theorem mem_canonicalEmbedding {a : α} {F : BoolUltrafilter α} :
    F ∈ canonicalEmbedding α a ↔ a ∈ F := .rfl

theorem canonicalEmbedding_injective : Function.Injective (canonicalEmbedding α) := by
  have key : ∀ a b : α, canonicalEmbedding α a = canonicalEmbedding α b → a ≤ b := by
    intro a b hab
    by_contra hle
    obtain ⟨F, hF⟩ := BoolUltrafilter.exists_mem_of_ne_bot
      (a := a ⊓ bᶜ) fun h => hle (disjoint_compl_right_iff.mp (disjoint_iff.mpr h))
    rw [BoolUltrafilter.inf_mem_iff, BoolUltrafilter.compl_mem_iff] at hF
    exact hF.2 (mem_canonicalEmbedding.mp (hab ▸ mem_canonicalEmbedding.mpr hF.1))
  exact fun a b hab => le_antisymm (key a b hab) (key b a hab.symm)

end Cslib.RelationAlgebra
