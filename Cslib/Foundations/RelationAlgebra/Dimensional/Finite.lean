/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.CanonicalExtension
public import Cslib.Foundations.RelationAlgebra.RelationalBasis

@[expose] public section

universe u v

namespace Cslib.RelationAlgebra

section NonAssoc

variable {α : Type u} [NonAssocRelationAlgebra α] {ι : Type v}

theorem star_eq_self_of_le_one {e : α} (he : e ≤ 1) : star e = e := by
  have key : ∀ {x : α}, x ≤ 1 → x ≤ star x := fun {x} hx => calc
    x = x * 1 ⊓ 1 := by rw [mul_one, inf_eq_left.mpr hx]
    _ ≤ x * (1 ⊓ star x * 1) := left_modular x 1 1
    _ ≤ 1 * (1 ⊓ star x * 1) := mul_le_mul_left hx _
    _ = 1 ⊓ star x := by rw [one_mul, mul_one]
    _ ≤ star x := inf_le_right
  have h1 : star e ≤ 1 := by simpa using star_mono he
  exact le_antisymm (by simpa using key h1) (key he)

theorem le_mul_self_of_le_one {e : α} (he : e ≤ 1) : e ≤ e * e := calc
  e = e * 1 ⊓ e := by rw [mul_one, inf_idem]
  _ ≤ e * (1 ⊓ star e * e) := left_modular e 1 e
  _ ≤ e * (e * e) := by
    rw [star_eq_self_of_le_one he]
    exact mul_le_mul_right inf_le_right e
  _ ≤ e * e := mul_le_mul_right ((mul_le_mul_right he e).trans (mul_one e).le) e

theorem atom_cycle_right {r s p : α} (hr : IsAtom r) (hp : p ≠ ⊥) (h : p ≤ r * s) :
    r ≤ p * star s := by
  have h₁ : star p ≤ star s * star r := by simpa using star_mono h
  have h₂ : star p ≠ ⊥ := fun h0 => hp (by simpa using congrArg star h0)
  simpa using star_mono (atom_cycle_left (isAtom_star_iff.mpr hr) h₂ h₁)

theorem le_mul_of_le_mul_top {c e : α} (he : e ≤ 1) (h : c ≤ e * ⊤) : c ≤ e * c := calc
  c = e * ⊤ ⊓ c := (inf_eq_right.mpr h).symm
  _ ≤ e * (⊤ ⊓ star e * c) := left_modular e ⊤ c
  _ = e * (e * c) := by rw [top_inf_eq, star_eq_self_of_le_one he]
  _ ≤ e * c := mul_le_mul_right ((mul_le_mul_left he c).trans (one_mul c).le) e

theorem le_mul_of_le_top_mul {c e : α} (he : e ≤ 1) (h : c ≤ ⊤ * e) : c ≤ c * e := by
  have h₁ : star c ≤ e * ⊤ := by simpa [star_eq_self_of_le_one he] using star_mono h
  simpa [star_eq_self_of_le_one he] using star_mono (le_mul_of_le_mul_top he h₁)

namespace IsBasicMatrix

variable {m : ι → ι → α}

theorem const {e : α} (he : IsAtom e) (he1 : e ≤ 1) : IsBasicMatrix fun _ _ : ι => e where
  isAtom _ _ := he
  le_one _ := he1
  star_apply _ _ := star_eq_self_of_le_one he1
  le_mul _ _ _ := le_mul_self_of_le_one he1

open Classical in
theorem update (hm : IsBasicMatrix m) (k : ι) {x : ι → α} {e : α}
    (hx : ∀ l, l ≠ k → IsAtom (x l)) (he : IsAtom e) (he1 : e ≤ 1)
    (hxm : ∀ l l', l ≠ k → l' ≠ k → x l ≤ m l l' * x l') (hxe : ∀ l, l ≠ k → x l ≤ x l * e) :
    IsBasicMatrix fun l h =>
      if l = k then (if h = k then e else star (x h)) else if h = k then x l else m l h where
  isAtom i j := by
    split_ifs with hi hj hj
    · exact he
    · exact isAtom_star_iff.mpr (hx j hj)
    · exact hx i hi
    · exact hm.isAtom i j
  le_one i := by
    split_ifs with hi
    · exact he1
    · exact hm.le_one i
  star_apply i j := by
    by_cases hi : i = k <;> by_cases hj : j = k <;> simp only [hi, hj, ↓reduceIte]
    · exact star_eq_self_of_le_one he1
    · exact star_star _
    · exact hm.star_apply i j
  le_mul i j l := by
    by_cases hi : i = k <;> by_cases hj : j = k <;> by_cases hl : l = k <;>
      simp only [hi, hj, hl, ↓reduceIte]
    · exact le_mul_self_of_le_one he1
    · simpa [star_eq_self_of_le_one he1] using star_mono (hxe l hl)
    · exact atom_cycle_left he (hx j hj).ne_bot (hxe j hj)
    · simpa [hm.star_apply] using star_mono (hxm l j hl hj)
    · exact hxe i hi
    · exact atom_cycle_right (hm.isAtom i l) (hx i hi).ne_bot (hxm i l hi hl)
    · exact hxm i j hi hj
    · exact hm.le_mul i j l

theorem exists_apply_eq [IsAtomic α] {a : α} (ha : IsAtom a) {i j : ι} (hij : i ≠ j) :
    ∃ m : ι → ι → α, IsBasicMatrix m ∧ m i j = a := by
  classical
  obtain ⟨e₀, he₀, he₀1, h₀⟩ := exists_atom_le_mul_left ha (one_mul a).ge
  obtain ⟨e₁, he₁, he₁1, h₁⟩ := exists_atom_le_mul_right ha (mul_one a).ge
  refine ⟨_, (const (ι := ι) he₀ he₀1).update j (x := fun _ => a) (fun _ _ => ha) he₁ he₁1
    (fun _ _ _ _ => h₀) (fun _ _ => h₁), ?_⟩
  simp [hij]

end IsBasicMatrix

end NonAssoc

section SemiAssoc

variable {α : Type u} [SemiAssocRelationAlgebra α] {ι : Type v}

theorem top_mul_assoc (a b : α) : ⊤ * a * b = ⊤ * (a * b) :=
  star_injective <| by simpa using (mul_assoc_top (star b) (star a)).symm

namespace IsBasicMatrix

variable {m : ι → ι → α}

theorem le_diag_mul (hm : IsBasicMatrix m) {c v : α} {l p : ι} (h : c ≤ m l p * v) :
    c ≤ m l l * c := by
  refine le_mul_of_le_mul_top (hm.le_one l) ?_
  calc
    c ≤ m l l * m l p * v := h.trans (mul_le_mul_left (hm.le_mul l l p) v)
    _ ≤ m l l * m l p * ⊤ := mul_le_mul_right le_top _
    _ = m l l * (m l p * ⊤) := mul_assoc_top _ _
    _ ≤ m l l * ⊤ := mul_le_mul_right le_top _

theorem mul_ne_bot (hm : IsBasicMatrix m) {c : α} (hc : c ≠ ⊥) {l p : ι} (h : c ≤ m p p * c) :
    m l p * c ≠ ⊥ := by
  have h₁ : c ≤ m p l * ⊤ := calc
    c ≤ m p l * m l p * c := h.trans (mul_le_mul_left (hm.le_mul p l p) c)
    _ ≤ m p l * m l p * ⊤ := mul_le_mul_right le_top _
    _ = m p l * (m l p * ⊤) := mul_assoc_top _ _
    _ ≤ m p l * ⊤ := mul_le_mul_right le_top _
  simpa [hm.star_apply] using inf_star_mul_ne_bot hc h₁

end IsBasicMatrix

theorem le_mul_of_le_mul_of_le_mul {c u v e : α} (he : e ≤ 1) (h : c ≤ u * v) (hv : v ≤ v * e) :
    c ≤ c * e := by
  refine le_mul_of_le_top_mul he ?_
  calc
    c ≤ ⊤ * (v * e) := h.trans (mul_le_mul' le_top hv)
    _ = ⊤ * v * e := (top_mul_assoc v e).symm
    _ ≤ ⊤ * e := mul_le_mul_left le_top e

open Classical in
theorem IsBasicMatrix.exists_update [IsAtomic α] {m : ι → ι → α} (hm : IsBasicMatrix m)
    {k p q r : ι} (hcover : ∀ l, l = k ∨ l = p ∨ l = q ∨ l = r) (hp : p ≠ k) (hq : q ≠ k)
    {xp xq : α} (hxp : IsAtom xp) (hxq : IsAtom xq) (hpq : p = q → xp = xq)
    (h : xq ≤ m q p * xp) (H : ∃ c, IsAtom c ∧ c ≤ m r p * xp ∧ c ≤ m r q * xq) :
    ∃ m', IsBasicMatrix m' ∧ m' p k = xp ∧ m' q k = xq ∧ m' k p = star xp ∧ m' k q = star xq ∧
      ∀ l h, k ≠ l → k ≠ h → m l h = m' l h := by
  obtain ⟨c, hc, hcp, hcq⟩ := H
  obtain ⟨e, he, he1, hpe⟩ := exists_atom_le_mul_right hxp (mul_one xp).ge
  let x : ι → α := fun l => if l = p then xp else if l = q then xq else c
  have hxp' : x p = xp := by simp [x]
  have hxq' : x q = xq := by
    by_cases hqp : q = p
    · simpa [x, hqp] using hpq hqp.symm
    · simp [x, hqp]
  have hx : ∀ l, IsAtom (x l) := fun l => by
    simp only [x]
    split_ifs <;> assumption
  -- the consistency conditions between the three points other than `k`
  have hqp : x q ≤ m q p * x p := by rwa [hxp', hxq']
  have hpq' : x p ≤ m p q * x q := by
    simpa [hm.star_apply] using atom_cycle_left (hx p) (hx q).ne_bot hqp
  have hpp : x p ≤ m p p * x p := hm.le_diag_mul hpq'
  have hqq : x q ≤ m q q * x q := hm.le_diag_mul hqp
  have hrp : x r ≤ m r p * x p := by
    by_cases h₁ : r = p
    · rw [h₁]; exact hpp
    by_cases h₂ : r = q
    · rw [h₂]; exact hqp
    · simpa [x, h₁, h₂] using hcp
  have hrq : x r ≤ m r q * x q := by
    by_cases h₁ : r = p
    · rw [h₁]; exact hpq'
    by_cases h₂ : r = q
    · rw [h₂]; exact hqq
    · rw [hxq']; simpa [x, h₁, h₂] using hcq
  have hpr : x p ≤ m p r * x r := by
    simpa [hm.star_apply] using atom_cycle_left (hx p) (hx r).ne_bot hrp
  have hqr : x q ≤ m q r * x r := by
    simpa [hm.star_apply] using atom_cycle_left (hx q) (hx r).ne_bot hrq
  have hrr : x r ≤ m r r * x r := hm.le_diag_mul hrp
  have hxm : ∀ l l', l ≠ k → l' ≠ k → x l ≤ m l l' * x l' := by
    intro l l' hl hl'
    rcases (hcover l).resolve_left hl with h₁ | h₁ | h₁ <;>
      rcases (hcover l').resolve_left hl' with h₂ | h₂ | h₂ <;> rw [h₁, h₂]
    · exact hpp
    · exact hpq'
    · exact hpr
    · exact hqp
    · exact hqq
    · exact hqr
    · exact hrp
    · exact hrq
    · exact hrr
  have hxe : ∀ l, l ≠ k → x l ≤ x l * e := by
    intro l hl
    have hpe' : x p ≤ x p * e := by rwa [hxp']
    rcases (hcover l).resolve_left hl with h₁ | h₁ | h₁ <;> rw [h₁]
    · exact hpe'
    · exact le_mul_of_le_mul_of_le_mul he1 hqp hpe'
    · exact le_mul_of_le_mul_of_le_mul he1 hrp hpe'
  refine ⟨_, hm.update k (fun l _ => hx l) he he1 hxm hxe, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hp, hxp']
  · simp [hq, hxq']
  · simp [hp, hxp']
  · simp [hq, hxq']
  · intro l h hl hh
    simp [Ne.symm hl, Ne.symm hh]

end SemiAssoc

section Basis

variable {α : Type u} {ι : Type v}

-- the cycle-law consequences of `m i j ≤ a * b` used to extend a basic matrix
private theorem IsBasicMatrix.cycle_aux [NonAssocRelationAlgebra α] {m : ι → ι → α}
    (hm : IsBasicMatrix m) {i j : ι} {a b : α} (ha : IsAtom a) (hb : IsAtom b)
    (hab : m i j ≤ a * b) :
    a ≤ m i j * star b ∧ star b ≤ m j i * a ∧ (i = j → b = star a) := by
  have h₁ : b ≤ star a * m i j := atom_cycle_left hb (hm.isAtom i j).ne_bot hab
  refine ⟨atom_cycle_right ha (hm.isAtom i j).ne_bot hab, ?_, ?_⟩
  · simpa [hm.star_apply] using star_mono h₁
  · rintro rfl
    refine ((isAtom_star_iff.mpr ha).le_iff_eq hb.ne_bot).mp ?_
    exact h₁.trans ((mul_le_mul_right (hm.le_one i) _).trans (mul_one _).le)

theorem isRelationalBasis_setOf_isBasicMatrix_fin_three [SemiAssocRelationAlgebra α]
    [IsAtomic α] : IsRelationalBasis {m : Fin 3 → Fin 3 → α | IsBasicMatrix m} where
  isBasicMatrix hm := hm
  exists_apply_eq ha :=
    let ⟨m, hm, h⟩ := IsBasicMatrix.exists_apply_eq ha (i := (0 : Fin 3)) (j := 1) (by decide)
    ⟨m, hm, 0, 1, by decide, h⟩
  exists_apply_eq_apply_eq {m i j k a b} hm hik hjk ha hb hab := by
    replace hm : IsBasicMatrix m := hm
    obtain ⟨ha', hb', hij⟩ := hm.cycle_aux ha hb hab
    have hia : a ≤ m i i * a := hm.le_diag_mul ha'
    by_cases h : i = j
    · subst h
      obtain rfl := hij rfl
      have hcover : ∀ i k : Fin 3, i ≠ k → ∃ q, q ≠ k ∧ q ≠ i ∧ ∀ l, l = k ∨ l = i ∨ l = q := by
        decide
      obtain ⟨q, hqk, hqi, hq⟩ := hcover i k hik
      obtain ⟨c, hc, hcq⟩ :=
        (eq_bot_or_exists_atom_le _).resolve_left (hm.mul_ne_bot ha.ne_bot (l := q) hia)
      obtain ⟨m', hm', h₁, -, h₂, -, h₃⟩ := hm.exists_update (r := q)
        (fun l => by grind) hik hqk ha hc (fun h => absurd h.symm hqi) hcq
        ⟨c, hc, hcq, hm.le_diag_mul hcq⟩
      exact ⟨m', hm', h₁, h₂, h₃⟩
    · have hcover : ∀ i j k : Fin 3, i ≠ k → j ≠ k → i ≠ j → ∀ l, l = k ∨ l = i ∨ l = j := by
        decide
      obtain ⟨m', hm', h₁, -, -, h₂, h₃⟩ := hm.exists_update (r := j)
        (fun l => by grind) hik hjk ha (isAtom_star_iff.mpr hb) (fun h' => absurd h' h) hb'
        ⟨star b, isAtom_star_iff.mpr hb, hb', hm.le_diag_mul hb'⟩
      exact ⟨m', hm', h₁, by simpa using h₂, h₃⟩

theorem IsBasicMatrix.exists_atom_le_inf [RelationAlgebra α] [IsAtomic α] {m : ι → ι → α}
    (hm : IsBasicMatrix m) {p q : ι} {xp xq : α} (hxq : IsAtom xq) (h : xq ≤ m q p * xp)
    (r : ι) : ∃ c, IsAtom c ∧ c ≤ m r p * xp ∧ c ≤ m r q * xq := by
  have h₁ : xq ≤ m q r * (m r p * xp) := calc
    xq ≤ m q r * m r p * xp := h.trans (mul_le_mul_left (hm.le_mul q r p) xp)
    _ = m q r * (m r p * xp) := mul_assoc _ _ _
  have h₂ : m r p * xp ⊓ m r q * xq ≠ ⊥ := by
    simpa [hm.star_apply] using inf_star_mul_ne_bot hxq.ne_bot h₁
  obtain ⟨c, hc, hle⟩ := (eq_bot_or_exists_atom_le _).resolve_left h₂
  exact ⟨c, hc, hle.trans inf_le_left, hle.trans inf_le_right⟩

theorem isRelationalBasis_setOf_isBasicMatrix_fin_four [RelationAlgebra α] [IsAtomic α] :
    IsRelationalBasis {m : Fin 4 → Fin 4 → α | IsBasicMatrix m} where
  isBasicMatrix hm := hm
  exists_apply_eq ha :=
    let ⟨m, hm, h⟩ := IsBasicMatrix.exists_apply_eq ha (i := (0 : Fin 4)) (j := 1) (by decide)
    ⟨m, hm, 0, 1, by decide, h⟩
  exists_apply_eq_apply_eq {m i j k a b} hm hik hjk ha hb hab := by
    replace hm : IsBasicMatrix m := hm
    obtain ⟨ha', hb', hij⟩ := hm.cycle_aux ha hb hab
    have hia : a ≤ m i i * a := hm.le_diag_mul ha'
    by_cases h : i = j
    · subst h
      obtain rfl := hij rfl
      have hcover : ∀ i k : Fin 4, i ≠ k →
          ∃ q r, q ≠ k ∧ q ≠ i ∧ ∀ l, l = k ∨ l = i ∨ l = q ∨ l = r := by
        decide
      obtain ⟨q, r, hqk, hqi, hq⟩ := hcover i k hik
      obtain ⟨c, hc, hcq⟩ :=
        (eq_bot_or_exists_atom_le _).resolve_left (hm.mul_ne_bot ha.ne_bot (l := q) hia)
      obtain ⟨m', hm', h₁, -, h₂, -, h₃⟩ := hm.exists_update hq hik hqk ha hc
        (fun h => absurd h.symm hqi) hcq (hm.exists_atom_le_inf hc hcq r)
      exact ⟨m', hm', h₁, h₂, h₃⟩
    · have hcover : ∀ i j k : Fin 4, i ≠ k → j ≠ k → i ≠ j →
          ∃ r, ∀ l, l = k ∨ l = i ∨ l = j ∨ l = r := by
        decide
      obtain ⟨r, hr⟩ := hcover i j k hik hjk h
      obtain ⟨m', hm', h₁, -, -, h₂, h₃⟩ := hm.exists_update hr hik hjk ha
        (isAtom_star_iff.mpr hb) (fun h' => absurd h' h) hb'
        (hm.exists_atom_le_inf (isAtom_star_iff.mpr hb) hb' r)
      exact ⟨m', hm', h₁, by simpa using h₂, h₃⟩

theorem IsRelationalBasis.mul_assoc_le [NonAssocRelationAlgebra α] [IsAtomic α]
    {B : Set (Fin 4 → Fin 4 → α)} (hB : IsRelationalBasis B) (x y z : α) :
    x * y * z ≤ x * (y * z) := by
  by_contra hle
  have hne : x * y * z ⊓ (x * (y * z))ᶜ ≠ ⊥ := fun h0 =>
    hle (disjoint_compl_right_iff.mp (disjoint_iff.mpr h0))
  obtain ⟨p, hp, hple⟩ := (eq_bot_or_exists_atom_le _).resolve_left hne
  refine hp.ne_bot (le_bot_iff.mp ?_)
  rw [← inf_compl_self (x * (y * z))]
  refine le_inf ?_ (hple.trans inf_le_right)
  obtain ⟨q, hq, hqxy, hpq⟩ := exists_atom_le_mul_left hp (hple.trans inf_le_left)
  obtain ⟨c, hc, hcz, hpc⟩ := exists_atom_le_mul_right hp hpq
  obtain ⟨a, ha, hax, hqa⟩ := exists_atom_le_mul_left hq hqxy
  obtain ⟨b, hb, hby, hqb⟩ := exists_atom_le_mul_right hq hqa
  obtain ⟨m, hm, i, j, hij, rfl⟩ := hB.exists_apply_eq hp
  have hfresh : ∀ i j : Fin 4, i ≠ j →
      ∃ k k', i ≠ k ∧ j ≠ k ∧ i ≠ k' ∧ k ≠ k' ∧ j ≠ k' := by
    decide
  obtain ⟨k, k', hik, hjk, hik', hkk', hjk'⟩ := hfresh i j hij
  obtain ⟨m₁, hm₁, h₁q, h₁c, h₁⟩ := hB.exists_apply_eq_apply_eq hm hik hjk hq hc hpc
  obtain ⟨m₂, hm₂, h₂a, h₂b, h₂⟩ :=
    hB.exists_apply_eq_apply_eq hm₁ hik' hkk' ha hb (h₁q ▸ hqb)
  have hm₂' := hB.isBasicMatrix hm₂
  calc
    m i j = m₂ i j := (h₁ i j hik.symm hjk.symm).trans (h₂ i j hik'.symm hjk'.symm)
    _ ≤ m₂ i k' * m₂ k' j := hm₂'.le_mul i k' j
    _ ≤ m₂ i k' * (m₂ k' k * m₂ k j) := mul_le_mul_right (hm₂'.le_mul k' k j) _
    _ = a * (b * c) := by rw [h₂a, h₂b, ← h₂ k j hkk'.symm hjk'.symm, h₁c]
    _ ≤ x * (y * z) := mul_le_mul' hax (mul_le_mul' hby hcz)

theorem IsRelationalBasis.mul_assoc [NonAssocRelationAlgebra α] [IsAtomic α]
    {B : Set (Fin 4 → Fin 4 → α)} (hB : IsRelationalBasis B) (x y z : α) :
    x * y * z = x * (y * z) := by
  refine le_antisymm (hB.mul_assoc_le x y z) (star_le_star_iff.mp ?_)
  simpa using hB.mul_assoc_le (star z) (star y) (star x)

end Basis

section Dimensional

variable {α : Type u} [NonAssocRelationAlgebra α]

theorem Dimensional.mul_assoc_top (h : Dimensional α (Fin 3)) (a b : α) :
    a * b * ⊤ = a * (b * ⊤) := by
  obtain ⟨β, _, f, hf, -⟩ := h
  apply hf
  simp [RelationAlgebra.mul_assoc_top]

theorem Dimensional.mul_assoc (h : Dimensional α (Fin 4)) (a b c : α) :
    a * b * c = a * (b * c) := by
  obtain ⟨β, _, f, hf, _, B, hB⟩ := h
  apply hf
  simpa using hB.mul_assoc (f a) (f b) (f c)

theorem dimensional_fin_three (α : Type u) [SemiAssocRelationAlgebra α] :
    Dimensional α (Fin 3) :=
  ⟨CanonicalExtension α, inferInstance, canonicalEmbedding α, canonicalEmbedding_injective,
    inferInstance, _, isRelationalBasis_setOf_isBasicMatrix_fin_three⟩

theorem dimensional_fin_four (α : Type u) [RelationAlgebra α] : Dimensional α (Fin 4) :=
  ⟨CanonicalExtension α, inferInstance, canonicalEmbedding α, canonicalEmbedding_injective,
    inferInstance, _, isRelationalBasis_setOf_isBasicMatrix_fin_four⟩

theorem dimensional_fin_three_iff :
    Dimensional α (Fin 3) ↔ ∀ a b : α, a * b * ⊤ = a * (b * ⊤) := by
  refine ⟨Dimensional.mul_assoc_top, fun h => ?_⟩
  let : SemiAssocRelationAlgebra α := { ‹NonAssocRelationAlgebra α› with mul_assoc_top := h }
  exact dimensional_fin_three α

theorem dimensional_fin_four_iff :
    Dimensional α (Fin 4) ↔ ∀ a b c : α, a * b * c = a * (b * c) := by
  refine ⟨Dimensional.mul_assoc, fun h => ?_⟩
  let : RelationAlgebra α :=
    { ‹NonAssocRelationAlgebra α› with mul_assoc := h, mul_assoc_top := fun a b => h a b ⊤ }
  exact dimensional_fin_four α

theorem ra_three_iff : RA α 3 ↔ ∀ a b : α, a * b * ⊤ = a * (b * ⊤) :=
  (ra_natCast_iff (n := 3)).trans dimensional_fin_three_iff

theorem ra_four_iff : RA α 4 ↔ ∀ a b c : α, a * b * c = a * (b * c) :=
  (ra_natCast_iff (n := 4)).trans dimensional_fin_four_iff

end Dimensional

end Cslib.RelationAlgebra
