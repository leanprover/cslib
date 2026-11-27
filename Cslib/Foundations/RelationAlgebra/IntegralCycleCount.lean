/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.SymmetricCycleOrbits

/-!
# Counting integral tables with nonsymmetric diversity atoms

We first choose the isomorphism class of the subtable on symmetric diversity atoms. Once
this subtable has been labelled, only the cycle orbits containing a nonsymmetric atom remain
to be specified. With `d = s + 2 * m` diversity atoms, the `m` converse pairs cost at
least `m * d` binary choices of cycles. Labelling their atoms costs at most `d ^ (2 * m)`.
Thus the normalized count in each nonsymmetric stratum is bounded by a constant times
`(d ^ 2 / 2 ^ d) ^ m`.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.IntegralAtom

open AtomStructure SymmetricCycles

private abbrev D (s m : ℕ) := Fin s ⊕ Fin m × Bool

private def flip {s m : ℕ} : D s m → D s m
  | .inl a => .inl a
  | .inr (a, b) => .inr (a, !b)

private theorem invol (s m : ℕ) : Function.Involutive (@flip s m) := by
  rintro (a | ⟨a,b⟩) <;> simp [flip]

private def label {s m : ℕ} : D s m → IntegralAtom (Fin s) (Fin m)
  | .inl a => .symm a
  | .inr (a, b) => .nsymm a b

private theorem label_flip {s m : ℕ} (a : D s m) : label (flip a) = conv (label a) := by
  rcases a with a | ⟨a,b⟩ <;> rfl

private theorem exists_label {s m : ℕ} {a : IntegralAtom (Fin s) (Fin m)} (ha : a ≠ .one) :
    ∃ x, label x = a := by
  cases a with
  | one => contradiction
  | symm a => exact ⟨.inl a, rfl⟩
  | nsymm a b => exact ⟨.inr (a,b), rfl⟩

private abbrev Key (s m : ℕ) := Triangle.Orbit (invol s m)

private def triangleKey {s m : ℕ} (a b c : D s m) : Key s m :=
  letI := Triangle.action (invol s m)
  Quotient.mk (MulAction.orbitRel _ _) (⟨![a,b,c]⟩ : Triangle flip)

private abbrev triple {X : Type*} (a b c : X) := a ::ₛ b ::ₛ c ::ₛ Sym.nil

private theorem exists_triple {X : Type*} (z : Sym X 3) : ∃ a b c, z = triple a b c := by
  obtain ⟨a, z, rfl⟩ := z.exists_eq_cons_of_succ
  obtain ⟨b, z, rfl⟩ := z.exists_eq_cons_of_succ
  obtain ⟨c, z, rfl⟩ := z.exists_eq_cons_of_succ
  exact ⟨a, b, c, by rw [Sym.eq_nil_of_card_zero z]⟩

private theorem congr_triple {X Y : Type*} (p : X → X → X → Y)
    (hs : ∀ a b c, p a b c = p b a c) (ht : ∀ a b c, p a b c = p a c b)
    {a b c d e f : X} (h : triple a b c = triple d e f) : p a b c = p d e f := by
  have pair_eq {x y z w : X} (he : pair x y = pair z w) :
      (x = z ∧ y = w) ∨ (x = w ∧ y = z) := by
    have hm : x ∈ pair z w := he ▸ Sym.mem_cons_self _ _
    have hm' : x = z ∨ x = w := by simpa [pair] using hm
    rcases hm' with rfl | rfl
    · exact Or.inl ⟨rfl, by simpa only [pair, Sym.cons_inj_right, Sym.cons_inj_left] using he⟩
    · unfold pair at he
      rw [Sym.cons_swap z x] at he
      exact Or.inr ⟨rfl, by simpa only [pair, Sym.cons_inj_right, Sym.cons_inj_left] using he⟩
  have same {a b c e f : X} (he : triple a b c = triple a e f) : p a b c = p a e f := by
    rcases pair_eq ((Sym.cons_inj_right _ _ _).mp he) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact ht _ _ _
  have hm : a ∈ triple d e f := h ▸ Sym.mem_cons_self _ _
  have hm' : a = d ∨ a = e ∨ a = f := by simpa [triple] using hm
  rcases hm' with rfl | rfl | rfl
  · exact same h
  · rw [hs d a f]
    apply same
    simpa only [triple, Sym.cons_swap d a] using h
  · rw [ht d e a, hs d a e]
    apply same
    simpa only [triple, Sym.cons_swap e a, Sym.cons_swap d a] using h

private noncomputable def symKey {s m : ℕ} (z : Sym (Fin s) 3) : Key s m :=
  let a := (exists_triple z).choose
  let b := (exists_triple z).choose_spec.choose
  let c := (exists_triple z).choose_spec.choose_spec.choose
  triangleKey (.inl a) (.inl b) (.inl c)

private theorem symKey_triple {s m : ℕ} (a b c : Fin s) :
    symKey (m := m) (triple a b c) = triangleKey (.inl a) (.inl b) (.inl c) := by
  let p (x y z : Fin s) : Key s m := triangleKey (.inl x) (.inl y) (.inl z)
  have hs (x y z : Fin s) : p x y z = p y x z := by
    let _ := Triangle.action (invol s m)
    apply Quotient.sound
    refine ⟨DihedralGroup.sr 1, Triangle.ext (funext fun i => ?_)⟩
    fin_cases i <;> rfl
  have ht (x y z : Fin s) : p x y z = p x z y := by
    let _ := Triangle.action (invol s m)
    apply Quotient.sound
    refine ⟨DihedralGroup.sr 0, Triangle.ext (funext fun i => ?_)⟩
    fin_cases i <;> rfl
  exact congr_triple p hs ht (exists_triple (triple a b c)).choose_spec.choose_spec.choose_spec.symm

private theorem symKey_injective (s m : ℕ) : Function.Injective (@symKey s m) := by
  rintro x y h
  obtain ⟨a,b,c,rfl⟩ := exists_triple x
  obtain ⟨d,e,f,rfl⟩ := exists_triple y
  simp only [symKey_triple] at h
  let _ := Triangle.action (invol s m)
  obtain ⟨g,hg⟩ := Quotient.exact h
  have h0 := congrArg (fun t : Triangle (@flip s m) => t.edge 0) hg
  have h1 := congrArg (fun t : Triangle (@flip s m) => t.edge 1) hg
  have h2 := congrArg (fun t : Triangle (@flip s m) => t.edge 2) hg
  rcases g with i | i <;> fin_cases i
  all_goals
    change Sum.inl _ = Sum.inl _ at h0 h1 h2
    obtain rfl := Sum.inl.inj h0
    obtain rfl := Sum.inl.inj h1
    obtain rfl := Sum.inl.inj h2
    apply Sym.ext
    simp only [triple, Sym.coe_cons, ← Multiset.singleton_add]
  all_goals ac_rfl

private abbrev Mixed (s m : ℕ) := ↥((Set.range (@symKey s m))ᶜ : Set (Key s m))

private theorem card_mixed_le (s m : ℕ) :
    Nat.card (Mixed s m) + ((s + 2).choose 3) + m * (s + 2 * m) ≤ (s + 2 * m + 2).choose 3 := by
  have hD : Nat.card (D s m) = s + 2 * m := by
    simp [D, Nat.card_eq_fintype_card, Nat.mul_comm]
  have hfix : Nat.card {a : D s m // flip a = a} = s := by
    let e : Fin s ≃ {a : D s m // flip a = a} :=
      { toFun a := ⟨.inl a, rfl⟩
        invFun := fun ⟨a, h⟩ => match a with
          | .inl a => a
          | .inr (a, b) => False.elim (by cases b <;> simp [flip] at h)
        left_inv _ := rfl
        right_inv := by
          rintro ⟨a | ⟨a,b⟩, h⟩
          · rfl
          · cases b <;> simp [flip] at h }
    rw [← Nat.card_congr e, Nat.card_fin]
  have h := Triangle.card_orbit_add_le_choose (invol s m) (m := m) (by rw [hfix, hD])
  rw [hD] at h
  have hc := (Set.range (@symKey s m)).ncard_add_ncard_compl
  rw [Set.ncard_range_of_injective (symKey_injective s m), Sym.natCard_sym_eq_choose, Nat.card_fin,
    Nat.add_succ_sub_one] at hc
  change _ + Nat.card (Mixed s m) = Nat.card (Key s m) at hc
  rw [Nat.add_comm (Nat.card (Mixed s m)), hc]
  exact h

attribute [local instance] SymmetricCycles.tableAction

private structure Presentation (s m : ℕ) where
  S : AtomStructure (IntegralAtom (Fin s) (Fin m))
  lawful : LawfulAtomStructure S
  hconv : S.conv = conv
  hid : S.id = {one}

attribute [local instance] Presentation.lawful

private def Presentation.table {s m : ℕ} (A : Presentation s m) : Set (Key s m) :=
  A.S.orbitCycles (invol s m) label fun a => A.hconv ▸ label_flip a

private theorem Presentation.mem_table {s m : ℕ} (A : Presentation s m) (a b c : D s m) :
    triangleKey a b c ∈ A.table ↔ (label a, label b, conv (label c)) ∈ A.S.cycles := by
  change (_, _, A.S.conv _) ∈ A.S.cycles ↔ _
  rw [A.hconv]
  rfl

private theorem Presentation.ext_table {s m : ℕ} {A B : Presentation s m}
    (he : A.table = B.table) : A.S = B.S := by
  apply A.S.ext_of_diversity (A.hconv.trans B.hconv.symm) (A.hid.trans B.hid.symm)
  · funext a
    have ha := (A.S.rightId_spec a).1
    have hb := (B.S.rightId_spec a).1
    rw [A.hid] at ha
    rw [B.hid] at hb
    exact ha.trans hb.symm
  · intro x hx y hy z hz
    rw [A.hid] at hx hy hz
    obtain ⟨a, rfl⟩ := exists_label hx
    obtain ⟨b, rfl⟩ := exists_label hy
    obtain ⟨c, rfl⟩ := exists_label hz
    have h := (A.mem_table a b (flip c)).symm.trans
      ((Set.ext_iff.mp he _).trans (B.mem_table a b (flip c)))
    simpa only [label_flip, ← A.hconv, A.S.conv_conv] using h

private noncomputable abbrev Presentation.pureTable {s m : ℕ} (A : Presentation s m) :
    Table (Fin s) :=
  symKey ⁻¹' A.table

private def permute {s m : ℕ} (g : Equiv.Perm (Fin s)) :
    IntegralAtom (Fin s) (Fin m) → IntegralAtom (Fin s) (Fin m)
  | .one => .one
  | .symm a => .symm (g a)
  | .nsymm a b => .nsymm a b

private def permSymm {s m : ℕ} (g : Equiv.Perm (Fin s)) :
    Equiv.Perm (IntegralAtom (Fin s) (Fin m)) where
  toFun := permute g
  invFun := permute g.symm
  left_inv a := by cases a <;> simp [permute]
  right_inv a := by cases a <;> simp [permute]

private def Presentation.relabel {s m : ℕ} (A : Presentation s m) (g : Equiv.Perm (Fin s)) :
    Presentation s m where
  S := A.S.map (permSymm g)
  lawful := inferInstance
  hconv := by
    funext a
    rw [AtomStructure.map_conv, A.hconv]
    cases a <;> simp [permSymm, permute, conv]
  hid := by
    ext a
    rw [AtomStructure.mem_map_id, A.hid]
    cases a <;> simp [permSymm, permute]

private theorem Presentation.pure_relabel {s m : ℕ} (A : Presentation s m)
    (g : Equiv.Perm (Fin s)) :
    (A.relabel g).pureTable = g • A.pureTable := by
  ext z
  obtain ⟨a,b,c,rfl⟩ := exists_triple z
  change symKey (triple a b c) ∈ (A.relabel g).table ↔ symKey ((triple a b c).map g.symm) ∈ A.table
  simp only [triple, Sym.map_cons, Sym.eq_nil_of_card_zero (Sym.nil.map g.symm)]
  rw [symKey_triple, symKey_triple, Presentation.mem_table, Presentation.mem_table]
  rfl

private noncomputable def presentation {s m : ℕ} (q : IsoClass.ofSymmNsymm s m) :
    Presentation s m := ⟨ofCycles q.out.val, q.out.prop, rfl, rfl⟩

/-- After labelling the symmetric subtable canonically, the other cycle orbits give an
upper bound on the number of classes with `s` symmetric atoms and `m` converse pairs. -/
theorem IsoClass.card_le_card_symmetric_tables (s m : ℕ) :
    Nat.card (ofSymmNsymm s m) ≤ Nat.card (UnlabelledTable (Fin s)) *
      2 ^ (((s + 2 * m + 2).choose 3) - (s + 2).choose 3 - m * (s + 2 * m)) := by
  classical
  let X := ofSymmNsymm s m
  let A (q : X) := presentation q
  let pureClass (q : X) : UnlabelledTable (Fin s) := ⟦(A q).pureTable⟧
  have norm (q : X) : ∃ g : Equiv.Perm (Fin s), g • (A q).pureTable = (pureClass q).out :=
    Quotient.exact (pureClass q).out_eq
  choose g hg using norm
  let B (q : X) := (A q).relabel (g q)
  have hB (q : X) : (B q).pureTable = (pureClass q).out := ((A q).pure_relabel _).trans (hg q)
  let code (q : X) := (pureClass q, (Subtype.val ⁻¹' (B q).table : Set (Mixed s m)))
  have hinj : Function.Injective code := by
    intro x y he
    have ht : (B x).table = (B y).table := by
      ext t
      by_cases h : t ∈ Set.range (@symKey s m)
      · obtain ⟨z,rfl⟩ := h
        have hq : pureClass x = pureClass y := congrArg Prod.fst he
        exact Set.ext_iff.mp ((hB x).trans (hq ▸ (hB y).symm)) z
      · exact Set.ext_iff.mp (congrArg Prod.snd he) ⟨t,h⟩
    have equiv {S R : AtomStructure (IntegralAtom (Fin s) (Fin m))} [LawfulAtomStructure S]
        [LawfulAtomStructure R] (h : S = R) :
        Nonempty (RelationAlgebraEquiv (ComplexAlgebra S) (ComplexAlgebra R)) := by
      subst R
      exact ⟨.refl _⟩
    obtain ⟨e⟩ := equiv (Presentation.ext_table ht)
    have eqv := ((ComplexAlgebra.mapEquiv (A x).S (permSymm (g x))).trans e).trans
      (ComplexAlgebra.mapEquiv (A y).S (permSymm (g y))).symm
    have hh : (⟦x.out⟧ : X) = ⟦y.out⟧ := Quotient.sound ⟨eqv⟩
    exact x.out_eq.symm.trans (hh.trans y.out_eq)
  have h := Nat.card_le_card_of_injective _ hinj
  have hset : Nat.card (Set (Mixed s m)) = 2 ^ Nat.card (Mixed s m) := by
    let _ := Fintype.ofFinite (Mixed s m)
    simp [Nat.card_eq_fintype_card]
  rw [Nat.card_prod, hset] at h
  have hb := card_mixed_le s m
  exact h.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (by omega)))

open Filter
open scoped Topology

private noncomputable abbrev weight (d : ℕ) : ℝ := d.factorial / 2 ^ ((d + 2).choose 3)

private theorem tendsto_weight_orbits :
    Tendsto (fun d => (Nat.card (UnlabelledTable (Fin d)) : ℝ) * weight d) atTop (𝓝 1) := by
  simpa only [weight, mul_div_assoc, card_table, Nat.cast_pow, Nat.cast_ofNat] using
    tendsto_card_orbits_mul_factorial_div_tables

private theorem exists_stratum_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ s m : ℕ, let d := s + 2 * m
    (Nat.card (IsoClass.ofSymmNsymm s m) : ℝ) * weight d ≤ C * ((d : ℝ) ^ 2 / 2 ^ d) ^ m := by
  obtain ⟨C, hC⟩ := tendsto_weight_orbits.bddAbove_range
  have hs (s : ℕ) := hC (Set.mem_range_self s)
  refine ⟨C, (show 0 ≤ (Nat.card (UnlabelledTable (Fin 0)) : ℝ) * weight 0 by positivity).trans
    (hs 0), fun s m => ?_⟩
  let d := s + 2 * m
  let B (j : ℕ) := (j + 2).choose 3
  let a := B d - B s - m * d
  have hexp : B s + a + d * m = B d := by
    have hh := card_mixed_le s m
    dsimp only [a, B, d]
    rw [Nat.mul_comm (s + 2 * m) m]
    omega
  have hfac : (d.factorial : ℝ) ≤ s.factorial * (d : ℝ) ^ (2 * m) := by
    have hh := Nat.factorial_mul_descFactorial (show 2 * m ≤ d by dsimp [d]; omega)
    rw [show d - 2 * m = s by dsimp [d]; omega] at hh
    exact_mod_cast hh.symm.le.trans (Nat.mul_le_mul_left _ (Nat.descFactorial_le_pow d _))
  have htab : (Nat.card (UnlabelledTable (Fin s)) : ℝ) * s.factorial ≤ C * 2 ^ B s :=
    (div_le_iff₀ (by positivity)).mp (by simpa only [weight, mul_div_assoc, B] using hs s)
  have hcount : (Nat.card (IsoClass.ofSymmNsymm s m) : ℝ) ≤
      Nat.card (UnlabelledTable (Fin s)) * (2 : ℝ) ^ a := by
    exact_mod_cast IsoClass.card_le_card_symmetric_tables s m
  change _ * (_ / (2 : ℝ) ^ B d) ≤ _
  rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
  calc
    _ ≤ ((Nat.card (UnlabelledTable (Fin s)) : ℝ) * 2 ^ a) *
        (s.factorial * (d : ℝ) ^ (2 * m)) :=
      mul_le_mul hcount hfac (by positivity) (by positivity)
    _ = ((Nat.card (UnlabelledTable (Fin s)) : ℝ) * s.factorial) *
        (2 ^ a * (d : ℝ) ^ (2 * m)) := by ring
    _ ≤ (C * 2 ^ B s) * (2 ^ a * (d : ℝ) ^ (2 * m)) :=
      mul_le_mul_of_nonneg_right htab (by positivity)
    _ = C * ((d : ℝ) ^ 2 / 2 ^ d) ^ m * 2 ^ B d := by
      rw [← hexp, pow_add _ (B s + a), pow_add _ (B s), div_pow, ← pow_mul, ← pow_mul]
      field_simp

private theorem card_witness_orbits_le_integral (n : ℕ) :
    Nat.card {q : UnlabelledTable (Fin n) // q.HasCommonWitnesses 2} ≤
      Nat.card (IsoClass.ofAtoms (n + 1)) := by
  let X := {q : UnlabelledTable (Fin n) // q.HasCommonWitnesses 2}
  have h (q : X) :
      UnlabelledTable.toIsoClass q ∈ Set.range RelationAlgebra.IsoClass.ofIntegral := by
    rw [RelationAlgebra.IsoClass.range_ofIntegral]
    exact UnlabelledTable.isIntegral_toIsoClass q
  choose f hf using h
  exact Nat.card_le_card_of_injective f fun x y he =>
    UnlabelledTable.toIsoClass_injective n ((hf x).symm.trans (he ▸ hf y))

/-- The labelled symmetric-table count divided by the number of labellings is asymptotic to
the number of integral relation algebras, including those with nonsymmetric atoms. -/
theorem IsoClass.tendsto_card_integral_mul_factorial_div_tables :
    Tendsto (fun d => (Nat.card (ofAtoms (d + 1)) : ℝ) * d.factorial /
      Nat.card (Table (Fin d))) atTop (𝓝 1) := by
  simp only [card_table, Nat.cast_pow, Nat.cast_ofNat, mul_div_assoc]
  obtain ⟨C,hC,hbound⟩ := exists_stratum_bound
  let r (d : ℕ) := (d : ℝ) ^ 2 / 2 ^ d
  have hr := tendsto_pow_const_div_const_pow_of_one_lt 2 (r := (2 : ℝ)) (by norm_num)
  have herr := (tendsto_pow_const_div_const_pow_of_one_lt 3 (r := (2 : ℝ))
    (by norm_num)).const_mul C
  rw [mul_zero] at herr
  have hlower := (tendsto_card_hasCommonWitnesses_div_orbits 2).mul tendsto_weight_orbits
  have hupper := tendsto_weight_orbits.add herr
  rw [add_zero] at hupper
  rw [one_mul] at hlower
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
  · filter_upwards with d
    change _ / _ * (_ * weight d) ≤ _
    rw [← mul_assoc, div_mul_cancel₀ _ (by exact_mod_cast Nat.card_pos.ne' :
      (Nat.card (UnlabelledTable (Fin d)) : ℝ) ≠ 0)]
    exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (card_witness_orbits_le_integral d))
      (by positivity)
  · filter_upwards [hr.eventually_le_const (by norm_num : (0 : ℝ) < 1)] with d hd
    change r d ≤ 1 at hd
    have hdk (m : ℕ) (hm : m < d / 2) : d - 2 * (m + 1) + 2 * (m + 1) = d := by omega
    let f (m : ℕ) := (Nat.card (ofSymmNsymm (d - 2 * m) m) : ℝ) * weight d
    have hstep (m : ℕ) (hm : m ∈ Finset.range (d / 2)) : f (m + 1) ≤ C * r d := by
      have h := hbound (d - 2 * (m + 1)) (m + 1)
      dsimp only at h
      rw [hdk m (Finset.mem_range.mp hm)] at h
      exact h.trans (mul_le_mul_of_nonneg_left (by
        simpa only [pow_one] using pow_le_pow_of_le_one (by positivity : 0 ≤ r d) hd
          (show 1 ≤ m + 1 by omega)) hC)
    have hzero : f 0 ≤ Nat.card (UnlabelledTable (Fin d)) * weight d := by
      have h := card_le_card_symmetric_tables d 0
      simp only [Nat.mul_zero, Nat.add_zero, Nat.sub_self, Nat.zero_mul, pow_zero,
        Nat.mul_one] at h
      simpa only [f, Nat.mul_zero, Nat.sub_zero] using
        mul_le_mul_of_nonneg_right (Nat.cast_le (α := ℝ) |>.mpr h) (show 0 ≤ weight d by positivity)
    have hsum := Finset.sum_le_sum hstep
    rw [card_ofAtoms_succ_eq_sum_ofSymmNsymm, Nat.cast_sum, Finset.sum_mul]
    change ∑ m ∈ Finset.range (d / 2 + 1), f m ≤ _
    rw [Finset.sum_range_succ']
    apply add_le_add hsum hzero |>.trans
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    change _ + _ ≤ _ + C * ((d : ℝ) ^ 3 / 2 ^ d)
    have hh : ((d / 2 : ℕ) : ℝ) ≤ d := by exact_mod_cast Nat.div_le_self d 2
    have hle := mul_le_mul_of_nonneg_right hh (mul_nonneg hC (show 0 ≤ r d by positivity))
    rw [add_comm]
    apply add_le_add_right
    refine hle.trans_eq ?_
    dsimp only [r]
    ring

/-- Symmetric tables at any fixed witness bound, counted up to relabelling, have the same
asymptotic count as all relation algebras on one more Boolean atom. -/
theorem tendsto_witness_orbits_div_all (k : ℕ) :
    Tendsto (fun d => (Nat.card {q : UnlabelledTable (Fin d) // q.HasCommonWitnesses k} : ℝ) /
      Nat.card (RelationAlgebra.IsoClass.ofAtoms (d + 1))) atTop (𝓝 1) := by
  have hI := IsoClass.tendsto_card_integral_mul_factorial_div_tables
  simp only [card_table, Nat.cast_pow, Nat.cast_ofNat, mul_div_assoc] at hI
  have hAll := (tendsto_add_atTop_iff_nat 1).mpr RelationAlgebra.IsoClass.tendsto_integral_div_all
  have h := (((tendsto_card_hasCommonWitnesses_div_orbits k).mul tendsto_weight_orbits).div
    hI (by norm_num)).mul hAll
  simp only [one_mul, div_one] at h
  apply h.congr' _
  filter_upwards [hI.eventually_const_lt (by norm_num : (0 : ℝ) < 1)] with d hd
  have hIp : (Nat.card (IsoClass.ofAtoms (d + 1)) : ℝ) ≠ 0 := by
    intro hz
    change 0 < _ * weight d at hd
    rw [hz, zero_mul] at hd
    exact hd.false
  have hUp : (Nat.card (UnlabelledTable (Fin d)) : ℝ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have hw : weight d ≠ 0 := by positivity
  change _ / _ * (_ * weight d) / (_ * weight d) * (_ / _) = _
  rw [← mul_assoc, div_mul_cancel₀ _ hUp, mul_div_mul_right _ _ hw,
    div_mul_div_cancel₀ hIp]

end Cslib.RelationAlgebra.IntegralAtom
