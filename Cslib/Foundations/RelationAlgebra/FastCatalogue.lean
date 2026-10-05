/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.FastClassification
public import Cslib.Foundations.RelationAlgebra.FastTruthTable

/-!
# Bit-parallel certificates for finite catalogues

Each bit of a natural number describes one choice of diversity cycles. Bitwise operations
compute associativity for all choices simultaneously. A certificate equates this truth table
with the set of cycle profiles of the explicitly listed algebras and their atom renamings.
-/

@[expose] public section

namespace Cslib.RelationAlgebra

open Code

variable {j k r : ℕ}

/-- A cycle table together with its verified numeric encoding. -/
structure EncodedCycleTable (j k : ℕ) where
  /-- The certified integral cycle table. -/
  table : IntegralCycleTable j k
  /-- The numeric encoding of its atom composition relation. -/
  code : ℕ
  /-- Correctness of the numeric encoding. -/
  encodes : EncodesTable table.cycles code

namespace Code

/-- Intersect a bounded family of truth words, starting with the word `full`. -/
def andBelow (full : ℕ) (f : ℕ → ℕ) (n : ℕ) : ℕ :=
  Nat.rec full (fun i acc => Nat.land (f i) acc) n

/-- The truth word for equality of two Boolean expressions. -/
def iffWord (full a b : ℕ) : ℕ := Nat.xor full (Nat.xor a b)

/-- Associativity for every assignment represented by a bit of the supplied cycle words. -/
def associativityWord (n full : ℕ) (cycles : ℕ → ℕ → ℕ → ℕ) : ℕ :=
  andBelow full (fun a => andBelow full (fun b => andBelow full (fun c =>
    andBelow full (fun d => iffWord full
      (orBelow (fun t => Nat.land (cycles a b t) (cycles t c d)) n)
      (orBelow (fun t => Nat.land (cycles b c t) (cycles a t d)) n)) n) n) n) n

/-- The set of all cycle profiles of the listed algebras and their atom renamings. -/
def profileWord (m p : ℕ) (profiles : ℕ → ℕ → ℕ) : ℕ :=
  orBelow (fun i => orBelow (fun q => Nat.shiftLeft 1 (profiles i q)) p) m

theorem bitAt_and (a b i : ℕ) : bitAt (Nat.land a b) i = (bitAt a i && bitAt b i) := by
  simp only [bitAt_eq_testBit, Nat.land_eq, Nat.testBit_and]

theorem bitAt_orBelow {f : ℕ → ℕ} {n i : ℕ} :
    bitAt (orBelow f n) i = true ↔ ∃ u < n, bitAt (f u) i = true := by
  simp only [bitAt_eq_testBit, testBit_orBelow]

theorem bitAt_andBelow {full : ℕ} {f : ℕ → ℕ} {n i : ℕ}
    (hf : bitAt full i = true) :
    bitAt (andBelow full f n) i = true ↔ ∀ u < n, bitAt (f u) i = true := by
  induction n with
  | zero => change bitAt full i = true ↔ _; simp [hf]
  | succ n ih =>
    change bitAt (Nat.land (f n) (andBelow full f n)) i = true ↔ _
    rw [bitAt_and, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨hn, h⟩ u hu
      rcases Nat.lt_succ_iff_lt_or_eq.mp hu with hu | rfl
      · exact h u hu
      · exact hn
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun u hu => h u (Nat.lt_succ_of_lt hu)⟩

theorem bitAt_iffWord {full a b i : ℕ} (hf : bitAt full i = true) :
    bitAt (iffWord full a b) i = true ↔ (bitAt a i = true ↔ bitAt b i = true) := by
  simp only [iffWord, bitAt_eq_testBit, Nat.xor_eq, Nat.testBit_xor] at *
  rw [hf]
  cases a.testBit i <;> cases b.testBit i <;> decide

theorem bitAt_profileWord {m p mask : ℕ} {profiles : ℕ → ℕ → ℕ} :
    bitAt (profileWord m p profiles) mask = true ↔
      ∃ i < m, ∃ q < p, profiles i q = mask := by
  simp only [profileWord, bitAt_orBelow]
  simp only [bitAt_eq_testBit, Nat.shiftLeft_eq', Nat.one_shiftLeft,
    Nat.testBit_two_pow, decide_eq_true_eq]

end Code

/-- A bit of the associativity truth word is set exactly for associative cycle tables. -/
theorem bitAt_associativityWord_iff {cycles : Finset (Cycle j k)}
    {words : ℕ → ℕ → ℕ → ℕ} {full mask : ℕ} (hf : bitAt full mask = true)
    (hw : ∀ a b c : Atom j k, bitAt (words a.code b.code c.code) mask = true ↔
      cycleClosure cycles a b c) :
    bitAt (associativityWord (atomCount j k) full words) mask = true ↔
      AtomCompositionAssociative cycles := by
  have hcode {P : ℕ → Prop} :
      (∀ c < atomCount j k, P c) ↔ ∀ x : Atom j k, P x.code := by
    constructor
    · intro h x
      exact h _ x.code_lt
    · intro h c hc
      obtain ⟨x, rfl⟩ := Atom.exists_code hc
      exact h x
  have hex (a b c d : Atom j k) :
      bitAt (orBelow (fun t => Nat.land (words a.code b.code t)
        (words t c.code d.code)) (atomCount j k)) mask = true ↔
      ∃ t, cycleClosure cycles a b t ∧ cycleClosure cycles t c d := by
    simp only [bitAt_orBelow, bitAt_and, Bool.and_eq_true]
    constructor
    · rintro ⟨t, ht, h1, h2⟩
      obtain ⟨t, rfl⟩ := Atom.exists_code ht
      exact ⟨t, (hw _ _ _).mp h1, (hw _ _ _).mp h2⟩
    · rintro ⟨t, h1, h2⟩
      exact ⟨t.code, t.code_lt, (hw _ _ _).mpr h1, (hw _ _ _).mpr h2⟩
  have hex' (a b c d : Atom j k) :
      bitAt (orBelow (fun t => Nat.land (words b.code c.code t)
        (words a.code t d.code)) (atomCount j k)) mask = true ↔
      ∃ t, cycleClosure cycles b c t ∧ cycleClosure cycles a t d := by
    simp only [bitAt_orBelow, bitAt_and, Bool.and_eq_true]
    constructor
    · rintro ⟨t, ht, h1, h2⟩
      obtain ⟨t, rfl⟩ := Atom.exists_code ht
      exact ⟨t, (hw _ _ _).mp h1, (hw _ _ _).mp h2⟩
    · rintro ⟨t, h1, h2⟩
      exact ⟨t.code, t.code_lt, (hw _ _ _).mpr h1, (hw _ _ _).mpr h2⟩
  simp only [associativityWord, bitAt_andBelow hf, bitAt_iffWord hf]
  rw [hcode]
  apply forall_congr'
  intro a
  rw [hcode]
  apply forall_congr'
  intro b
  rw [hcode]
  apply forall_congr'
  intro c
  rw [hcode]
  apply forall_congr'
  intro d
  rw [hex, hex']
namespace Code

/-- Four atom codes specifying one necessary associativity equation. -/
abbrev Quadruple := ℕ × ℕ × ℕ × ℕ

/-- Intersect selected necessary associativity equations over all cycle assignments. -/
def associativityWordFor (n full : ℕ) (cycles : ℕ → ℕ → ℕ → ℕ)
    (quads : ℕ → Quadruple) (q : ℕ) : ℕ :=
  andBelow full (fun i =>
    let (a, b, c, d) := quads i
    iffWord full
      (orBelow (fun t => Nat.land (cycles a b t) (cycles t c d)) n)
      (orBelow (fun t => Nat.land (cycles b c t) (cycles a t d)) n)) q

end Code

/-- Every associative table satisfies any supplied family of associativity equations. -/
theorem bitAt_associativityWordFor {cycles : Finset (Cycle j k)}
    {words : ℕ → ℕ → ℕ → ℕ} {full mask q : ℕ} {quads : ℕ → Quadruple}
    (hf : bitAt full mask = true)
    (hw : ∀ a b c : Atom j k, bitAt (words a.code b.code c.code) mask = true ↔
      cycleClosure cycles a b c)
    (hq : ∀ i < q, (quads i).1 < atomCount j k ∧ (quads i).2.1 < atomCount j k ∧
      (quads i).2.2.1 < atomCount j k ∧ (quads i).2.2.2 < atomCount j k)
    (ha : AtomCompositionAssociative cycles) :
    bitAt (associativityWordFor (atomCount j k) full words quads q) mask = true := by
  have h := (bitAt_associativityWord_iff hf hw).mpr ha
  simp only [associativityWord, bitAt_andBelow hf] at h
  apply (bitAt_andBelow hf).mpr
  intro i hi
  obtain ⟨h1, h2, h3, h4⟩ := hq i hi
  exact h _ h1 _ h2 _ h3 _ h4

/-- A bit-parallel coverage certificate proves exhaustiveness of a finite catalogue. -/
theorem cycles_exhaustive_of_truthTable {m p q : ℕ} (reps : Fin r → Cycle j k)
    (cover : ∀ c : Cycle j k, ∃ i, (some c.1, some c.2.1, some c.2.2) ∈ cycleOrbit (reps i))
    (distinct : ∀ i l, (some (reps i).1, some (reps i).2.1, some (reps i).2.2) ∈
      cycleOrbit (reps l) ↔ i = l)
    (models : Fin m → IntegralCycleTable j k) (renames : Fin p → Atom j k → Atom j k)
    (hrenames : ∀ i, Function.Injective (renames i) ∧ renames i none = none ∧
      ∀ x, renames i x.converse = (renames i x).converse)
    (profiles : ℕ → ℕ → ℕ)
    (hprofiles : ∀ (i : Fin m) (s : Fin p), choiceMask (fun c =>
      decide (cycleClosure (models i).cycles (renames s (some (reps c).1))
        (renames s (some (reps c).2.1)) (renames s (some (reps c).2.2)))) = profiles i s)
    (words : ℕ → ℕ → ℕ → ℕ)
    (hwords : ∀ mask < 2 ^ r, ∀ a b c : Atom j k,
      bitAt (words a.code b.code c.code) mask = true ↔
        cycleClosure (selectedCycles reps (fun i => bitAt mask i)) a b c)
    (quads : ℕ → Quadruple)
    (hquads : ∀ i < q, (quads i).1 < atomCount j k ∧ (quads i).2.1 < atomCount j k ∧
      (quads i).2.2.1 < atomCount j k ∧ (quads i).2.2.2 < atomCount j k)
    (hcheck : associativityWordFor (atomCount j k) (truthOnes (2 ^ r)) words quads q =
      profileWord m p profiles) :
    ∀ bits : Fin r → Bool, AtomCompositionAssociative (selectedCycles reps bits) →
      ∃ i : Fin m, ∃ f, AtomRelabelling (selectedCycles reps bits) (models i).cycles f := by
  intro bits ha
  let mask := choiceMask bits
  have hm : mask < 2 ^ r := choiceMask_lt bits
  have hw : ∀ a b c : Atom j k, bitAt (words a.code b.code c.code) mask = true ↔
      cycleClosure (selectedCycles reps bits) a b c := by
    simpa only [mask, bitAt_choiceMask] using hwords mask hm
  have hf : bitAt (truthOnes (2 ^ r)) mask = true := by
    rw [bitAt_truthOnes, decide_eq_true_iff]
    exact hm
  have hbit := bitAt_associativityWordFor hf hw hquads ha
  rw [hcheck, bitAt_profileWord] at hbit
  obtain ⟨idx, hi, s, hs, he⟩ := hbit
  let i : Fin m := ⟨idx, hi⟩
  let p : Fin p := ⟨s, hs⟩
  refine ⟨i, renames p, atomRelabelling_of_cycle_basis reps cover
    (hrenames p).1 (hrenames p).2.1 (hrenames p).2.2 ?_⟩
  intro c
  rw [cycleClosure_selectedCycles_rep reps distinct]
  have heq : choiceMask bits = choiceMask (fun c => decide (cycleClosure (models i).cycles
      (renames p (some (reps c).1)) (renames p (some (reps c).2.1))
      (renames p (some (reps c).2.2)))) := he.symm.trans (hprofiles i p).symm
  have hb := congrArg (fun code => bitAt code c) heq
  simp only [bitAt_choiceMask] at hb
  rw [hb, decide_eq_true_iff]



namespace Code

/-- Interpret a cycle slot: `0` is false, `1` is true, and `i + 2` is cycle variable `i`. -/
def cycleWord (r slot : ℕ) : ℕ :=
  if slot = 0 then 0 else if slot = 1 then truthOnes (2 ^ r) else truthColumn r (slot - 2)

/-- The bit of a cycle slot is its truth value on the specified assignment. -/
theorem bitAt_cycleWord {r slot mask : ℕ} (hs : slot < r + 2) (hm : mask < 2 ^ r) :
    bitAt (cycleWord r slot) mask = true ↔
      slot = 1 ∨ ∃ i : Fin r, slot = i.val + 2 ∧ bitAt mask i = true := by
  by_cases h0 : slot = 0
  · subst slot
    simp [cycleWord, bitAt]
  by_cases h1 : slot = 1
  · subst slot
    simp [cycleWord, bitAt_truthOnes, hm]
  have hi : slot - 2 < r := by omega
  rw [cycleWord, ite_eq_right h0, ite_eq_right h1, bitAt_truthColumn hi hm]
  constructor
  · intro h
    exact Or.inr ⟨⟨slot - 2, hi⟩, by dsimp; omega, h⟩
  · rintro (h | ⟨i, he, hb⟩)
    · exact (h1 h).elim
    · have he' : slot - 2 = i := by omega
      simpa only [he'] using hb

end Code

/-- A finite slot lookup identifies the identity cycles and the distinct diversity-cycle orbits. -/
def CycleSlots (reps : Fin r → Cycle j k) (slots : ℕ → ℕ → ℕ → ℕ) : Prop :=
  ∀ x y z : Atom j k,
    slots x.code y.code z.code < r + 2 ∧
    (slots x.code y.code z.code = 1 ↔
      (x = none ∧ y = z) ∨ (y = none ∧ x = z) ∨ (z = none ∧ y = x.converse)) ∧
    ∀ i : Fin r, slots x.code y.code z.code = i.val + 2 ↔
      (x, y, z) ∈ cycleOrbit (reps i)

instance (reps : Fin r → Cycle j k) (slots : ℕ → ℕ → ℕ → ℕ) :
    Decidable (CycleSlots reps slots) := by
  unfold CycleSlots
  infer_instance

/-- Verified cycle slots supply the truth-word interpretation needed by catalogue certificates. -/
theorem bitAt_cycleWord_of_slots (reps : Fin r → Cycle j k)
    (slots : ℕ → ℕ → ℕ → ℕ) (hs : CycleSlots reps slots)
    {mask : ℕ} (hm : mask < 2 ^ r) (x y z : Atom j k) :
    bitAt (cycleWord r (slots x.code y.code z.code)) mask = true ↔
      cycleClosure (selectedCycles reps (fun i => bitAt mask i)) x y z := by
  rw [bitAt_cycleWord (hs x y z).1 hm, (hs x y z).2.1, cycleClosure_selectedCycles]
  simp only [(hs x y z).2.2, or_assoc, and_comm]

end Cslib.RelationAlgebra
