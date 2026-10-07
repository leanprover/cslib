/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.FastCatalogueProfiles

/-!
# Constraints for certified relation-algebra search

Associativity is an equality between disjunctions of conjunctions of cycle variables.
Each conjunction is stored as a small natural-number mask. Evaluating these expressions
on a partial assignment detects contradictions and constraints satisfied by every completion,
as in Jipsen's `findra3.p` and `findra4.p` enumeration programs.

The masks here have one bit per cycle variable, rather than one bit per assignment.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Search

/-- Every set bit of `small` is also set in `large`. -/
def MaskSubset (small large : ℕ) : Prop := small &&& large = small

theorem MaskSubset.trans {a b c : ℕ} (hab : MaskSubset a b) (hbc : MaskSubset b c) :
    MaskSubset a c := by
  unfold MaskSubset at *
  calc
    a &&& c = (a &&& b) &&& c := by rw [hab]
    _ = a &&& (b &&& c) := Nat.and_assoc _ _ _
    _ = a := by rw [hbc, hab]

theorem maskSubset_iff {a b : ℕ} :
    MaskSubset a b ↔ ∀ i, a.testBit i = true → b.testBit i = true := by
  constructor
  · intro h i hi
    have := congrArg (fun n : ℕ => n.testBit i) h
    simpa [Nat.testBit_and, hi] using this
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_and]
    cases hi : a.testBit i
    · simp
    · simp [h i hi]

theorem maskSubset_or {a b mask : ℕ} :
    MaskSubset (a ||| b) mask ↔ MaskSubset a mask ∧ MaskSubset b mask := by
  simp only [maskSubset_iff, Nat.testBit_or, Bool.or_eq_true]
  constructor
  · intro h
    exact ⟨fun i hi => h i (Or.inl hi), fun i hi => h i (Or.inr hi)⟩
  · rintro ⟨ha, hb⟩ i (hi | hi)
    · exact ha i hi
    · exact hb i hi

theorem maskSubset_singleton {i mask : ℕ} :
    MaskSubset (1 <<< i) mask ↔ Code.bitAt mask i = true := by
  rw [Code.bitAt_eq_testBit, maskSubset_iff]
  simp [Nat.one_shiftLeft, Nat.testBit_two_pow]

/-- A positive Boolean expression in disjunctive normal form. The empty mask is `true`. -/
abbrev Dnf := List ℕ

/-- Structural equality using primitive numeric comparisons during kernel reduction. -/
def Dnf.beq : Dnf → Dnf → Bool
  | [], [] => true
  | a :: as, b :: bs => Nat.beq a b && beq as bs
  | _, _ => false

theorem Dnf.beq_eq_true (a b : Dnf) : a.beq b = true ↔ a = b := by
  induction a generalizing b with
  | nil => cases b <;> simp [beq]
  | cons a as ih => cases b <;> simp [beq, ih, Nat.beq_eq]

/-- Evaluate the disjunction of the monomials in a DNF. -/
def Dnf.eval (terms : Dnf) (mask : ℕ) : Bool :=
  terms.any fun term => Nat.beq (Nat.land term mask) term

/-- A term remains possible exactly when none of its required variables is excluded. -/
def Dnf.possible (terms : Dnf) (off : ℕ) : Bool :=
  terms.any fun term => Nat.beq (Nat.land term off) 0

theorem Dnf.eval_eq_true {terms : Dnf} {mask : ℕ} :
    terms.eval mask = true ↔ ∃ term ∈ terms, MaskSubset term mask := by
  simp [eval, List.any_eq_true, MaskSubset]

theorem Dnf.possible_eq_true {terms : Dnf} {off : ℕ} :
    terms.possible off = true ↔ ∃ term ∈ terms, term &&& off = 0 := by
  simp [possible, List.any_eq_true]

theorem Dnf.eval_mono {terms : Dnf} {on mask : ℕ} (h : MaskSubset on mask)
    (ht : terms.eval on = true) : terms.eval mask = true := by
  obtain ⟨term, hm, ht⟩ := eval_eq_true.mp ht
  exact eval_eq_true.mpr ⟨term, hm, ht.trans h⟩

theorem Dnf.possible_of_eval {terms : Dnf} {off mask : ℕ}
    (hoff : mask &&& off = 0) (ht : terms.eval mask = true) :
    terms.possible off = true := by
  obtain ⟨term, hm, ht⟩ := eval_eq_true.mp ht
  refine possible_eq_true.mpr ⟨term, hm, ?_⟩
  calc
    term &&& off = (term &&& mask) &&& off := by rw [ht]
    _ = term &&& (mask &&& off) := Nat.and_assoc _ _ _
    _ = 0 := by rw [hoff]; simp

theorem Dnf.eval_false_of_impossible {terms : Dnf} {off mask : ℕ}
    (hoff : mask &&& off = 0) (ht : terms.possible off = false) :
    terms.eval mask = false := by
  cases he : terms.eval mask
  · rfl
  · have := possible_of_eval hoff he
    simp [ht] at this

/-- Insert a term into a sorted list, removing duplicates with primitive comparisons. -/
def Dnf.insert (term : ℕ) : Dnf → Dnf
  | [] => [term]
  | x :: xs =>
    if Nat.ble term x then
      if Nat.beq term x then x :: xs else term :: x :: xs
    else x :: insert term xs

theorem Dnf.mem_insert (value term : ℕ) (terms : Dnf) :
    value ∈ insert term terms ↔ value = term ∨ value ∈ terms := by
  induction terms with
  | nil => simp [insert]
  | cons x xs ih =>
    simp only [insert]
    split
    · split
      · rename_i h
        have he : term = x := Nat.eq_of_beq_eq_true h
        simp [he]
      · simp only [List.mem_cons]
    · simp only [List.mem_cons, ih]
      tauto

/-- Sort and deduplicate the small term lists used in atomic equations. -/
def Dnf.sort : Dnf → Dnf
  | [] => []
  | x :: xs => insert x (sort xs)

theorem Dnf.mem_sort (value : ℕ) (terms : Dnf) : value ∈ sort terms ↔ value ∈ terms := by
  induction terms with
  | nil => rfl
  | cons x xs ih => simp only [sort, mem_insert, ih, List.mem_cons]

/-- Canonicalize a DNF without enumerating assignments or using opaque library computations. -/
def Dnf.normalize (terms : Dnf) : Dnf :=
  if terms.any (fun term => Nat.beq term 0) then [0] else sort terms

theorem Dnf.eval_normalize (terms : Dnf) (mask : ℕ) :
    terms.normalize.eval mask = terms.eval mask := by
  apply Bool.eq_iff_iff.mpr
  unfold normalize
  split
  · rename_i h
    have hm : 0 ∈ terms := by simpa [List.any_eq_true, Nat.beq_eq] using h
    have ht : terms.eval mask = true := eval_eq_true.mpr ⟨0, hm, by simp [MaskSubset]⟩
    rw [ht]
    simp [eval]
  · simp [eval_eq_true, mem_sort]

/-- One atomic associativity equation. -/
structure Equation where
  /-- Witnesses for the left association. -/
  left : Dnf
  /-- Witnesses for the right association. -/
  right : Dnf
  deriving DecidableEq, BEq

/-- Evaluate an equation on a complete cycle assignment. -/
def Equation.eval (eqn : Equation) (mask : ℕ) : Bool :=
  eqn.left.eval mask == eqn.right.eval mask

/-- A definitely true side and an impossible opposite side refute every completion. -/
def Equation.conflict (eqn : Equation) (on off : ℕ) : Bool :=
  (eqn.left.eval on && !eqn.right.possible off) ||
    (eqn.right.eval on && !eqn.left.possible off)

/-- Both sides are definitely true, or both are impossible. -/
def Equation.settled (eqn : Equation) (on off : ℕ) : Bool :=
  (eqn.left.eval on && eqn.right.eval on) ||
    (!eqn.left.possible off && !eqn.right.possible off)

theorem Equation.eval_false_of_conflict {eqn : Equation} {on off mask : ℕ}
    (hon : MaskSubset on mask) (hoff : mask &&& off = 0)
    (h : eqn.conflict on off = true) : eqn.eval mask = false := by
  simp only [conflict, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h
  rcases h with ⟨hl, hr⟩ | ⟨hr, hl⟩
  · simp [eval, Dnf.eval_mono hon hl, Dnf.eval_false_of_impossible hoff hr]
  · simp [eval, Dnf.eval_mono hon hr, Dnf.eval_false_of_impossible hoff hl]

theorem Equation.eval_true_of_settled {eqn : Equation} {on off mask : ℕ}
    (hon : MaskSubset on mask) (hoff : mask &&& off = 0)
    (h : eqn.settled on off = true) : eqn.eval mask = true := by
  simp only [settled, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h
  rcases h with ⟨hl, hr⟩ | ⟨hl, hr⟩
  · simp [eval, Dnf.eval_mono hon hl, Dnf.eval_mono hon hr]
  · simp [eval, Dnf.eval_false_of_impossible hoff hl, Dnf.eval_false_of_impossible hoff hr]

/-- Evaluate a cycle slot: zero is false, one is true, and `i + 2` names variable `i`. -/
def slotEval (mask slot : ℕ) : Bool :=
  if slot = 0 then false else if slot = 1 then true else Code.bitAt mask (slot - 2)

/-- Encode one cycle slot as a monomial, omitting the identically false slot. -/
def slotTerm (slot : ℕ) : Option ℕ :=
  if slot = 0 then none else if slot = 1 then some 0 else some (1 <<< (slot - 2))

/-- The conjunction of two cycle slots as a DNF with at most one term. -/
def pairTerms (a b : ℕ) : Dnf :=
  match slotTerm a, slotTerm b with
  | some x, some y => [x ||| y]
  | _, _ => []

theorem slotTerm_spec {slot mask : ℕ} :
    (∃ term, slotTerm slot = some term ∧ MaskSubset term mask) ↔
      slotEval mask slot = true := by
  unfold slotTerm slotEval
  split
  · simp
  · split
    · simp [MaskSubset]
    · simp [maskSubset_singleton]

theorem pairTerms_eval (a b mask : ℕ) :
    (pairTerms a b).eval mask = (slotEval mask a && slotEval mask b) := by
  apply Bool.eq_iff_iff.mpr
  rw [Bool.and_eq_true, ← slotTerm_spec, ← slotTerm_spec]
  unfold pairTerms
  cases ha : slotTerm a <;> cases hb : slotTerm b <;>
    simp [Dnf.eval_eq_true, maskSubset_or]

theorem Dnf.eval_flatMap {α : Type*} (xs : List α) (f : α → Dnf) (mask : ℕ) :
    Dnf.eval (xs.flatMap f) mask = xs.any (fun x => (f x).eval mask) := by
  simp [eval, List.any_flatMap]

/-- Compile an atomic associativity equation from the finite slot lookup. -/
def compileEquation (n : ℕ) (slots : ℕ → ℕ → ℕ → ℕ) (quad : Code.Quadruple) : Equation :=
  let (a, b, c, d) := quad
  ⟨Dnf.normalize ((List.range n).flatMap fun t => pairTerms (slots a b t) (slots t c d)),
    Dnf.normalize ((List.range n).flatMap fun t => pairTerms (slots b c t) (slots a t d))⟩

theorem compileEquation_eval (n : ℕ) (slots : ℕ → ℕ → ℕ → ℕ)
    (a b c d mask : ℕ) :
    (compileEquation n slots (a, b, c, d)).eval mask = true ↔
      ((∃ t < n, slotEval mask (slots a b t) = true ∧
          slotEval mask (slots t c d) = true) ↔
        ∃ t < n, slotEval mask (slots b c t) = true ∧
          slotEval mask (slots a t d) = true) := by
  simp only [compileEquation, Equation.eval, Dnf.eval_normalize, beq_iff_eq]
  rw [Bool.eq_iff_iff]
  simp only [Dnf.eval_flatMap, pairTerms_eval, List.any_eq_true, List.mem_range,
    Bool.and_eq_true]

theorem slotEval_eq_cycleWord {r slot mask : ℕ} (hs : slot < r + 2)
    (hm : mask < 2 ^ r) :
    slotEval mask slot = Code.bitAt (Code.cycleWord r slot) mask := by
  unfold slotEval Code.cycleWord
  split
  · simp [Code.bitAt]
    rfl
  · split
    · simp [Code.bitAt_truthOnes, hm]
    · symm
      exact Code.bitAt_truthColumn (by omega) hm

/-- A compiled slot is the corresponding semantic cycle, for every assignment. -/
theorem slotEval_spec {j k r : ℕ} (reps : Fin r → Cycle j k)
    (slots : ℕ → ℕ → ℕ → ℕ) (hs : CycleSlots reps slots)
    {mask : ℕ} (hm : mask < 2 ^ r) (a b c : Atom j k) :
    slotEval mask (slots a.code b.code c.code) = true ↔
      cycleClosure (selectedCycles reps (fun i => Code.bitAt mask i)) a b c := by
  rw [slotEval_eq_cycleWord (hs a b c).1 hm]
  exact bitAt_cycleWord_of_slots reps slots hs hm a b c

/-- All compiled atomic equations characterize associativity exactly. -/
theorem associative_iff_compiled {j k r : ℕ} (reps : Fin r → Cycle j k)
    (slots : ℕ → ℕ → ℕ → ℕ) (hs : CycleSlots reps slots)
    {mask : ℕ} (hm : mask < 2 ^ r) :
    AtomCompositionAssociative (selectedCycles reps (fun i => Code.bitAt mask i)) ↔
      ∀ a < atomCount j k, ∀ b < atomCount j k, ∀ c < atomCount j k,
        ∀ d < atomCount j k,
        (compileEquation (atomCount j k) slots (a, b, c, d)).eval mask = true := by
  have hex (a b c d : Atom j k) :
      (∃ t < atomCount j k, slotEval mask (slots a.code b.code t) = true ∧
        slotEval mask (slots t c.code d.code) = true) ↔
      ∃ t, cycleClosure (selectedCycles reps (fun i => Code.bitAt mask i)) a b t ∧
        cycleClosure (selectedCycles reps (fun i => Code.bitAt mask i)) t c d := by
    constructor
    · rintro ⟨t, ht, h1, h2⟩
      obtain ⟨t, rfl⟩ := Atom.exists_code ht
      exact ⟨t, (slotEval_spec reps slots hs hm _ _ _).mp h1,
        (slotEval_spec reps slots hs hm _ _ _).mp h2⟩
    · rintro ⟨t, h1, h2⟩
      exact ⟨t.code, t.code_lt, (slotEval_spec reps slots hs hm _ _ _).mpr h1,
        (slotEval_spec reps slots hs hm _ _ _).mpr h2⟩
  have hex' (a b c d : Atom j k) :
      (∃ t < atomCount j k, slotEval mask (slots b.code c.code t) = true ∧
        slotEval mask (slots a.code t d.code) = true) ↔
      ∃ t, cycleClosure (selectedCycles reps (fun i => Code.bitAt mask i)) b c t ∧
        cycleClosure (selectedCycles reps (fun i => Code.bitAt mask i)) a t d := by
    constructor
    · rintro ⟨t, ht, h1, h2⟩
      obtain ⟨t, rfl⟩ := Atom.exists_code ht
      exact ⟨t, (slotEval_spec reps slots hs hm _ _ _).mp h1,
        (slotEval_spec reps slots hs hm _ _ _).mp h2⟩
    · rintro ⟨t, h1, h2⟩
      exact ⟨t.code, t.code_lt, (slotEval_spec reps slots hs hm _ _ _).mpr h1,
        (slotEval_spec reps slots hs hm _ _ _).mpr h2⟩
  constructor
  · intro ha a ha' b hb c hc d hd
    obtain ⟨a, rfl⟩ := Atom.exists_code ha'
    obtain ⟨b, rfl⟩ := Atom.exists_code hb
    obtain ⟨c, rfl⟩ := Atom.exists_code hc
    obtain ⟨d, rfl⟩ := Atom.exists_code hd
    rw [compileEquation_eval, hex, hex']
    exact ha a b c d
  · intro h a b c d
    have := h a.code a.code_lt b.code b.code_lt c.code c.code_lt d.code d.code_lt
    rwa [compileEquation_eval, hex, hex'] at this

/-- Compare two equations, allowing their sides to be exchanged. -/
def Equation.same (a b : Equation) : Bool :=
  (a.left.beq b.left && a.right.beq b.right) ||
    (a.left.beq b.right && a.right.beq b.left)

theorem Equation.eval_eq_of_same {a b : Equation} (h : a.same b = true) (mask : ℕ) :
    a.eval mask = b.eval mask := by
  simp only [same, Bool.or_eq_true, Bool.and_eq_true, Dnf.beq_eq_true] at h
  rcases h with ⟨hl, hr⟩ | ⟨hl, hr⟩
  · simp [eval, hl, hr]
  · simp [eval, hl, hr, BEq.comm]

/-- Check that every supplied equation is an actual atomic associativity equation. -/
def sourcesCheck (n q : ℕ) (slots : ℕ → ℕ → ℕ → ℕ)
    (equations : ℕ → Equation) (sources : ℕ → Code.Quadruple) : Bool :=
  Code.allBelow (fun i =>
    let (a, b, c, d) := sources i
    Nat.blt a n && Nat.blt b n && Nat.blt c n && Nat.blt d n &&
      (equations i).same (compileEquation n slots (a, b, c, d))) q

/-- Check coverage of all atomic equations, including those involving the identity. -/
def equationsCoverCheck (n q : ℕ) (slots : ℕ → ℕ → ℕ → ℕ)
    (equations : ℕ → Equation) (cover : ℕ → ℕ → ℕ → ℕ → ℕ) : Bool :=
  Code.allBelow (fun a => Code.allBelow (fun b => Code.allBelow (fun c =>
    Code.allBelow (fun d =>
      let eqn := compileEquation n slots (a, b, c, d)
      eqn.left.beq eqn.right ||
        (Nat.blt (cover a b c d) q && (equations (cover a b c d)).same eqn)) n) n) n) n

/-- A checked equation list is equivalent to full atomic associativity. -/
theorem associative_iff_equations {j k r q : ℕ} (reps : Fin r → Cycle j k)
    (slots : ℕ → ℕ → ℕ → ℕ) (hs : CycleSlots reps slots)
    (equations : ℕ → Equation) (sources : ℕ → Code.Quadruple)
    (cover : ℕ → ℕ → ℕ → ℕ → ℕ)
    (hsource : sourcesCheck (atomCount j k) q slots equations sources = true)
    (hcover : equationsCoverCheck (atomCount j k) q slots equations cover = true)
    {mask : ℕ} (hm : mask < 2 ^ r) :
    AtomCompositionAssociative (selectedCycles reps (fun i => Code.bitAt mask i)) ↔
      Code.allBelow (fun i => (equations i).eval mask) q = true := by
  rw [associative_iff_compiled reps slots hs hm]
  constructor
  · intro h
    apply Code.allBelow_eq_true.mpr
    intro i hi
    have hh := Code.allBelow_eq_true.mp hsource i hi
    simp only [Bool.and_eq_true, Nat.blt_eq] at hh
    rw [Equation.eval_eq_of_same hh.2]
    exact h (sources i).1 hh.1.1.1.1 (sources i).2.1 hh.1.1.1.2
      (sources i).2.2.1 hh.1.1.2 (sources i).2.2.2 hh.1.2
  · intro h a ha b hb c hc d hd
    have hh := Code.allBelow_eq_true.mp (Code.allBelow_eq_true.mp
      (Code.allBelow_eq_true.mp (Code.allBelow_eq_true.mp hcover a ha) b hb) c hc) d hd
    simp only [Bool.or_eq_true, Bool.and_eq_true, Dnf.beq_eq_true, Nat.blt_eq] at hh
    rcases hh with ht | ⟨hi, he⟩
    · simp [Equation.eval, ht]
    · rw [← Equation.eval_eq_of_same he]
      exact Code.allBelow_eq_true.mp h _ hi

end Cslib.RelationAlgebra.Search
