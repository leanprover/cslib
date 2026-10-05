/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Cycles

/-!
# Numeric codes for finite cycle tables

Finite facts about a cycle table can be proved by evaluating a Boolean checker in the kernel,
provided that the checker is cheap to reduce. The kernel accelerates arithmetic and bitwise
operations on natural-number literals, but reduces type-class instances, `Finset`s, and
structural recursion comparatively slowly. This file therefore encodes atoms as natural numbers
and the closure of a cycle table as the bits of one natural number, and it supplies loops
defined directly by `Nat.rec`. A checker is proved correct once; each concrete table is then
handled by `decide +kernel` on a closed Boolean term.

The code of a table is assembled from the six table positions of each listed cycle, so the
kernel visits the finset of cycles only once.

## Main definitions

* `Atom.code`: atoms numbered from `0` (the identity) to `atomCount j k - 1`.
* `orbitCode`, `identityCode`: the table positions of a Peircean orbit and of the identity cycles.
* `tableCode`: the closure of a cycle table, packed into the bits of one number.
* `Code.assocCheck`: a bitmask associativity checker.

## Main statements

* `bitAt_tableCode`: the bits of `tableCode` decide `cycleClosure`.
* `assocCheck_iff`: on an encoded table, the checker decides `AtomCompositionAssociative`.
* `atomCompositionAssociative_of_assocCheck`: associativity from one evaluation of the checker.
-/

@[expose] public section

namespace Cslib.RelationAlgebra

namespace Code

/-! ### Kernel-friendly loops -/

/-- `Nat.testBit`, phrased with primitive operations that the kernel evaluates directly. -/
def bitAt (m i : ℕ) : Bool := Nat.beq (Nat.land (Nat.shiftRight m i) 1) 1

theorem bitAt_eq_testBit (m i : ℕ) : bitAt m i = m.testBit i := by
  have h1 : Nat.land (Nat.shiftRight m i) 1 = (m >>> i) % 2 := Nat.and_one_is_mod _
  rw [bitAt, Nat.testBit, h1, Nat.one_and_eq_mod_two]
  rcases Nat.mod_two_eq_zero_or_one (m >>> i) with h | h <;> rw [h] <;> rfl

/-- Decide `∀ i < n, p i`, testing indices from `n - 1` down to `0`. -/
def allBelow (p : ℕ → Bool) (n : ℕ) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun i acc => p i && acc) n

/-- Decide `∃ i < n, p i`, testing indices from `n - 1` down to `0`. -/
def anyBelow (p : ℕ → Bool) (n : ℕ) : Bool :=
  Nat.rec (motive := fun _ => Bool) false (fun i acc => p i || acc) n

/-- The number whose bits below `n` are given by `p`. -/
def bitsOf (p : ℕ → Bool) (n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0
    (fun i acc => cond (p i) (Nat.lor acc (Nat.shiftLeft 1 i)) acc) n

/-- The bitwise union of `f i` over `i < n`. -/
def orBelow (f : ℕ → ℕ) (n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun i acc => Nat.lor (f i) acc) n

@[simp]
theorem allBelow_zero (p : ℕ → Bool) : allBelow p 0 = true := rfl

theorem allBelow_succ (p : ℕ → Bool) (n : ℕ) : allBelow p (n + 1) = (p n && allBelow p n) := rfl

@[simp]
theorem anyBelow_zero (p : ℕ → Bool) : anyBelow p 0 = false := rfl

theorem anyBelow_succ (p : ℕ → Bool) (n : ℕ) : anyBelow p (n + 1) = (p n || anyBelow p n) := rfl

theorem bitsOf_succ (p : ℕ → Bool) (n : ℕ) :
    bitsOf p (n + 1) = cond (p n) (bitsOf p n ||| 1 <<< n) (bitsOf p n) := rfl

theorem orBelow_succ (f : ℕ → ℕ) (n : ℕ) : orBelow f (n + 1) = (f n ||| orBelow f n) := rfl

theorem allBelow_eq_true {p : ℕ → Bool} {n : ℕ} :
    allBelow p n = true ↔ ∀ i < n, p i = true := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [allBelow_succ, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨hn, h⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact h i hi
      · exact hn
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun i hi => h i (Nat.lt_succ_of_lt hi)⟩

theorem anyBelow_eq_true {p : ℕ → Bool} {n : ℕ} :
    anyBelow p n = true ↔ ∃ i < n, p i = true := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [anyBelow_succ, Bool.or_eq_true, ih]
    constructor
    · rintro (h | ⟨i, hi, h⟩)
      · exact ⟨n, Nat.lt_succ_self n, h⟩
      · exact ⟨i, Nat.lt_succ_of_lt hi, h⟩
    · rintro ⟨i, hi, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact Or.inr ⟨i, hi, h⟩
      · exact Or.inl h

/-- Checkers phrase an implication `p → q` as `!p || q`. -/
theorem not_or_eq_true {p q : Bool} : (!p || q) = true ↔ (p = true → q = true) := by
  cases p <;> cases q <;> simp

theorem testBit_bitsOf (p : ℕ → Bool) (n i : ℕ) :
    (bitsOf p n).testBit i = (decide (i < n) && p i) := by
  induction n with
  | zero => simp [bitsOf]
  | succ n ih =>
    rw [bitsOf_succ]
    cases hp : p n
    · simp only [Bool.cond_false, ih]
      by_cases hi : i = n
      · subst hi
        simp [hp]
      · have : i < n + 1 ↔ i < n := by omega
        simp [this]
    · simp only [Bool.cond_true, Nat.testBit_or, ih, Nat.one_shiftLeft, Nat.testBit_two_pow]
      by_cases hi : i = n
      · subst hi
        simp [hp]
      · have : i < n + 1 ↔ i < n := by omega
        simp [this, Ne.symm hi]

theorem bitAt_bitsOf {p : ℕ → Bool} {n i : ℕ} (hi : i < n) : bitAt (bitsOf p n) i = p i := by
  simp [bitAt_eq_testBit, testBit_bitsOf, hi]

theorem bitsOf_lt (p : ℕ → Bool) (n : ℕ) : bitsOf p n < 2 ^ n := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  simp [testBit_bitsOf, Nat.not_lt.mpr hi]

theorem testBit_orBelow (f : ℕ → ℕ) (n i : ℕ) :
    (orBelow f n).testBit i = true ↔ ∃ u < n, (f u).testBit i = true := by
  induction n with
  | zero => simp [orBelow]
  | succ n ih =>
    rw [orBelow_succ, Nat.testBit_or, Bool.or_eq_true, ih]
    constructor
    · rintro (h | ⟨u, hu, h⟩)
      · exact ⟨n, Nat.lt_succ_self n, h⟩
      · exact ⟨u, Nat.lt_succ_of_lt hu, h⟩
    · rintro ⟨u, hu, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hu with hu | rfl
      · exact Or.inr ⟨u, hu, h⟩
      · exact Or.inl h

/-- The bits of a number below `2 ^ n` vanish from position `n` on. -/
theorem testBit_eq_false_of_lt {m n i : ℕ} (hm : m < 2 ^ n) (hi : n ≤ i) :
    m.testBit i = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le hm (Nat.pow_le_pow_right (by decide) hi))

/-- Numbers below `2 ^ n` are equal when their first `n` bits agree. -/
theorem eq_of_testBit_eq_of_lt {m m' n : ℕ} (hm : m < 2 ^ n) (hm' : m' < 2 ^ n)
    (h : ∀ i < n, m.testBit i = m'.testBit i) : m = m' := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < n
  · exact h i hi
  · rw [testBit_eq_false_of_lt hm (by omega), testBit_eq_false_of_lt hm' (by omega)]

/-! ### Triples of codes -/

/-- The position of a triple of codes in a table over `n` atoms. -/
def index (n x y z : ℕ) : ℕ := Nat.add (Nat.mul (Nat.add (Nat.mul x n) y) n) z

theorem index_eq (n x y z : ℕ) : index n x y z = (x * n + y) * n + z := rfl

theorem index_lt {n x y z : ℕ} (hx : x < n) (hy : y < n) (hz : z < n) :
    index n x y z < n * n * n := by
  rw [index_eq]
  have h1 : x * n + y < n * n :=
    calc x * n + y < x * n + n := by omega
      _ = (x + 1) * n := (Nat.succ_mul x n).symm
      _ ≤ n * n := Nat.mul_le_mul_right n hx
  calc (x * n + y) * n + z < (x * n + y) * n + n := by omega
    _ = (x * n + y + 1) * n := (Nat.succ_mul _ n).symm
    _ ≤ n * n * n := Nat.mul_le_mul_right n h1

theorem index_mod {n x y z : ℕ} (hz : z < n) : index n x y z % n = z := by
  rw [index_eq, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hz]

theorem index_div {n x y z : ℕ} (hz : z < n) : index n x y z / n = x * n + y := by
  rw [index_eq, Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hz,
    Nat.zero_add]

theorem index_div_mod {n x y z : ℕ} (hy : y < n) (hz : z < n) :
    index n x y z / n % n = y := by
  rw [index_div hz, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hy]

theorem index_div_div {n x y z : ℕ} (hy : y < n) (hz : z < n) :
    index n x y z / n / n = x := by
  rw [index_div hz, Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hy,
    Nat.zero_add]

theorem index_injective {n x y z x' y' z' : ℕ} (hy : y < n) (hz : z < n) (hy' : y' < n)
    (hz' : z' < n) (h : index n x y z = index n x' y' z') : x = x' ∧ y = y' ∧ z = z' := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← index_div_div hy hz (x := x), h, index_div_div hy' hz']
  · rw [← index_div_mod hy hz (x := x), h, index_div_mod hy' hz']
  · rw [← index_mod hz (x := x) (y := y), h, index_mod hz']

/-- The `n`-bit field of `m` starting at position `i`. -/
def field (m i n : ℕ) : ℕ := Nat.mod (Nat.shiftRight m i) (Nat.pow 2 n)

theorem field_eq (m i n : ℕ) : field m i n = (m >>> i) % 2 ^ n := rfl

theorem testBit_field (m i n b : ℕ) :
    (field m i n).testBit b = (decide (b < n) && m.testBit (i + b)) := by
  rw [field_eq, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]

theorem field_lt (m i n : ℕ) : field m i n < 2 ^ n := Nat.mod_lt _ (Nat.two_pow_pos n)

end Code

open Code

/-! ### Atom codes -/

variable {j k : ℕ}

/-- The number of atoms of an integral algebra with signature `⟨1, j, k⟩`. -/
abbrev atomCount (j k : ℕ) : ℕ := j + 2 * k + 1

/-- Number the atoms: `0` is the identity, then the symmetric atoms, then the converse pairs. -/
def Atom.code : Atom j k → ℕ
  | none => 0
  | some (.inl i) => i.val + 1
  | some (.inr (i, b)) => j + 1 + 2 * i.val + b.toNat

/-- The atom with a given code; out-of-range codes denote the identity. -/
def Atom.ofCode (c : ℕ) : Atom j k :=
  if h0 : c = 0 then none
  else if h : c ≤ j then some (.inl ⟨c - 1, by omega⟩)
  else if h' : c < j + 2 * k + 1 then
    some (.inr (⟨(c - (j + 1)) / 2, by omega⟩, decide ((c - (j + 1)) % 2 = 1)))
  else none

theorem Atom.code_lt (x : Atom j k) : x.code < atomCount j k := by
  change x.code < j + 2 * k + 1
  rcases x with _ | i | ⟨i, b⟩
  · simp [Atom.code]
  · have := i.isLt
    simp only [Atom.code]
    omega
  · have := i.isLt
    simp only [Atom.code]
    cases b <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega

@[simp]
theorem Atom.ofCode_code (x : Atom j k) : Atom.ofCode x.code = x := by
  rcases x with _ | i | ⟨i, b⟩
  · rfl
  · have hi := i.isLt
    change Atom.ofCode (i.val + 1) = _
    rw [Atom.ofCode, dite_eq_right (by omega), dite_eq_left (by omega)]
    simp only [Option.some.injEq, Sum.inl.injEq, Fin.ext_iff]
    omega
  · have hi := i.isLt
    change Atom.ofCode (j + 1 + 2 * i.val + b.toNat) = _
    have hb := Bool.toNat_le b
    rw [Atom.ofCode, dite_eq_right (by omega), dite_eq_right (by omega),
      dite_eq_left (by omega)]
    simp only [Option.some.injEq, Sum.inr.injEq, Prod.mk.injEq, Fin.ext_iff]
    cases b
    · simp only [Bool.toNat_false, decide_eq_false_iff_not]
      omega
    · simp only [Bool.toNat_true, decide_eq_true_eq]
      omega

theorem Atom.code_injective : Function.Injective (Atom.code : Atom j k → ℕ) := by
  intro x y h
  rw [← Atom.ofCode_code x, h, Atom.ofCode_code]

@[simp]
theorem Atom.code_inj {x y : Atom j k} : x.code = y.code ↔ x = y :=
  Atom.code_injective.eq_iff

@[simp]
theorem Atom.code_none : Atom.code (none : Atom j k) = 0 := rfl

theorem Atom.code_eq_zero {x : Atom j k} : x.code = 0 ↔ x = none := by
  rw [← Atom.code_none, Atom.code_inj]

theorem Atom.code_ofCode {c : ℕ} (hc : c < atomCount j k) :
    (Atom.ofCode c : Atom j k).code = c := by
  unfold Atom.ofCode
  split_ifs with h0 h1
  · exact h0.symm
  · simp only [Atom.code]
    omega
  · simp only [Atom.code]
    by_cases hb : (c - (j + 1)) % 2 = 1
    · simp only [hb, decide_true, Bool.toNat_true]
      omega
    · simp only [hb, decide_false, Bool.toNat_false]
      omega

/-- Every code below `atomCount j k` is the code of an atom. -/
theorem Atom.exists_code {c : ℕ} (hc : c < atomCount j k) : ∃ x : Atom j k, x.code = c :=
  ⟨Atom.ofCode c, Atom.code_ofCode hc⟩

namespace Code

/-- Converse on codes. -/
def conv (j c : ℕ) : ℕ :=
  if c ≤ j then c else if (c - (j + 1)) % 2 = 0 then c + 1 else c - 1

end Code

@[simp]
theorem Atom.code_converse (x : Atom j k) : (Atom.converse x).code = conv j x.code := by
  rcases x with _ | i | ⟨i, b⟩
  · change 0 = conv j 0
    rw [conv, ite_eq_left (Nat.zero_le j)]
  · have hi := i.isLt
    change i.val + 1 = conv j (i.val + 1)
    rw [conv, ite_eq_left (by omega)]
  · change j + 1 + 2 * i.val + (!b).toNat = conv j (j + 1 + 2 * i.val + b.toNat)
    rw [conv, ite_eq_right (by omega)]
    cases b
    · rw [ite_eq_left (by simp only [Bool.toNat_false]; omega)]
      simp
    · rw [ite_eq_right (by simp only [Bool.toNat_true]; omega)]
      simp

/-! ### Table codes -/

/-- A decidable ternary relation on atoms: bit `index n x y z` records `P x y z`. -/
def tripleCode (P : Atom j k → Atom j k → Atom j k → Prop) [∀ x y z, Decidable (P x y z)] :
    ℕ :=
  bitsOf (fun i => decide (P
    (Atom.ofCode (i / atomCount j k / atomCount j k))
    (Atom.ofCode (i / atomCount j k % atomCount j k))
    (Atom.ofCode (i % atomCount j k))))
    (atomCount j k * atomCount j k * atomCount j k)

theorem bitAt_tripleCode (P : Atom j k → Atom j k → Atom j k → Prop)
    [∀ x y z, Decidable (P x y z)] (x y z : Atom j k) :
    bitAt (tripleCode P) (index (atomCount j k) x.code y.code z.code) = decide (P x y z) := by
  have hx := x.code_lt
  have hy := y.code_lt
  have hz := z.code_lt
  rw [tripleCode, bitAt_bitsOf (index_lt hx hy hz), index_div_div hy hz, index_div_mod hy hz,
    index_mod hz, Atom.ofCode_code, Atom.ofCode_code, Atom.ofCode_code]

theorem index_code_inj {x y z x' y' z' : Atom j k} :
    index (atomCount j k) x.code y.code z.code = index (atomCount j k) x'.code y'.code z'.code ↔
      x' = x ∧ y' = y ∧ z' = z := by
  constructor
  · intro h
    obtain ⟨h1, h2, h3⟩ := index_injective y.code_lt z.code_lt y'.code_lt z'.code_lt h
    exact ⟨(Atom.code_injective h1).symm, (Atom.code_injective h2).symm,
      (Atom.code_injective h3).symm⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

/-- The identity cycles, which belong to every cycle table. -/
def identityCode (j k : ℕ) : ℕ :=
  tripleCode (j := j) (k := k) fun x y z =>
    (x = none ∧ y = z) ∨ (y = none ∧ x = z) ∨ (z = none ∧ y = Atom.converse x)

namespace Code

/-- The table positions of the six Peircean transforms of the code triple `(x, y, z)`. -/
def orbitBits (n j x y z : ℕ) : ℕ :=
  Nat.lor (Nat.shiftLeft 1 (index n x y z)) <|
    Nat.lor (Nat.shiftLeft 1 (index n (conv j x) z y)) <|
      Nat.lor (Nat.shiftLeft 1 (index n z (conv j y) x)) <|
        Nat.lor (Nat.shiftLeft 1 (index n (conv j y) (conv j x) (conv j z))) <|
          Nat.lor (Nat.shiftLeft 1 (index n y (conv j z) (conv j x)))
            (Nat.shiftLeft 1 (index n (conv j z) x (conv j y)))

/-- The bits of a fold of bitwise unions over a finset. -/
theorem testBit_fold_lor {α : Type*} (s : Finset α) (f : α → ℕ) (i : ℕ) :
    (s.fold (fun a b : ℕ => a ||| b) 0 f).testBit i = true ↔ ∃ a ∈ s, (f a).testBit i = true := by
  have h := Finset.fold_op_rel_iff_or (s := s) (op := fun a b : ℕ => a ||| b) (b := 0) (f := f)
    (r := fun i m => m.testBit i = true) (fun {_ _ _} => by simp [Nat.testBit_or]) (c := i)
  simpa using h

end Code

/-- The Peircean orbit of one diversity cycle. -/
def orbitCode (c : Cycle j k) : ℕ :=
  orbitBits (atomCount j k) j (Atom.code (some c.1)) (Atom.code (some c.2.1))
    (Atom.code (some c.2.2))

theorem bitAt_orbitCode (c : Cycle j k) (x y z : Atom j k) :
    bitAt (orbitCode c) (index (atomCount j k) x.code y.code z.code) =
      decide ((x, y, z) ∈ cycleOrbit c) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, orbitCode, bitAt_eq_testBit]
  simp only [orbitBits, Nat.lor_eq, Nat.shiftLeft_eq', Nat.testBit_or, Nat.one_shiftLeft,
    Nat.testBit_two_pow, ← Atom.code_converse, Bool.or_eq_true, decide_eq_true_eq,
    index_code_inj, cycleOrbit, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]

/-- The closure of a cycle table: bit `index n x y z` records `cycleClosure cycles x y z`.
The identity cycles are added to the six table positions of each listed cycle. -/
def tableCode (cycles : Finset (Cycle j k)) : ℕ :=
  Nat.lor (identityCode j k) (cycles.fold (fun a b : ℕ => a ||| b) 0 orbitCode)

theorem bitAt_tableCode (cycles : Finset (Cycle j k)) (x y z : Atom j k) :
    bitAt (tableCode cycles) (index (atomCount j k) x.code y.code z.code) =
      decide (cycleClosure cycles x y z) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, tableCode, bitAt_eq_testBit, Nat.lor_eq,
    Nat.testBit_or, Bool.or_eq_true, ← bitAt_eq_testBit, identityCode, bitAt_tripleCode,
    decide_eq_true_iff, testBit_fold_lor, cycleClosure, or_assoc, or_assoc]
  simp only [← bitAt_eq_testBit, bitAt_orbitCode, decide_eq_true_eq]

/-- A number encodes the closure of `cycles` on atom codes. -/
def EncodesTable (cycles : Finset (Cycle j k)) (t : ℕ) : Prop :=
  ∀ x y z : Atom j k,
    bitAt t (index (atomCount j k) x.code y.code z.code) = decide (cycleClosure cycles x y z)

theorem encodesTable_tableCode (cycles : Finset (Cycle j k)) :
    EncodesTable cycles (tableCode cycles) :=
  bitAt_tableCode cycles

/-- A cycle holds exactly when its position is set in a verified table code. -/
theorem cycleClosure_iff_bitAt {cycles : Finset (Cycle j k)} {t : ℕ}
    (ht : EncodesTable cycles t) (x y z : Atom j k) :
    cycleClosure cycles x y z ↔
      bitAt t (index (atomCount j k) x.code y.code z.code) = true := by
  rw [ht, decide_eq_true_iff]

/-! ### Associativity -/

namespace Code

/-- The `n`-bit mask of the atoms below the product of `x` and `y` in table `t`. -/
def prodMask (n t x y : ℕ) : ℕ := field t (index n x y 0) n

/-- The union of the products `u * c` for the atoms `u` in the mask `s`. -/
def leftMul (n t s c : ℕ) : ℕ := orBelow (fun u => cond (bitAt s u) (prodMask n t u c) 0) n

/-- The union of the products `a * u` for the atoms `u` in the mask `s`. -/
def rightMul (n t a s : ℕ) : ℕ := orBelow (fun u => cond (bitAt s u) (prodMask n t a u) 0) n

/-- Compare `(a * b) * c` with `a * (b * c)` for all atoms. -/
def assocCheck (n t : ℕ) : Bool :=
  allBelow (fun a => allBelow (fun b => allBelow (fun c =>
    Nat.beq (leftMul n t (prodMask n t a b) c) (rightMul n t a (prodMask n t b c))) n) n) n

theorem testBit_prodMask {n t x y z : ℕ} (hz : z < n) :
    (prodMask n t x y).testBit z = t.testBit (index n x y z) := by
  rw [prodMask, testBit_field]
  simp [hz, index_eq]

theorem prodMask_lt (n t x y : ℕ) : prodMask n t x y < 2 ^ n := field_lt _ _ _

theorem orBelow_lt {f : ℕ → ℕ} {n m : ℕ} (h : ∀ u < n, f u < 2 ^ m) : orBelow f n < 2 ^ m := by
  induction n with
  | zero => exact Nat.two_pow_pos m
  | succ n ih =>
    rw [orBelow_succ]
    exact Nat.or_lt_two_pow (h n (Nat.lt_succ_self n))
      (ih fun u hu => h u (Nat.lt_succ_of_lt hu))

theorem leftMul_lt (n t s c : ℕ) : leftMul n t s c < 2 ^ n := by
  refine orBelow_lt fun u _ => ?_
  cases bitAt s u
  · exact Nat.two_pow_pos n
  · exact prodMask_lt n t u c

theorem rightMul_lt (n t a s : ℕ) : rightMul n t a s < 2 ^ n := by
  refine orBelow_lt fun u _ => ?_
  cases bitAt s u
  · exact Nat.two_pow_pos n
  · exact prodMask_lt n t a u

theorem testBit_leftMul {n t s c d : ℕ} :
    (leftMul n t s c).testBit d = true ↔
      ∃ u < n, s.testBit u = true ∧ (prodMask n t u c).testBit d = true := by
  rw [leftMul, testBit_orBelow]
  apply exists_congr
  intro u
  rw [bitAt_eq_testBit]
  cases s.testBit u <;> simp

theorem testBit_rightMul {n t a s d : ℕ} :
    (rightMul n t a s).testBit d = true ↔
      ∃ u < n, s.testBit u = true ∧ (prodMask n t a u).testBit d = true := by
  rw [rightMul, testBit_orBelow]
  apply exists_congr
  intro u
  rw [bitAt_eq_testBit]
  cases s.testBit u <;> simp

end Code

/-- On an encoded table, the bitmask checker decides associativity. -/
theorem assocCheck_iff {cycles : Finset (Cycle j k)} {t : ℕ} (ht : EncodesTable cycles t) :
    assocCheck (atomCount j k) t = true ↔ AtomCompositionAssociative cycles := by
  set n := atomCount j k
  have hbit (x y z : Atom j k) :
      t.testBit (index n x.code y.code z.code) = true ↔ cycleClosure cycles x y z := by
    rw [← bitAt_eq_testBit, ht, decide_eq_true_iff]
  -- Both sides of each associativity instance, as statements about code masks.
  have hleft (a b c d : Atom j k) :
      (leftMul n t (prodMask n t a.code b.code) c.code).testBit d.code = true ↔
        ∃ u, cycleClosure cycles a b u ∧ cycleClosure cycles u c d := by
    rw [testBit_leftMul]
    constructor
    · rintro ⟨u, hu, h1, h2⟩
      obtain ⟨u, rfl⟩ := Atom.exists_code hu
      rw [testBit_prodMask u.code_lt, hbit] at h1
      rw [testBit_prodMask d.code_lt, hbit] at h2
      exact ⟨u, h1, h2⟩
    · rintro ⟨u, h1, h2⟩
      refine ⟨u.code, u.code_lt, ?_, ?_⟩
      · rw [testBit_prodMask u.code_lt, hbit]
        exact h1
      · rw [testBit_prodMask d.code_lt, hbit]
        exact h2
  have hright (a b c d : Atom j k) :
      (rightMul n t a.code (prodMask n t b.code c.code)).testBit d.code = true ↔
        ∃ u, cycleClosure cycles b c u ∧ cycleClosure cycles a u d := by
    rw [testBit_rightMul]
    constructor
    · rintro ⟨u, hu, h1, h2⟩
      obtain ⟨u, rfl⟩ := Atom.exists_code hu
      rw [testBit_prodMask u.code_lt, hbit] at h1
      rw [testBit_prodMask d.code_lt, hbit] at h2
      exact ⟨u, h1, h2⟩
    · rintro ⟨u, h1, h2⟩
      refine ⟨u.code, u.code_lt, ?_, ?_⟩
      · rw [testBit_prodMask u.code_lt, hbit]
        exact h1
      · rw [testBit_prodMask d.code_lt, hbit]
        exact h2
  have hcode {P : ℕ → Prop} : (∀ c < n, P c) ↔ ∀ x : Atom j k, P x.code := by
    constructor
    · intro h x
      exact h _ x.code_lt
    · intro h c hc
      obtain ⟨x, rfl⟩ := Atom.exists_code hc
      exact h x
  simp only [assocCheck, allBelow_eq_true, Nat.beq_eq]
  rw [hcode]
  refine forall_congr' fun a => ?_
  rw [hcode]
  refine forall_congr' fun b => ?_
  rw [hcode]
  refine forall_congr' fun c => ?_
  constructor
  · intro h d
    rw [← hleft, ← hright, h]
  · intro h
    apply eq_of_testBit_eq_of_lt (leftMul_lt _ _ _ _) (rightMul_lt _ _ _ _)
    intro e he
    obtain ⟨d, rfl⟩ := Atom.exists_code he
    rw [Bool.eq_iff_iff, hleft, hright]
    exact h d

/-- Associativity of a cycle table, certified by evaluating the bitmask checker. -/
theorem atomCompositionAssociative_of_assocCheck {cycles : Finset (Cycle j k)}
    (h : assocCheck (atomCount j k) (tableCode cycles) = true) :
    AtomCompositionAssociative cycles :=
  (assocCheck_iff (encodesTable_tableCode cycles)).mp h

end Cslib.RelationAlgebra
