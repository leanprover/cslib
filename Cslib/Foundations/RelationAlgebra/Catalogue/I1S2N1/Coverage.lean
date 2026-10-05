/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Coverage000
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Coverage001
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Coverage002
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Coverage003
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Coverage004
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Coverage005
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Coverage006
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Coverage007
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Coverage008
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Coverage009
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Coverage010
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Coverage011
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Coverage012
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Coverage013
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Coverage014
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Coverage015
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Coverage016
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Coverage017
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Coverage018
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Coverage019
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Coverage020

/-!
# Complete profile coverage for the ⟨1, 2, 1⟩ row

Independent block certificates bound kernel memory. Their union equals the simultaneous
associativity truth table, computed from a sufficient collection of necessary equations.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S2N1.Coverage

/-- The independently certified coverage words. -/
def blockWords : ℕ → ℕ
  | 0 => Coverage000.word
  | 1 => Coverage001.word
  | 2 => Coverage002.word
  | 3 => Coverage003.word
  | 4 => Coverage004.word
  | 5 => Coverage005.word
  | 6 => Coverage006.word
  | 7 => Coverage007.word
  | 8 => Coverage008.word
  | 9 => Coverage009.word
  | 10 => Coverage010.word
  | 11 => Coverage011.word
  | 12 => Coverage012.word
  | 13 => Coverage013.word
  | 14 => Coverage014.word
  | 15 => Coverage015.word
  | 16 => Coverage016.word
  | 17 => Coverage017.word
  | 18 => Coverage018.word
  | 19 => Coverage019.word
  | 20 => Coverage020.word
  | _ => 0

private theorem blockWords_eq : ∀ b, b < 21 →
    Code.profileWord (min 64 (1316 - b * 64)) 4
      (fun i q => Data.profiles (b * 64 + i) q) = blockWords b
  | 0, _ => Coverage000.word_eq
  | 1, _ => Coverage001.word_eq
  | 2, _ => Coverage002.word_eq
  | 3, _ => Coverage003.word_eq
  | 4, _ => Coverage004.word_eq
  | 5, _ => Coverage005.word_eq
  | 6, _ => Coverage006.word_eq
  | 7, _ => Coverage007.word_eq
  | 8, _ => Coverage008.word_eq
  | 9, _ => Coverage009.word_eq
  | 10, _ => Coverage010.word_eq
  | 11, _ => Coverage011.word_eq
  | 12, _ => Coverage012.word_eq
  | 13, _ => Coverage013.word_eq
  | 14, _ => Coverage014.word_eq
  | 15, _ => Coverage015.word_eq
  | 16, _ => Coverage016.word_eq
  | 17, _ => Coverage017.word_eq
  | 18, _ => Coverage018.word_eq
  | 19, _ => Coverage019.word_eq
  | 20, _ => Coverage020.word_eq
  | n + 21, h => False.elim (by omega)

/-- The union of the block words is the complete profile word. -/
theorem profileWord_eq : Code.profileWord 1316 4 Data.profiles =
    Code.orBelow blockWords 21 :=
  Code.profileWord_eq_of_chunks Data.profiles (by decide) (by decide) blockWords blockWords_eq

/-- The truth word for a cycle on the specified atom codes. -/
def words (a b c : ℕ) : ℕ := Code.cycleWord 16 (Data.slots a b c)

/-- A sufficient list of necessary associativity equations. -/
def quads : ℕ → Code.Quadruple
  | 0 => (1, 1, 1, 3)
  | 1 => (1, 1, 2, 2)
  | 2 => (1, 1, 2, 3)
  | 3 => (1, 1, 2, 4)
  | 4 => (1, 1, 3, 3)
  | 5 => (1, 1, 3, 4)
  | 6 => (1, 1, 4, 4)
  | 7 => (1, 2, 1, 3)
  | 8 => (1, 2, 2, 3)
  | 9 => (1, 2, 2, 4)
  | 10 => (1, 2, 3, 2)
  | 11 => (1, 2, 3, 3)
  | 12 => (1, 2, 3, 4)
  | 13 => (1, 2, 4, 3)
  | 14 => (1, 2, 4, 4)
  | 15 => (1, 3, 1, 4)
  | 16 => (1, 3, 2, 4)
  | 17 => (1, 3, 3, 3)
  | 18 => (1, 3, 3, 4)
  | 19 => (1, 3, 4, 4)
  | 20 => (1, 4, 3, 4)
  | 21 => (2, 2, 2, 3)
  | 22 => (2, 2, 3, 3)
  | 23 => (2, 2, 3, 4)
  | 24 => (2, 2, 4, 4)
  | 25 => (2, 3, 2, 4)
  | 26 => (2, 3, 3, 3)
  | 27 => (2, 3, 3, 4)
  | 28 => (2, 3, 4, 4)
  | 29 => (2, 4, 3, 4)
  | 30 => (3, 3, 3, 3)
  | 31 => (3, 3, 4, 3)
  | _ => (0, 0, 0, 0)

/-- Every equation uses valid atom codes. -/
theorem quads_lt : ∀ i < 32, (quads i).1 < 5 ∧ (quads i).2.1 < 5 ∧
    (quads i).2.2.1 < 5 ∧ (quads i).2.2.2 < 5 := by
  have h : ∀ i : Fin 32, (quads i).1 < 5 ∧ (quads i).2.1 < 5 ∧
      (quads i).2.2.1 < 5 ∧ (quads i).2.2.2 < 5 := by decide +kernel
  intro i hi
  exact h ⟨i, hi⟩

/-- Every assignment satisfying these necessary equations is a listed cycle profile. -/
theorem check : Code.associativityWordFor 5 (Code.truthOnes (2 ^ 16)) words quads 32 =
    Code.profileWord 1316 4 Data.profiles := by
  rw [profileWord_eq]
  decide +kernel

end Cslib.RelationAlgebra.Catalogue.I1S2N1.Coverage
