/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Coverage000
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Coverage001
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Coverage002
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Coverage003
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Coverage004
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Coverage005
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Coverage006
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Coverage007
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Coverage008
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Coverage009
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Coverage010
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Coverage011
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Coverage012
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Coverage013
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Coverage014
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Coverage015
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Coverage016
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Coverage017
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Coverage018
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Coverage019
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Coverage020
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Coverage021
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Coverage022
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Coverage023
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Coverage024
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Coverage025
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Coverage026
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Coverage027
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Coverage028
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Coverage029
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Coverage030
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Coverage031
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Coverage032
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Coverage033
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Coverage034
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Coverage035
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Coverage036
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Coverage037
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Coverage038
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Coverage039
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Coverage040
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Coverage041
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Coverage042
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Coverage043
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Coverage044
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Coverage045
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Coverage046
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Coverage047

/-!
# Complete profile coverage for the ⟨1, 4, 0⟩ row

Independent block certificates bound kernel memory. Their union equals the simultaneous
associativity truth table, computed from a sufficient collection of necessary equations.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage

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
  | 21 => Coverage021.word
  | 22 => Coverage022.word
  | 23 => Coverage023.word
  | 24 => Coverage024.word
  | 25 => Coverage025.word
  | 26 => Coverage026.word
  | 27 => Coverage027.word
  | 28 => Coverage028.word
  | 29 => Coverage029.word
  | 30 => Coverage030.word
  | 31 => Coverage031.word
  | 32 => Coverage032.word
  | 33 => Coverage033.word
  | 34 => Coverage034.word
  | 35 => Coverage035.word
  | 36 => Coverage036.word
  | 37 => Coverage037.word
  | 38 => Coverage038.word
  | 39 => Coverage039.word
  | 40 => Coverage040.word
  | 41 => Coverage041.word
  | 42 => Coverage042.word
  | 43 => Coverage043.word
  | 44 => Coverage044.word
  | 45 => Coverage045.word
  | 46 => Coverage046.word
  | 47 => Coverage047.word
  | _ => 0

private theorem blockWords_eq : ∀ b, b < 48 →
    Code.profileWord (min 64 (3013 - b * 64)) 24
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
  | 21, _ => Coverage021.word_eq
  | 22, _ => Coverage022.word_eq
  | 23, _ => Coverage023.word_eq
  | 24, _ => Coverage024.word_eq
  | 25, _ => Coverage025.word_eq
  | 26, _ => Coverage026.word_eq
  | 27, _ => Coverage027.word_eq
  | 28, _ => Coverage028.word_eq
  | 29, _ => Coverage029.word_eq
  | 30, _ => Coverage030.word_eq
  | 31, _ => Coverage031.word_eq
  | 32, _ => Coverage032.word_eq
  | 33, _ => Coverage033.word_eq
  | 34, _ => Coverage034.word_eq
  | 35, _ => Coverage035.word_eq
  | 36, _ => Coverage036.word_eq
  | 37, _ => Coverage037.word_eq
  | 38, _ => Coverage038.word_eq
  | 39, _ => Coverage039.word_eq
  | 40, _ => Coverage040.word_eq
  | 41, _ => Coverage041.word_eq
  | 42, _ => Coverage042.word_eq
  | 43, _ => Coverage043.word_eq
  | 44, _ => Coverage044.word_eq
  | 45, _ => Coverage045.word_eq
  | 46, _ => Coverage046.word_eq
  | 47, _ => Coverage047.word_eq
  | n + 48, h => False.elim (by omega)

/-- The union of the block words is the complete profile word. -/
theorem profileWord_eq : Code.profileWord 3013 24 Data.profiles =
    Code.orBelow blockWords 48 :=
  Code.profileWord_eq_of_chunks Data.profiles (by decide) (by decide) blockWords blockWords_eq

/-- The truth word for a cycle on the specified atom codes. -/
def words (a b c : ℕ) : ℕ := Code.cycleWord 20 (Data.slots a b c)

/-- A sufficient list of necessary associativity equations. -/
def quads : ℕ → Code.Quadruple
  | 0 => (1, 1, 2, 2)
  | 1 => (1, 1, 2, 3)
  | 2 => (1, 1, 2, 4)
  | 3 => (1, 1, 3, 3)
  | 4 => (1, 1, 3, 4)
  | 5 => (1, 1, 4, 4)
  | 6 => (1, 2, 2, 3)
  | 7 => (1, 2, 2, 4)
  | 8 => (1, 2, 3, 3)
  | 9 => (1, 2, 3, 4)
  | 10 => (1, 2, 4, 3)
  | 11 => (1, 2, 4, 4)
  | 12 => (1, 3, 3, 4)
  | 13 => (1, 3, 4, 4)
  | 14 => (2, 2, 3, 3)
  | 15 => (2, 2, 3, 4)
  | 16 => (2, 2, 4, 4)
  | 17 => (2, 3, 3, 4)
  | 18 => (2, 3, 4, 4)
  | 19 => (3, 3, 4, 4)
  | _ => (0, 0, 0, 0)

/-- Every equation uses valid atom codes. -/
theorem quads_lt : ∀ i < 20, (quads i).1 < 5 ∧ (quads i).2.1 < 5 ∧
    (quads i).2.2.1 < 5 ∧ (quads i).2.2.2 < 5 := by
  have h : ∀ i : Fin 20, (quads i).1 < 5 ∧ (quads i).2.1 < 5 ∧
      (quads i).2.2.1 < 5 ∧ (quads i).2.2.2 < 5 := by decide +kernel
  intro i hi
  exact h ⟨i, hi⟩

/-- Every assignment satisfying these necessary equations is a listed cycle profile. -/
theorem check : Code.associativityWordFor 5 (Code.truthOnes (2 ^ 20)) words quads 20 =
    Code.profileWord 3013 24 Data.profiles := by
  rw [profileWord_eq]
  decide +kernel

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage
