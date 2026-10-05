/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Mathlib.Tactic.FinCases
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1985
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1986
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1987
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1988
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1989
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1990
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1991
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1992
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1993
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1994
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1995
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1996
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1997
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1998
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1999
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2000
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2001
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2002
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2003
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2004
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2005
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2006
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2007
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2008
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2009
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2010
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2011
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2012
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2013
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2014
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2015
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2016
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2017
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2018
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2019
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2020
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2021
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2022
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2023
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2024
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2025
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2026
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2027
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2028
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2029
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2030
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2031
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2032
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2033
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2034
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2035
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2036
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2037
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2038
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2039
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2040
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2041
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2042
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2043
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2044
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2045
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2046
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2047
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2048

/-!
# Certified models 1985–2048 of the ⟨1, 4, 0⟩ row

Each record refers to an explicitly defined algebra and certifies its canonical cycle profile.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Models031

/-- The explicit models in this block, with their certified numeric profiles. -/
def entries : Array (ProfiledCycleTable Data.cycleReps) :=
  #[
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1985.table, code := 9926313260829611811963963900445331521,
        encodes := Ra1985.tableCode_eq ▸ encodesTable_tableCode Ra1985.cycles } 251902
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1986.table, code := 9926313260829611811963963902592815169,
        encodes := Ra1986.tableCode_eq ▸ encodesTable_tableCode Ra1986.cycles } 251903
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1987.table, code := 9923554850792703994923030698172616769,
        encodes := Ra1987.tableCode_eq ▸ encodesTable_tableCode Ra1987.cycles } 252733
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1988.table, code := 9923554850792703994995088363077505089,
        encodes := Ra1988.tableCode_eq ▸ encodesTable_tableCode Ra1988.cycles } 252734
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1989.table, code := 9923554850792703994995088365224988737,
        encodes := Ra1989.tableCode_eq ▸ encodesTable_tableCode Ra1989.cycles } 252735
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1990.table, code := 9926313258416595954051524870923358273,
        encodes := Ra1990.tableCode_eq ▸ encodesTable_tableCode Ra1990.cycles } 252765
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1991.table, code := 9926313258416595954123582535828246593,
        encodes := Ra1991.tableCode_eq ▸ encodesTable_tableCode Ra1991.cycles } 252766
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1992.table, code := 9926313258416595954123582537975730241,
        encodes := Ra1992.tableCode_eq ▸ encodesTable_tableCode Ra1992.cycles } 252767
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1993.table, code := 9926313258498802981482630331041583169,
        encodes := Ra1993.tableCode_eq ▸ encodesTable_tableCode Ra1993.cycles } 252783
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1994.table, code := 9926313258498802983860530998717714497,
        encodes := Ra1994.tableCode_eq ▸ encodesTable_tableCode Ra1994.cycles } 252797
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1995.table, code := 9926313258498802983932588663622602817,
        encodes := Ra1995.tableCode_eq ▸ encodesTable_tableCode Ra1995.cycles } 252798
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1996.table, code := 9926313258498802983932588665770086465,
        encodes := Ra1996.tableCode_eq ▸ encodesTable_tableCode Ra1996.cycles } 252799
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1997.table, code := 9923554853196048450313768614572068929,
        encodes := Ra1997.tableCode_eq ▸ encodesTable_tableCode Ra1997.cycles } 252830
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1998.table, code := 9923554853196048450313768616719552577,
        encodes := Ra1998.tableCode_eq ▸ encodesTable_tableCode Ra1998.cycles } 252831
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1999.table, code := 9923473723637423021801777103622115393,
        encodes := Ra1999.tableCode_eq ▸ encodesTable_tableCode Ra1999.cycles } 252851
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2000.table, code := 9923473723639840873368950902532345921,
        encodes := Ra2000.tableCode_eq ▸ encodesTable_tableCode Ra2000.cycles } 252853
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2001.table, code := 9923473723639840873441008569584717889,
        encodes := Ra2001.tableCode_eq ▸ encodesTable_tableCode Ra2001.cycles } 252855
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2002.table, code := 9923554853275837628411485611498934337,
        encodes := Ra2002.tableCode_eq ▸ encodesTable_tableCode Ra2002.cycles } 252857
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2003.table, code := 9923554853275837628483543276403822657,
        encodes := Ra2003.tableCode_eq ▸ encodesTable_tableCode Ra2003.cycles } 252858
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2004.table, code := 9923554853275837628483543278551306305,
        encodes := Ra2004.tableCode_eq ▸ encodesTable_tableCode Ra2004.cycles } 252859
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2005.table, code := 9923554853278255480050717077461536833,
        encodes := Ra2005.tableCode_eq ▸ encodesTable_tableCode Ra2005.cycles } 252861
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2006.table, code := 9923554853278255480122774742366425153,
        encodes := Ra2006.tableCode_eq ▸ encodesTable_tableCode Ra2006.cycles } 252862
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2007.table, code := 9923554853278255480122774744513908801,
        encodes := Ra2007.tableCode_eq ▸ encodesTable_tableCode Ra2007.cycles } 252863
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2008.table, code := 9926232131263732832569502742335459393,
        encodes := Ra2008.tableCode_eq ▸ encodesTable_tableCode Ra2008.cycles } 252887
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2009.table, code := 9926313260902147439179211250212278337,
        encodes := Ra2009.tableCode_eq ▸ encodesTable_tableCode Ra2009.cycles } 252893
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2010.table, code := 9926313260902147439251268915117166657,
        encodes := Ra2010.tableCode_eq ▸ encodesTable_tableCode Ra2010.cycles } 252894
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2011.table, code := 9926313260902147439251268917264650305,
        encodes := Ra2011.tableCode_eq ▸ encodesTable_tableCode Ra2011.cycles } 252895
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2012.table, code := 9926232131345939859928550535401312321,
        encodes := Ra2012.tableCode_eq ▸ encodesTable_tableCode Ra2012.cycles } 252903
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2013.table, code := 9926313260984354466610316710330503233,
        encodes := Ra2013.tableCode_eq ▸ encodesTable_tableCode Ra2013.cycles } 252911
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2014.table, code := 9926232131343522010667219737114841153,
        encodes := Ra2014.tableCode_eq ▸ encodesTable_tableCode Ra2014.cycles } 252913
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2015.table, code := 9926232131343522010739277404167213121,
        encodes := Ra2015.tableCode_eq ▸ encodesTable_tableCode Ra2015.cycles } 252915
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2016.table, code := 9926232131345939862306451203077443649,
        encodes := Ra2016.tableCode_eq ▸ encodesTable_tableCode Ra2016.cycles } 252917
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2017.table, code := 9926232131345939862378508870129815617,
        encodes := Ra2017.tableCode_eq ▸ encodesTable_tableCode Ra2017.cycles } 252919
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2018.table, code := 9926313260981936617348985912044032065,
        encodes := Ra2018.tableCode_eq ▸ encodesTable_tableCode Ra2018.cycles } 252921
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2019.table, code := 9926313260981936617421043576948920385,
        encodes := Ra2019.tableCode_eq ▸ encodesTable_tableCode Ra2019.cycles } 252922
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2020.table, code := 9926313260981936617421043579096404033,
        encodes := Ra2020.tableCode_eq ▸ encodesTable_tableCode Ra2020.cycles } 252923
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2021.table, code := 9926313260984354468988217378006634561,
        encodes := Ra2021.tableCode_eq ▸ encodesTable_tableCode Ra2021.cycles } 252925
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2022.table, code := 9926313260984354469060275042911522881,
        encodes := Ra2022.tableCode_eq ▸ encodesTable_tableCode Ra2022.cycles } 252926
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2023.table, code := 9926313260984354469060275045059006529,
        encodes := Ra2023.tableCode_eq ▸ encodesTable_tableCode Ra2023.cycles } 252927
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2024.table, code := 9923554850792703997156816048923873345,
        encodes := Ra2024.tableCode_eq ▸ encodesTable_tableCode Ra2024.cycles } 253743
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2025.table, code := 9923554850792703999606774383652376641,
        encodes := Ra2025.tableCode_eq ▸ encodesTable_tableCode Ra2025.cycles } 253759
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2026.table, code := 9926313258416595956285310221674614849,
        encodes := Ra2026.tableCode_eq ▸ encodesTable_tableCode Ra2026.cycles } 253775
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2027.table, code := 9926313258416595958735268556403118145,
        encodes := Ra2027.tableCode_eq ▸ encodesTable_tableCode Ra2027.cycles } 253791
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2028.table, code := 9926313258498802986094316349468971073,
        encodes := Ra2028.tableCode_eq ▸ encodesTable_tableCode Ra2028.cycles } 253807
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2029.table, code := 9926313258498802988544274684197474369,
        encodes := Ra2029.tableCode_eq ▸ encodesTable_tableCode Ra2029.cycles } 253823
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2030.table, code := 9923554853196048454925454632999456833,
        encodes := Ra2030.tableCode_eq ▸ encodesTable_tableCode Ra2030.cycles } 253854
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2031.table, code := 9923554853196048454925454635146940481,
        encodes := Ra2031.tableCode_eq ▸ encodesTable_tableCode Ra2031.cycles } 253855
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2032.table, code := 9923473723637423023963504787321000001,
        encodes := Ra2032.tableCode_eq ▸ encodesTable_tableCode Ra2032.cycles } 253859
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2033.table, code := 9923473723639840875602736253283602497,
        encodes := Ra2033.tableCode_eq ▸ encodesTable_tableCode Ra2033.cycles } 253863
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2034.table, code := 9923554853275837630645270962250190913,
        encodes := Ra2034.tableCode_eq ▸ encodesTable_tableCode Ra2034.cycles } 253867
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2035.table, code := 9923554853278255482284502426065309761,
        encodes := Ra2035.tableCode_eq ▸ encodesTable_tableCode Ra2035.cycles } 253870
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2036.table, code := 9923554853278255482284502428212793409,
        encodes := Ra2036.tableCode_eq ▸ encodesTable_tableCode Ra2036.cycles } 253871
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2037.table, code := 9923473723637423026413463122049503297,
        encodes := Ra2037.tableCode_eq ▸ encodesTable_tableCode Ra2037.cycles } 253875
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2038.table, code := 9923473723639840877980636920959733825,
        encodes := Ra2038.tableCode_eq ▸ encodesTable_tableCode Ra2038.cycles } 253877
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2039.table, code := 9923473723639840878052694588012105793,
        encodes := Ra2039.tableCode_eq ▸ encodesTable_tableCode Ra2039.cycles } 253879
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2040.table, code := 9923554853275837633023171629926322241,
        encodes := Ra2040.tableCode_eq ▸ encodesTable_tableCode Ra2040.cycles } 253881
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2041.table, code := 9923554853275837633095229294831210561,
        encodes := Ra2041.tableCode_eq ▸ encodesTable_tableCode Ra2041.cycles } 253882
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2042.table, code := 9923554853275837633095229296978694209,
        encodes := Ra2042.tableCode_eq ▸ encodesTable_tableCode Ra2042.cycles } 253883
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2043.table, code := 9923554853278255484662403095888924737,
        encodes := Ra2043.tableCode_eq ▸ encodesTable_tableCode Ra2043.cycles } 253885
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2044.table, code := 9923554853278255484734460760793813057,
        encodes := Ra2044.tableCode_eq ▸ encodesTable_tableCode Ra2044.cycles } 253886
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2045.table, code := 9923554853278255484734460762941296705,
        encodes := Ra2045.tableCode_eq ▸ encodesTable_tableCode Ra2045.cycles } 253887
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2046.table, code := 9926232131263732834731230426034344001,
        encodes := Ra2046.tableCode_eq ▸ encodesTable_tableCode Ra2046.cycles } 253895
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2047.table, code := 9926313260902147441412996598816051265,
        encodes := Ra2047.tableCode_eq ▸ encodesTable_tableCode Ra2047.cycles } 253902
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2048.table, code := 9926313260902147441412996600963534913,
        encodes := Ra2048.tableCode_eq ▸ encodesTable_tableCode Ra2048.cycles } 253903
      (by decide +kernel)]

/-- The packed profiles in this block agree with the certified orbit action. -/
theorem profiles_eq : ∀ i : Fin 64, ∀ p : Fin 24,
    Data.profiles (1984 + i.val) p.val =
      Code.permuteProfile (Data.canonicalMask (1984 + i.val)) (Data.orbitAction p) := by
  decide +kernel

/-- Every canonical profile in this block is least among its atom renamings. -/
theorem profiles_minimal : ∀ i : Fin 64, ∀ p : Fin 24,
    Data.profiles (1984 + i.val) 0 ≤ Data.profiles (1984 + i.val) p.val := by
  decide +kernel

/-- Identity renaming reads the canonical mask in this block. -/
theorem profiles_zero : ∀ i : Fin 64,
    Data.profiles (1984 + i.val) 0 = Data.canonicalMask (1984 + i.val) := by
  decide +kernel

/-- Every mask in this block is smaller than its successor, where a successor exists. -/
theorem canonicalMask_increasing : ∀ i : Fin 64,
    Data.canonicalMask (1984 + i.val) < Data.canonicalMask (1984 + i.val + 1) := by
  decide +kernel

/-- Each model record has the canonical mask stored at its global index. -/
theorem entries_profile (fallback : ProfiledCycleTable Data.cycleReps) : ∀ i : Fin 64,
    (entries.getD i.val fallback).profile =
      Data.canonicalMask (1984 + i.val) := by
  intro i
  fin_cases i <;> rfl

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Models031
