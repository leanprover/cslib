/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Data
public import Cslib.Foundations.RelationAlgebra.FastCatalogueCoverage

/-!
# Profile coverage for models 961–1024 of the ⟨1, 2, 1⟩ row

The balanced word contains exactly the cycle profiles of this block and its atom renamings.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S2N1.Coverage015

/-- The cycle profiles covered by this block of models. -/
def word : ℕ :=
  (Nat.shiftLeft
    (Nat.shiftLeft
      (Code.joinWords 8192
        (Nat.shiftLeft
          (Code.joinWords 2048
            (Nat.shiftLeft
              (Code.joinWords 512
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    297747071055821155530452781502797185024
                    128)
                  256)
                (Code.joinWords 256
                  (Nat.shiftLeft
                    338947622109741354347689737761480245248
                    128)
                  (Code.joinWords 128
                    336277808028214613707668163941950816256
                    338947622184018663405977137718711287808)))
              1024)
            (Code.joinWords 1024
              (Code.joinWords 512
                (Nat.shiftLeft
                  319014718988379809508442909513351168000
                  128)
                (Nat.shiftLeft
                  11574251042342174720
                  128))
              (Code.joinWords 512
                (Nat.shiftLeft
                  5337681170573802813703601270936305664
                  128)
                (Nat.shiftLeft
                  5337681170573802813703601270936305664
                  128))))
          4096)
        (Code.joinWords 4096
          (Nat.shiftLeft
            (Code.joinWords 1024
              (Code.joinWords 512
                (Nat.shiftLeft
                  11529215046068469888
                  128)
                (Nat.shiftLeft
                  11529215046068469888
                  128))
              (Code.joinWords 512
                (Nat.shiftLeft
                  11574391781978013696
                  128)
                (Nat.shiftLeft
                  11574391781978013696
                  128)))
            2048)
          (Code.joinWords 2048
            (Code.joinWords 1024
              (Code.joinWords 512
                (Code.joinWords 256
                  (Nat.shiftLeft
                    11529215046068469760
                    128)
                  (Nat.shiftLeft
                    17293822569102704640
                    128))
                (Nat.shiftLeft
                  11574251042342174720
                  128))
              (Code.joinWords 512
                (Code.joinWords 256
                  (Nat.shiftLeft
                    11574392329586343936
                    128)
                  (Nat.shiftLeft
                    289356276058554368
                    128))
                (Code.joinWords 256
                  (Nat.shiftLeft
                    11574392329586343936
                    128)
                  (Nat.shiftLeft
                    289356276058554368
                    128))))
            (Code.joinWords 1024
              (Code.joinWords 512
                (Nat.shiftLeft
                  11529215046068469760
                  128)
                (Nat.shiftLeft
                  11574251042342174720
                  128))
              (Code.joinWords 512
                (Nat.shiftLeft
                  16186078350169636864
                  128)
                (Nat.shiftLeft
                  16204092748679118848
                  128))))))
      16384)
    32768)

/-- The block word is computed from the verified profile data. -/
theorem word_eq :
    Code.profileWord 64 4 (fun i q => Data.profiles (960 + i) q) = word := by
  decide +kernel

end Cslib.RelationAlgebra.Catalogue.I1S2N1.Coverage015
