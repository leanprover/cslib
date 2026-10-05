/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Data
public import Cslib.Foundations.RelationAlgebra.FastCatalogueCoverage

/-!
# Profile coverage for models 257–320 of the ⟨1, 2, 1⟩ row

The balanced word contains exactly the cycle profiles of this block and its atom renamings.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S2N1.Coverage004

/-- The cycle profiles covered by this block of models. -/
def word : ℕ :=
  (Nat.shiftLeft
    (Code.joinWords 8192
      (Nat.shiftLeft
        (Code.joinWords 2048
          (Nat.shiftLeft
            (Code.joinWords 512
              (Nat.shiftLeft
                (Code.joinWords 128
                  336211606183847158602606698309659656192
                  338947622184018663387603014184966553600)
                256)
              (Code.joinWords 256
                (Nat.shiftLeft
                  338947622109741354347689737761480245248
                  128)
                (Code.joinWords 128
                  166132730285680358969561209158661832704
                  18374123533744734208)))
            1024)
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
                11574251044498046976
                128)
              (Nat.shiftLeft
                11574251044498046976
                128))))
        4096)
      (Code.joinWords 4096
        (Nat.shiftLeft
          (Code.joinWords 1024
            (Code.joinWords 512
              (Nat.shiftLeft
                16140901064495857792
                128)
              (Nat.shiftLeft
                16140901064495857792
                128))
            (Code.joinWords 512
              (Nat.shiftLeft
                17361376563513262080
                128)
              (Nat.shiftLeft
                8138004526658486272
                128)))
          2048)
        (Code.joinWords 2048
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
                11574392329586343936
                128)
              (Nat.shiftLeft
                11574392329586343936
                128)))
          (Code.joinWords 1024
            (Code.joinWords 512
              (Nat.shiftLeft
                5764607523034234880
                128)
              (Nat.shiftLeft
                5787125521171087360
                128))
            (Code.joinWords 512
              (Nat.shiftLeft
                5787196165871124480
                128)
              (Nat.shiftLeft
                5787196165871124480
                128))))))
    16384)

/-- The block word is computed from the verified profile data. -/
theorem word_eq :
    Code.profileWord 64 4 (fun i q => Data.profiles (256 + i) q) = word := by
  decide +kernel

end Cslib.RelationAlgebra.Catalogue.I1S2N1.Coverage004
