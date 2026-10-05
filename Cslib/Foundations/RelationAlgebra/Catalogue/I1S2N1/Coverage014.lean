/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Data
public import Cslib.Foundations.RelationAlgebra.FastCatalogueCoverage

/-!
# Profile coverage for models 897–960 of the ⟨1, 2, 1⟩ row

The balanced word contains exactly the cycle profiles of this block and its atom renamings.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S2N1.Coverage014

/-- The cycle profiles covered by this block of models. -/
def word : ℕ :=
  (Nat.shiftLeft
    (Nat.shiftLeft
      (Code.joinWords 8192
        (Nat.shiftLeft
          (Code.joinWords 2048
            (Code.joinWords 1024
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    332306998946228968225951765070086144000
                    128)
                  256)
                512)
              (Code.joinWords 512
                (Code.joinWords 256
                  (Nat.shiftLeft
                    338947622109741354353476863282651332608
                    128)
                  (Code.joinWords 128
                    336277808028214613707668163941950816256
                    41200551128197507875524356215914102784))
                (Nat.shiftLeft
                  5787125521171087360
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
                  5787125522249023488
                  128)
                (Nat.shiftLeft
                  5787125522249023488
                  128))))
          4096)
        (Code.joinWords 4096
          (Nat.shiftLeft
            (Code.joinWords 1024
              (Code.joinWords 512
                (Nat.shiftLeft
                  5764607523034234944
                  128)
                (Nat.shiftLeft
                  5764607523034234944
                  128))
              (Code.joinWords 512
                (Nat.shiftLeft
                  5787195890989006848
                  128)
                (Nat.shiftLeft
                  5787195890989006848
                  128)))
            2048)
          (Code.joinWords 2048
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
                  5787196164793171968
                  128)
                (Nat.shiftLeft
                  5787196164793171968
                  128)))
            (Code.joinWords 1024
              (Code.joinWords 512
                (Nat.shiftLeft
                  5764607523034234880
                  128)
                (Nat.shiftLeft
                  6365838073288196096
                  128))
              (Code.joinWords 512
                (Nat.shiftLeft
                  1754222699560845312
                  128)
                (Nat.shiftLeft
                  1736208301051363328
                  128))))))
      16384)
    32768)

/-- The block word is computed from the verified profile data. -/
theorem word_eq :
    Code.profileWord 64 4 (fun i q => Data.profiles (896 + i) q) = word := by
  decide +kernel

end Cslib.RelationAlgebra.Catalogue.I1S2N1.Coverage014
