/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Data
public import Cslib.Foundations.RelationAlgebra.FastCatalogueCoverage

/-!
# Profile coverage for models 705–768 of the ⟨1, 2, 1⟩ row

The balanced word contains exactly the cycle profiles of this block and its atom renamings.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S2N1.Coverage011

/-- The cycle profiles covered by this block of models. -/
def word : ℕ :=
  (Nat.shiftLeft
    (Code.joinWords 16384
      (Nat.shiftLeft
        (Code.joinWords 4096
          (Nat.shiftLeft
            (Code.joinWords 1024
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    255211775190703847597530955573826158592
                    128)
                  256)
                512)
              (Code.joinWords 512
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    333345458317935933751657864335930163200
                    128)
                  256)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    333345458317935933751657864335930163200
                    128)
                  256)))
            2048)
          (Nat.shiftLeft
            (Code.joinWords 1024
              (Code.joinWords 512
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    319014718988379809496913694467282698240
                    128)
                  256)
                (Nat.shiftLeft
                  (Code.joinWords 128
                    320011639985218496401591549762492956672
                    333345458317935933751657864335930163200)
                  256))
              (Code.joinWords 512
                (Nat.shiftLeft
                  (Code.joinWords 128
                    330645463951497823384822006244735713280
                    338688022553131238502295316130487599104)
                  256)
                (Nat.shiftLeft
                  (Code.joinWords 128
                    330645463951497823384822006244735713280
                    338688022553131238502295316130487599104)
                  256)))
            2048))
        8192)
      (Code.joinWords 8192
        (Code.joinWords 4096
          (Code.joinWords 1024
            (Code.joinWords 512
              (Nat.shiftLeft
                (Nat.shiftLeft
                  170141183460469231731687303715884105728
                  128)
                256)
              (Nat.shiftLeft
                (Nat.shiftLeft
                  170141183460469231731687303715884105728
                  128)
                256))
            (Code.joinWords 512
              (Code.joinWords 256
                (Code.joinWords 128
                  16145404664123289792
                  75557863725914323431680)
                (Nat.shiftLeft
                  4096
                  128))
              4629700416936890432))
          (Code.joinWords 2048
            (Code.joinWords 1024
              64
              (Code.joinWords 512
                64
                64))
            (Nat.shiftLeft
              64
              1024)))
        (Nat.shiftLeft
          (Code.joinWords 2048
            (Nat.shiftLeft
              64
              1024)
            (Nat.shiftLeft
              (Nat.shiftLeft
                864691128455135232
                512)
              1024))
          4096)))
    32768)

/-- The block word is computed from the verified profile data. -/
theorem word_eq :
    Code.profileWord 64 4 (fun i q => Data.profiles (704 + i) q) = word := by
  decide +kernel

end Cslib.RelationAlgebra.Catalogue.I1S2N1.Coverage011
