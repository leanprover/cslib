/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Data
public import Cslib.Foundations.RelationAlgebra.FastCatalogueCoverage

/-!
# Profile coverage for models 193–256 of the ⟨1, 2, 1⟩ row

The balanced word contains exactly the cycle profiles of this block and its atom renamings.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S2N1.Coverage003

/-- The cycle profiles covered by this block of models. -/
def word : ℕ :=
  (Nat.shiftLeft
    (Code.joinWords 8192
      (Nat.shiftLeft
        (Code.joinWords 2048
          (Code.joinWords 1024
            (Code.joinWords 512
              (Code.joinWords 256
                (Nat.shiftLeft
                  297747071055821155530452781502797185024
                  128)
                (Nat.shiftLeft
                  319014718988379809513054595531778555904
                  128))
              (Code.joinWords 256
                (Nat.shiftLeft
                  320260870234428168145122390149808783360
                  128)
                (Nat.shiftLeft
                  333605073160862675150445765715904430080
                  128)))
            (Code.joinWords 512
              (Code.joinWords 256
                (Nat.shiftLeft
                  338947622109741354354200253972797718528
                  128)
                (Code.joinWords 128
                  62307562302432098641814564886282240
                  18374123533744734208))
              (Nat.shiftLeft
                6510516211317473280
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
                6798746588547121152
                128)
              (Nat.shiftLeft
                6799872488453963776
                128))))
        4096)
      (Code.joinWords 4096
        (Nat.shiftLeft
          (Code.joinWords 512
            (Nat.shiftLeft
              1152921504606847040
              128)
            (Nat.shiftLeft
              1152921504606847040
              128))
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
                6798817231091269632
                128)
              (Nat.shiftLeft
                6799943130998112256
                128)))
          (Code.joinWords 1024
            (Nat.shiftLeft
              (Nat.shiftLeft
                723390690146385920
                128)
              512)
            (Code.joinWords 512
              (Nat.shiftLeft
                1012746966204940288
                128)
              (Nat.shiftLeft
                1012746966204940288
                128))))))
    16384)

/-- The block word is computed from the verified profile data. -/
theorem word_eq :
    Code.profileWord 64 4 (fun i q => Data.profiles (192 + i) q) = word := by
  decide +kernel

end Cslib.RelationAlgebra.Catalogue.I1S2N1.Coverage003
