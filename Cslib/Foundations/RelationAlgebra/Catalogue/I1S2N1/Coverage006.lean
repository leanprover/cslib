/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Data
public import Cslib.Foundations.RelationAlgebra.FastCatalogueCoverage

/-!
# Profile coverage for models 385–448 of the ⟨1, 2, 1⟩ row

The balanced word contains exactly the cycle profiles of this block and its atom renamings.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S2N1.Coverage006

/-- The cycle profiles covered by this block of models. -/
def word : ℕ :=
  (Nat.shiftLeft
    (Code.joinWords 8192
      (Nat.shiftLeft
        (Nat.shiftLeft
          (Nat.shiftLeft
            (Code.joinWords 512
              (Code.joinWords 256
                (Nat.shiftLeft
                  320264115459578833652161013943273259008
                  128)
                (Code.joinWords 128
                  336273913746149590701248512874545938432
                  338947622184250777162330399554062516224))
              (Code.joinWords 256
                (Nat.shiftLeft
                  106758166730880509659826230709754789888
                  128)
                (Nat.shiftLeft
                  5787125522517458944
                  128)))
            1024)
          2048)
        4096)
      (Code.joinWords 4096
        (Nat.shiftLeft
          (Code.joinWords 1024
            (Code.joinWords 512
              (Code.joinWords 256
                (Nat.shiftLeft
                  106338239662793271012896185539838869504
                  128)
                (Nat.shiftLeft
                  5764607523034234944
                  128))
              (Code.joinWords 256
                (Nat.shiftLeft
                  106338239662793271012896185539838869504
                  128)
                (Nat.shiftLeft
                  5764607523034234944
                  128)))
            (Code.joinWords 512
              (Code.joinWords 256
                (Nat.shiftLeft
                  106753623411476056042587004528765173760
                  128)
                (Nat.shiftLeft
                  5787125521171087360
                  128))
              (Code.joinWords 256
                (Nat.shiftLeft
                  106753623411476056042587004528765173760
                  128)
                (Nat.shiftLeft
                  5787125521171087360
                  128))))
          2048)
        (Code.joinWords 2048
          (Nat.shiftLeft
            (Code.joinWords 512
              (Code.joinWords 256
                (Nat.shiftLeft
                  320265753224540247267415578887042629632
                  128)
                (Code.joinWords 128
                  336273913746149590701248512874545938432
                  338947637395825866143717349449090990080))
              (Code.joinWords 256
                (Nat.shiftLeft
                  106755251074846749089138526295680876544
                  128)
                (Nat.shiftLeft
                  5787337455795437568
                  128)))
            1024)
          (Code.joinWords 1024
            (Code.joinWords 512
              (Code.joinWords 256
                (Nat.shiftLeft
                  106338239662793269832304564822427566080
                  128)
                (Nat.shiftLeft
                  5764607523034234880
                  128))
              (Code.joinWords 256
                (Nat.shiftLeft
                  106753623411476056042587004528765173760
                  128)
                (Nat.shiftLeft
                  5787125521171087360
                  128)))
            (Code.joinWords 512
              (Code.joinWords 256
                (Nat.shiftLeft
                  106755251094731463201614850618541735936
                  128)
                (Nat.shiftLeft
                  5787196166139559936
                  128))
              (Code.joinWords 256
                (Nat.shiftLeft
                  106755251094731463201614850618541735936
                  128)
                (Nat.shiftLeft
                  5787196166139559936
                  128)))))))
    16384)

/-- The block word is computed from the verified profile data. -/
theorem word_eq :
    Code.profileWord 64 4 (fun i q => Data.profiles (384 + i) q) = word := by
  decide +kernel

end Cslib.RelationAlgebra.Catalogue.I1S2N1.Coverage006
