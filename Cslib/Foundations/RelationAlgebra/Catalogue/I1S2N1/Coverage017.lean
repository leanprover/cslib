/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Data
public import Cslib.Foundations.RelationAlgebra.FastCatalogueCoverage

/-!
# Profile coverage for models 1089–1152 of the ⟨1, 2, 1⟩ row

The balanced word contains exactly the cycle profiles of this block and its atom renamings.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S2N1.Coverage017

/-- The cycle profiles covered by this block of models. -/
def word : ℕ :=
  (Nat.shiftLeft
    (Nat.shiftLeft
      (Code.joinWords 8192
        (Nat.shiftLeft
          (Nat.shiftLeft
            (Nat.shiftLeft
              (Code.joinWords 512
                (Nat.shiftLeft
                  (Code.joinWords 128
                    336276509894578843947963329513774907392
                    338947622184250777162330399554062516224)
                  256)
                (Code.joinWords 256
                  (Nat.shiftLeft
                    213510492048257520114484681948870475776
                    128)
                  (Code.joinWords 128
                    3894282297150930885108477884104704
                    5787125522517458944)))
              1024)
            2048)
          4096)
        (Code.joinWords 4096
          (Nat.shiftLeft
            (Code.joinWords 1024
              (Code.joinWords 512
                (Code.joinWords 256
                  (Nat.shiftLeft
                    106338239662793272193487806257250172928
                    128)
                  (Nat.shiftLeft
                    5764607523034235008
                    128))
                (Code.joinWords 256
                  (Nat.shiftLeft
                    106338239662793272193487806257250172928
                    128)
                  (Nat.shiftLeft
                    5764607523034235008
                    128)))
              (Code.joinWords 512
                (Code.joinWords 256
                  (Nat.shiftLeft
                    106756868636626721566987004885742911488
                    128)
                  (Nat.shiftLeft
                    5787266261343797248
                    128))
                (Code.joinWords 256
                  (Nat.shiftLeft
                    106756868656433762195553089284128899072
                    128)
                  (Nat.shiftLeft
                    5787336630087974912
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
                    336273913785763657791281233062382272512
                    338947637395825866126355832145405018112))
                (Code.joinWords 256
                  (Nat.shiftLeft
                    106755251074846749089138526295680876544
                    128)
                  (Code.joinWords 128
                    3909493872239912271917636778983424
                    11574392332270698496)))
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
    32768)

/-- The block word is computed from the verified profile data. -/
theorem word_eq :
    Code.profileWord 64 4 (fun i q => Data.profiles (1088 + i) q) = word := by
  decide +kernel

end Cslib.RelationAlgebra.Catalogue.I1S2N1.Coverage017
