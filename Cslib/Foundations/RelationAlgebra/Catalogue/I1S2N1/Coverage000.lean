/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Data
public import Cslib.Foundations.RelationAlgebra.FastCatalogueCoverage

/-!
# Profile coverage for models 1–64 of the ⟨1, 2, 1⟩ row

The balanced word contains exactly the cycle profiles of this block and its atom renamings.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S2N1.Coverage000

/-- The cycle profiles covered by this block of models. -/
def word : ℕ :=
  (Code.joinWords 8192
    (Code.joinWords 4096
      (Code.joinWords 2048
        (Code.joinWords 1024
          (Code.joinWords 512
            (Nat.shiftLeft
              (Nat.shiftLeft
                172799639452039063477494917836444794880
                128)
              256)
            (Nat.shiftLeft
              (Nat.shiftLeft
                170141183460469231731687303715884105728
                128)
              256))
          (Code.joinWords 512
            (Code.joinWords 256
              (Nat.shiftLeft
                256
                128)
              (Nat.shiftLeft
                180775007426748719275378177766064128000
                128))
            (Code.joinWords 256
              (Nat.shiftLeft
                256
                128)
              (Nat.shiftLeft
                180775007426748719275378177766064128000
                128))))
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
            (Nat.shiftLeft
              (Nat.shiftLeft
                170141183460469231731687303715884105728
                128)
              256)
            (Nat.shiftLeft
              (Nat.shiftLeft
                170141183460469231731687303715884105728
                128)
              256))))
      (Code.joinWords 2048
        (Code.joinWords 1024
          (Code.joinWords 512
            (Code.joinWords 256
              192
              (Code.joinWords 128
                14167099448608935641088
                255211775190703851360666746610574688256))
            (Nat.shiftLeft
              (Nat.shiftLeft
                256208696187542534502208810869036417024
                128)
              256))
          (Code.joinWords 512
            (Nat.shiftLeft
              (Nat.shiftLeft
                255211775190703847597530955573826158592
                128)
              256)
            (Nat.shiftLeft
              (Code.joinWords 128
                255211775190703847597530955573826158592
                256208696187542534502208810869036417024)
              256)))
        (Code.joinWords 1024
          (Code.joinWords 512
            (Nat.shiftLeft
              (Nat.shiftLeft
                255211775190703847597530955573826158592
                128)
              256)
            (Nat.shiftLeft
              (Nat.shiftLeft
                256208696187542534502208810869036417024
                128)
              256))
          (Code.joinWords 512
            (Nat.shiftLeft
              (Nat.shiftLeft
                255211775190703847611366013629108322304
                128)
              256)
            (Nat.shiftLeft
              (Nat.shiftLeft
                256208696187542534516043868924318580736
                128)
              256)))))
    (Code.joinWords 4096
      (Code.joinWords 2048
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
            (Nat.shiftLeft
              (Nat.shiftLeft
                170141183460469231731687303715884105728
                128)
              256)
            (Nat.shiftLeft
              (Nat.shiftLeft
                170141183460469231731687303715884105728
                128)
              256)))
        (Code.joinWords 1024
          (Code.joinWords 512
            (Code.joinWords 256
              (Nat.shiftLeft
                4
                128)
              (Nat.shiftLeft
                170141183460469234240444497740383125504
                128))
            (Code.joinWords 256
              (Nat.shiftLeft
                4
                128)
              (Nat.shiftLeft
                170141183460469234240444497740383125504
                128)))
          (Code.joinWords 512
            (Code.joinWords 256
              (Nat.shiftLeft
                9223372036854775808
                128)
              (Nat.shiftLeft
                170141183460469231731687303715884105728
                128))
            (Code.joinWords 256
              (Nat.shiftLeft
                9223372036854775808
                128)
              (Nat.shiftLeft
                170141183460469231731687303715884105728
                128)))))
      (Code.joinWords 2048
        (Code.joinWords 1024
          (Code.joinWords 512
            (Nat.shiftLeft
              (Nat.shiftLeft
                255211775190703847597530955573826158592
                128)
              256)
            (Nat.shiftLeft
              (Nat.shiftLeft
                256208696187542534502208810869036417024
                128)
              256))
          (Code.joinWords 512
            (Code.joinWords 256
              (Nat.shiftLeft
                255211775190703847597530955573826158592
                128)
              (Nat.shiftLeft
                255211775190703847597530955573826158592
                128))
            (Code.joinWords 256
              (Nat.shiftLeft
                255211775190703847597530955573826158592
                128)
              (Nat.shiftLeft
                256208696187542534502208810869036417024
                128))))
        (Code.joinWords 1024
          (Code.joinWords 512
            (Code.joinWords 256
              (Nat.shiftLeft
                256
                128)
              (Nat.shiftLeft
                42535295865117374046052586104004018176
                128))
            (Code.joinWords 256
              (Code.joinWords 128
                13836183955189006528
                256)
              (Code.joinWords 128
                14167099448608935641088
                18963252907773419061248)))
          (Code.joinWords 512
            (Code.joinWords 256
              (Nat.shiftLeft
                316356262996809977768255787727748858112
                128)
              (Nat.shiftLeft
                17149707381026848768
                128))
            (Code.joinWords 256
              (Code.joinWords 128
                271162511140122838087076389480927592640
                316356262996809977768255787727748858112)
              (Code.joinWords 128
                271162511140122852254175838089863233536
                20769187434139327663829366343729152)))))))

/-- The block word is computed from the verified profile data. -/
theorem word_eq :
    Code.profileWord 64 4 (fun i q => Data.profiles (0 + i) q) = word := by
  decide +kernel

end Cslib.RelationAlgebra.Catalogue.I1S2N1.Coverage000
