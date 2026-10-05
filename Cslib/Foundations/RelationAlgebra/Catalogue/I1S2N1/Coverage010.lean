/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Data
public import Cslib.Foundations.RelationAlgebra.FastCatalogueCoverage

/-!
# Profile coverage for models 641–704 of the ⟨1, 2, 1⟩ row

The balanced word contains exactly the cycle profiles of this block and its atom renamings.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S2N1.Coverage010

/-- The cycle profiles covered by this block of models. -/
def word : ℕ :=
  (Nat.shiftLeft
    (Code.joinWords 8192
      (Code.joinWords 4096
        (Nat.shiftLeft
          (Nat.shiftLeft
            (Nat.shiftLeft
              (Nat.shiftLeft
                (Nat.shiftLeft
                  255211775190703847597530955573826158592
                  128)
                256)
              512)
            1024)
          2048)
        (Code.joinWords 2048
          (Code.joinWords 1024
            (Code.joinWords 512
              (Nat.shiftLeft
                (Nat.shiftLeft
                  255211775190703847597530955573826158592
                  128)
                256)
              (Nat.shiftLeft
                (Code.joinWords 128
                  256208696187542534502208810869036417024
                  256208696187542534502208810869036417024)
                256))
            (Code.joinWords 512
              (Nat.shiftLeft
                (Code.joinWords 128
                  256208696187542534502208810869036417024
                  256208696187542534502208810869036417024)
                256)
              (Nat.shiftLeft
                (Code.joinWords 128
                  256208696187542534502208810869036417024
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
                  256208696187542534516043868924318580736
                  128)
                256)
              (Nat.shiftLeft
                (Nat.shiftLeft
                  256208696187542534516043868924318580736
                  128)
                256)))))
      (Code.joinWords 4096
        (Code.joinWords 2048
          (Nat.shiftLeft
            (Nat.shiftLeft
              (Nat.shiftLeft
                (Nat.shiftLeft
                  255211775190703847597530955573826158592
                  128)
                256)
              512)
            1024)
          (Code.joinWords 1024
            (Code.joinWords 512
              (Nat.shiftLeft
                (Code.joinWords 128
                  71056858171929192824832
                  319014718988379813038688556619516608512)
                256)
              (Nat.shiftLeft
                (Code.joinWords 128
                  71056858171929192824832
                  77095223755525124170195671648493895680)
                256))
            (Code.joinWords 512
              (Nat.shiftLeft
                18014398509481984000
                128)
              (Nat.shiftLeft
                18014398509481984000
                128))))
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
                  256208696187542534502208810869036417024
                  128))
              (Code.joinWords 256
                (Nat.shiftLeft
                  255211775190703847597530955573826158592
                  128)
                (Nat.shiftLeft
                  256208696187542534502208810869036417024
                  128))))
          (Code.joinWords 1024
            (Nat.shiftLeft
              (Nat.shiftLeft
                10675362341147605604258700452876517376
                256)
              512)
            (Code.joinWords 512
              (Code.joinWords 256
                (Code.joinWords 128
                  170141183460469231731687303715884105728
                  337623910929368631735869622196841218048)
                (Code.joinWords 128
                  5379219545442095599480414842862436352
                  18302628885633695744))
              (Code.joinWords 256
                (Code.joinWords 128
                  170141183460469231731687303715884105728
                  337623910929368631735869622196841218048)
                (Code.joinWords 128
                  5379219545442095599480414842862436352
                  18302628885633695744)))))))
    32768)

/-- The block word is computed from the verified profile data. -/
theorem word_eq :
    Code.profileWord 64 4 (fun i q => Data.profiles (640 + i) q) = word := by
  decide +kernel

end Cslib.RelationAlgebra.Catalogue.I1S2N1.Coverage010
