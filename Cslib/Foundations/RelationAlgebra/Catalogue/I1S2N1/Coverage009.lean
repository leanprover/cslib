/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Data
public import Cslib.Foundations.RelationAlgebra.FastCatalogueCoverage

/-!
# Profile coverage for models 577–640 of the ⟨1, 2, 1⟩ row

The balanced word contains exactly the cycle profiles of this block and its atom renamings.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S2N1.Coverage009

/-- The cycle profiles covered by this block of models. -/
def word : ℕ :=
  (Code.joinWords 32768
    (Nat.shiftLeft
      (Nat.shiftLeft
        (Nat.shiftLeft
          (Nat.shiftLeft
            (Code.joinWords 1024
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    333605073160862715273199493544375484416
                    128)
                  256)
                512)
              (Code.joinWords 512
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    333609956225484177081592490720510345216
                    128)
                  256)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    333609956225484186526325456459800772608
                    128)
                  256)))
            2048)
          4096)
        8192)
      16384)
    (Code.joinWords 8192
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
            (Code.joinWords 256
              61632
              (Code.joinWords 128
                14167099448608935641088
                256208696187542761175799988612006674432))
            (Code.joinWords 256
              61632
              (Code.joinWords 128
                14167099448608935641088
                256208696187542761175799988612006674432))))
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
                255211775190703847597530955573826158592
                128)
              256)
            (Nat.shiftLeft
              (Nat.shiftLeft
                996920996838686904677855295210258432
                128)
              256))))
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
                  255211775190703847597530955573826158592
                  128)
                256)
              (Nat.shiftLeft
                (Nat.shiftLeft
                  996920996838686904677855295210258432
                  128)
                256)))
          (Code.joinWords 512
            192
            192))
        (Nat.shiftLeft
          (Nat.shiftLeft
            (Code.joinWords 512
              (Code.joinWords 256
                127605887595351923816059300356015784128
                6917529027641081856)
              (Code.joinWords 256
                143556623544770914291769676207835054272
                7782220156096217088))
            1024)
          2048))))

/-- The block word is computed from the verified profile data. -/
theorem word_eq :
    Code.profileWord 64 4 (fun i q => Data.profiles (576 + i) q) = word := by
  decide +kernel

end Cslib.RelationAlgebra.Catalogue.I1S2N1.Coverage009
