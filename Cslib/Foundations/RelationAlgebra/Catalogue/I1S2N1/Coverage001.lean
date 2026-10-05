/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Data
public import Cslib.Foundations.RelationAlgebra.FastCatalogueCoverage

/-!
# Profile coverage for models 65–128 of the ⟨1, 2, 1⟩ row

The balanced word contains exactly the cycle profiles of this block and its atom renamings.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S2N1.Coverage001

/-- The cycle profiles covered by this block of models. -/
def word : ℕ :=
  (Code.joinWords 16384
    (Nat.shiftLeft
      (Nat.shiftLeft
        (Nat.shiftLeft
          (Code.joinWords 1024
            (Code.joinWords 512
              (Nat.shiftLeft
                (Nat.shiftLeft
                  255211775190703847597530955573826158592
                  128)
                256)
              (Nat.shiftLeft
                (Nat.shiftLeft
                  312077810385377330698210594809807110144
                  128)
                256))
            (Code.joinWords 512
              (Nat.shiftLeft
                (Nat.shiftLeft
                  316360806325886754064360016636532490240
                  128)
                256)
              (Nat.shiftLeft
                (Nat.shiftLeft
                  317399280909633036086184942664358559744
                  128)
                256)))
          2048)
        4096)
      8192)
    (Code.joinWords 8192
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
              (Code.joinWords 256
                (Code.joinWords 128
                  151131872856561490653376
                  226673591177742970269696)
                (Code.joinWords 128
                  240840690626351905906688
                  312077810385377515903521094853705347072))
              (Code.joinWords 256
                151131922536828307042496
                8192)))
          (Nat.shiftLeft
            (Nat.shiftLeft
              192
              512)
            1024))
        (Code.joinWords 2048
          (Nat.shiftLeft
            (Code.joinWords 512
              64
              64)
            1024)
          (Nat.shiftLeft
            (Code.joinWords 512
              64
              64)
            1024)))
      (Code.joinWords 4096
        (Code.joinWords 2048
          (Nat.shiftLeft
            (Nat.shiftLeft
              192
              512)
            1024)
          (Code.joinWords 1024
            (Code.joinWords 512
              64
              64)
            (Code.joinWords 512
              64
              64)))
        (Code.joinWords 2048
          (Nat.shiftLeft
            (Code.joinWords 512
              64
              64)
            1024)
          (Code.joinWords 1024
            (Nat.shiftLeft
              5782621921543716928
              512)
            (Code.joinWords 512
              5764607523034234944
              6647313049998852160))))))

/-- The block word is computed from the verified profile data. -/
theorem word_eq :
    Code.profileWord 64 4 (fun i q => Data.profiles (64 + i) q) = word := by
  decide +kernel

end Cslib.RelationAlgebra.Catalogue.I1S2N1.Coverage001
