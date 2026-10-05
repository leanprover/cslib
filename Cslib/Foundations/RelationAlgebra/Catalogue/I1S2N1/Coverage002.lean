/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Data
public import Cslib.Foundations.RelationAlgebra.FastCatalogueCoverage

/-!
# Profile coverage for models 129–192 of the ⟨1, 2, 1⟩ row

The balanced word contains exactly the cycle profiles of this block and its atom renamings.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S2N1.Coverage002

/-- The cycle profiles covered by this block of models. -/
def word : ℕ :=
  (Nat.shiftLeft
    (Code.joinWords 8192
      (Code.joinWords 4096
        (Code.joinWords 2048
          (Nat.shiftLeft
            (Nat.shiftLeft
              (Code.joinWords 256
                (Nat.shiftLeft
                  226673591177742970269696
                  128)
                (Code.joinWords 128
                  240840690626351905898496
                  312077810385377515903521094853705347072))
              512)
            1024)
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
                297747071095435236787584950299569160192
                (Nat.shiftLeft
                  311039351013670314275631753170096488448
                  128))
              (Code.joinWords 256
                298748535352180488634258249628017229824
                (Code.joinWords 128
                  4867778304890568001336824171593728
                  312077810385377279801391895631468953600)))))
        (Code.joinWords 2048
          (Code.joinWords 1024
            (Code.joinWords 256
              (Nat.shiftLeft
                21267647932558653983754735533588217856
                128)
              (Nat.shiftLeft
                1152921504606846976
                128))
            (Code.joinWords 512
              (Code.joinWords 128
                128
                289356276058554368)
              (Code.joinWords 128
                128
                289356276058554368)))
          (Nat.shiftLeft
            (Code.joinWords 512
              (Code.joinWords 256
                (Code.joinWords 128
                  128
                  1125899906842624)
                16140901064495857664)
              (Code.joinWords 256
                128
                16194944260024303616))
            1024)))
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
                (Nat.shiftLeft
                  297747071055821155530452781502797185024
                  128)
                (Code.joinWords 128
                  16141041801984212992
                  311039351013670314259490852105600630784))
              (Code.joinWords 256
                (Code.joinWords 128
                  39652766883359836930362572800
                  298743992052659842435130636798007443456)
                (Code.joinWords 128
                  74276416540417350653909696512
                  312077810385377279785196951371444649984))))
          (Code.joinWords 1024
            (Code.joinWords 512
              (Code.joinWords 256
                2361183241434822606976
                128)
              (Code.joinWords 256
                2361183241434822606976
                128))
            (Code.joinWords 512
              (Code.joinWords 256
                39768823762042841331134365824
                141287244169216)
              (Code.joinWords 256
                39768823762042841331134365824
                141287244169216))))
        (Code.joinWords 2048
          (Nat.shiftLeft
            (Code.joinWords 512
              (Code.joinWords 128
                297747071055821155530452781502797185152
                1125899906842624)
              298743992052659842435130636798007443584)
            1024)
          (Code.joinWords 1024
            (Nat.shiftLeft
              (Code.joinWords 256
                298743992052659842446695880641094877312
                16194944260024303616)
              512)
            (Code.joinWords 512
              (Code.joinWords 256
                297747071055821155541981996548865654912
                16140901064495857664)
              (Code.joinWords 256
                314694728002078832921541565364459012224
                17059635388479438848))))))
    16384)

/-- The block word is computed from the verified profile data. -/
theorem word_eq :
    Code.profileWord 64 4 (fun i q => Data.profiles (128 + i) q) = word := by
  decide +kernel

end Cslib.RelationAlgebra.Catalogue.I1S2N1.Coverage002
