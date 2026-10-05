/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Data
public import Cslib.Foundations.RelationAlgebra.FastCatalogueCoverage

/-!
# Profile coverage for models 769–832 of the ⟨1, 2, 1⟩ row

The balanced word contains exactly the cycle profiles of this block and its atom renamings.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S2N1.Coverage012

/-- The cycle profiles covered by this block of models. -/
def word : ℕ :=
  (Nat.shiftLeft
    (Nat.shiftLeft
      (Code.joinWords 8192
        (Code.joinWords 4096
          (Code.joinWords 2048
            (Nat.shiftLeft
              (Code.joinWords 512
                (Code.joinWords 256
                  (Nat.shiftLeft
                    151115727451828646838272
                    128)
                  (Code.joinWords 128
                    240840690626351905898496
                    312077810385377515903521094853705342976))
                (Code.joinWords 256
                  (Code.joinWords 128
                    11565243843087474816
                    226673591177742970269952)
                  (Code.joinWords 128
                    240840690626351905898496
                    312077810385377515903521094853705347072)))
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
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    311039351082994956476333624508584820736
                    128)
                  256)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    56294999100227584
                    128)
                  256))))
          (Code.joinWords 2048
            (Code.joinWords 1024
              128
              (Code.joinWords 512
                128
                128))
            (Code.joinWords 1024
              (Nat.shiftLeft
                (Nat.shiftLeft
                  6935543426150563840
                  256)
                512)
              (Code.joinWords 512
                (Code.joinWords 256
                  128
                  6917529030862307328)
                (Code.joinWords 256
                  192
                  6935543429384372224)))))
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
                    311043894273421532233665816289888698368
                    128)
                  (Nat.shiftLeft
                    311043894273421532233665816289888698368
                    128))
                (Nat.shiftLeft
                  1043002631458183499881063450132086784
                  128)))
            (Code.joinWords 1024
              (Code.joinWords 512
                192
                192)
              (Code.joinWords 512
                192
                192)))
          (Code.joinWords 2048
            (Code.joinWords 1024
              (Nat.shiftLeft
                127938194594298152766991429551983165440
                512)
              (Code.joinWords 512
                127609781817995824919486875659159994496
                127942104028749256626465645384668545216))
            (Code.joinWords 1024
              (Nat.shiftLeft
                (Code.joinWords 256
                  85402898729180844851417469387643289792
                  4629700416936869888)
                512)
              (Code.joinWords 512
                (Code.joinWords 256
                  85071889804449249590044607051127062720
                  4611686019501129728)
                (Code.joinWords 256
                  101354937823416869946087892721902551232
                  5494391546469941248))))))
      16384)
    32768)

/-- The block word is computed from the verified profile data. -/
theorem word_eq :
    Code.profileWord 64 4 (fun i q => Data.profiles (768 + i) q) = word := by
  decide +kernel

end Cslib.RelationAlgebra.Catalogue.I1S2N1.Coverage012
