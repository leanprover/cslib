/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Data
public import Cslib.Foundations.RelationAlgebra.FastCatalogueCoverage

/-!
# Profile coverage for models 1025–1088 of the ⟨1, 2, 1⟩ row

The balanced word contains exactly the cycle profiles of this block and its atom renamings.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S2N1.Coverage016

/-- The cycle profiles covered by this block of models. -/
def word : ℕ :=
  (Nat.shiftLeft
    (Nat.shiftLeft
      (Code.joinWords 8192
        (Nat.shiftLeft
          (Nat.shiftLeft
            (Code.joinWords 1024
              (Code.joinWords 512
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    319014718988379809514207517036385402880
                    128)
                  256)
                (Code.joinWords 256
                  (Nat.shiftLeft
                    320260870234428168127761013586295521280
                    128)
                  (Code.joinWords 128
                    320260870234428168127761013586295521280
                    333605073160862675150445765715904430080)))
              (Code.joinWords 512
                (Code.joinWords 256
                  (Nat.shiftLeft
                    333609940998820787177050398489401360384
                    128)
                  (Code.joinWords 128
                    1298133867883517070843229719494656
                    1012746966204940288))
                (Code.joinWords 256
                  (Nat.shiftLeft
                    120099448950563267062565716540530884608
                    128)
                  (Nat.shiftLeft
                    1012746966204940288
                    128))))
            2048)
          4096)
        (Code.joinWords 4096
          (Nat.shiftLeft
            (Code.joinWords 1024
              (Code.joinWords 512
                (Code.joinWords 256
                  (Nat.shiftLeft
                    1180591620717411303424
                    128)
                  (Nat.shiftLeft
                    64
                    128))
                (Code.joinWords 256
                  (Nat.shiftLeft
                    1180591620717411303424
                    128)
                  (Nat.shiftLeft
                    64
                    128)))
              (Code.joinWords 512
                (Code.joinWords 256
                  (Nat.shiftLeft
                    13345825539009839767523375744584515584
                    128)
                  (Nat.shiftLeft
                    723461060232740864
                    128))
                (Code.joinWords 256
                  (Nat.shiftLeft
                    13345825519202799138957291346198528000
                    128)
                  (Nat.shiftLeft
                    723390691488563200
                    128))))
            2048)
          (Code.joinWords 2048
            (Code.joinWords 1024
              (Code.joinWords 512
                (Code.joinWords 256
                  (Nat.shiftLeft
                    319014718988379809496913694467282698240
                    128)
                  (Nat.shiftLeft
                    319014718988379809496913694467282698240
                    128))
                (Code.joinWords 256
                  (Nat.shiftLeft
                    320260870234428168127761013586295521280
                    128)
                  (Code.joinWords 128
                    320260870234428168127761013586295521280
                    333605073160862675150445765715904430080)))
              (Code.joinWords 512
                (Code.joinWords 256
                  (Nat.shiftLeft
                    18681884097008309807452725792533905408
                    128)
                  (Code.joinWords 128
                    3909454258158655139748840007008256
                    18084979188552433664))
                (Code.joinWords 256
                  (Nat.shiftLeft
                    18681884097008309807452725792533905408
                    128)
                  (Nat.shiftLeft
                    6510586856281735168
                    128))))
            (Code.joinWords 1024
              (Nat.shiftLeft
                (Code.joinWords 256
                  (Nat.shiftLeft
                    13344202926434507005323375566095646720
                    128)
                  (Nat.shiftLeft
                    723390690146385920
                    128))
                512)
              (Code.joinWords 512
                (Code.joinWords 256
                  (Nat.shiftLeft
                    18681884097008309807452725792533905408
                    128)
                  (Nat.shiftLeft
                    1012746966204940288
                    128))
                (Code.joinWords 256
                  (Nat.shiftLeft
                    18681884097008309807452725792533905408
                    128)
                  (Nat.shiftLeft
                    1012746966204940288
                    128)))))))
      16384)
    32768)

/-- The block word is computed from the verified profile data. -/
theorem word_eq :
    Code.profileWord 64 4 (fun i q => Data.profiles (1024 + i) q) = word := by
  decide +kernel

end Cslib.RelationAlgebra.Catalogue.I1S2N1.Coverage016
