/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Data
public import Cslib.Foundations.RelationAlgebra.FastCatalogueCoverage

/-!
# Profile coverage for models 321–384 of the ⟨1, 2, 1⟩ row

The balanced word contains exactly the cycle profiles of this block and its atom renamings.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S2N1.Coverage005

/-- The cycle profiles covered by this block of models. -/
def word : ℕ :=
  (Nat.shiftLeft
    (Code.joinWords 8192
      (Nat.shiftLeft
        (Code.joinWords 2048
          (Nat.shiftLeft
            (Nat.shiftLeft
              (Nat.shiftLeft
                (Code.joinWords 128
                  170141183460469231731687303715884105728
                  338947622184018663387603014184966553600)
                256)
              512)
            1024)
          (Code.joinWords 1024
            (Code.joinWords 512
              (Code.joinWords 256
                (Nat.shiftLeft
                  319014718988379809496913694467282698240
                  128)
                (Nat.shiftLeft
                  319014718988379809514207517036385402880
                  128))
              (Code.joinWords 256
                (Nat.shiftLeft
                  320260870234428168127761013586295521280
                  128)
                (Nat.shiftLeft
                  333605073160862675150445765715904430080
                  128)))
            (Code.joinWords 512
              (Code.joinWords 256
                (Nat.shiftLeft
                  18683506709815756327018734772566360064
                  128)
                (Nat.shiftLeft
                  1012746966204940288
                  128))
              (Code.joinWords 256
                (Nat.shiftLeft
                  18682208615561968234179508948554481664
                  128)
                (Nat.shiftLeft
                  1012746966204940288
                  128)))))
        4096)
      (Code.joinWords 4096
        (Nat.shiftLeft
          (Nat.shiftLeft
            (Nat.shiftLeft
              (Nat.shiftLeft
                9223372036854775808
                128)
              512)
            1024)
          2048)
        (Code.joinWords 2048
          (Code.joinWords 1024
            (Code.joinWords 512
              (Code.joinWords 256
                (Nat.shiftLeft
                  319014718988379809496913694467282698240
                  128)
                (Nat.shiftLeft
                  319014718988379809514207517036385402880
                  128))
              (Code.joinWords 256
                (Nat.shiftLeft
                  320260870234428168127761013586295521280
                  128)
                (Nat.shiftLeft
                  333605073160862675150445765715904430080
                  128)))
            (Code.joinWords 512
              (Code.joinWords 256
                (Nat.shiftLeft
                  18681884097008309807452725792533905408
                  128)
                (Nat.shiftLeft
                  1012818160925016064
                  128))
              (Code.joinWords 256
                (Nat.shiftLeft
                  18681884097008309807452725792533905408
                  128)
                (Nat.shiftLeft
                  1012746966473375744
                  128))))
          (Code.joinWords 1024
            (Code.joinWords 512
              (Nat.shiftLeft
                11529215046068469760
                128)
              (Code.joinWords 256
                (Nat.shiftLeft
                  13344202926434507016897626608437821440
                  128)
                (Nat.shiftLeft
                  723390690146385920
                  128)))
            (Code.joinWords 512
              (Code.joinWords 256
                (Nat.shiftLeft
                  18681884097008309819027118124276154368
                  128)
                (Nat.shiftLeft
                  1012746966204940288
                  128))
              (Code.joinWords 256
                (Nat.shiftLeft
                  18681884097008309819027118124276154368
                  128)
                (Nat.shiftLeft
                  1012746966204940288
                  128)))))))
    16384)

/-- The block word is computed from the verified profile data. -/
theorem word_eq :
    Code.profileWord 64 4 (fun i q => Data.profiles (320 + i) q) = word := by
  decide +kernel

end Cslib.RelationAlgebra.Catalogue.I1S2N1.Coverage005
