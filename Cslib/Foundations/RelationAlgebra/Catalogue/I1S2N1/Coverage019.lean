/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Data
public import Cslib.Foundations.RelationAlgebra.FastCatalogueCoverage

/-!
# Profile coverage for models 1217–1280 of the ⟨1, 2, 1⟩ row

The balanced word contains exactly the cycle profiles of this block and its atom renamings.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S2N1.Coverage019

/-- The cycle profiles covered by this block of models. -/
def word : ℕ :=
  (Nat.shiftLeft
    (Nat.shiftLeft
      (Nat.shiftLeft
        (Code.joinWords 4096
          (Nat.shiftLeft
            (Code.joinWords 1024
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    332306998946228968225951765070086144000
                    128)
                  256)
                512)
              (Code.joinWords 512
                (Nat.shiftLeft
                  (Code.joinWords 128
                    320260870234429074822125724558176550912
                    333609941013444860585473663958528294912)
                  256)
                (Nat.shiftLeft
                  (Code.joinWords 128
                    320260870234429074822125724558176550912
                    333609941013444860585473663958528294912)
                  256)))
            2048)
          (Nat.shiftLeft
            (Code.joinWords 1024
              (Code.joinWords 512
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    319014718988379875610044454642315689984
                    128)
                  256)
                (Nat.shiftLeft
                  (Code.joinWords 128
                    330936232575575773732019714039172038656
                    29736151446819797204992)
                  256))
              (Code.joinWords 512
                (Nat.shiftLeft
                  (Code.joinWords 128
                    330940142069681019928922902840439996416
                    5337681170573812246862315965728686080)
                  256)
                (Nat.shiftLeft
                  (Code.joinWords 128
                    330940142069681019928922902840439996416
                    5337681170573802802129350226438258688)
                  256)))
            2048))
        8192)
      16384)
    32768)

/-- The block word is computed from the verified profile data. -/
theorem word_eq :
    Code.profileWord 64 4 (fun i q => Data.profiles (1216 + i) q) = word := by
  decide +kernel

end Cslib.RelationAlgebra.Catalogue.I1S2N1.Coverage019
