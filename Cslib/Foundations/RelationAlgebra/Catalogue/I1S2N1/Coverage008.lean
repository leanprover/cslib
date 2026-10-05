/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Data
public import Cslib.Foundations.RelationAlgebra.FastCatalogueCoverage

/-!
# Profile coverage for models 513–576 of the ⟨1, 2, 1⟩ row

The balanced word contains exactly the cycle profiles of this block and its atom renamings.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S2N1.Coverage008

/-- The cycle profiles covered by this block of models. -/
def word : ℕ :=
  (Nat.shiftLeft
    (Nat.shiftLeft
      (Code.joinWords 4096
        (Nat.shiftLeft
          (Code.joinWords 1024
            (Nat.shiftLeft
              (Nat.shiftLeft
                (Code.joinWords 128
                  40140115104391984316416
                  332306998946228971915300579811996467200)
                256)
              512)
            (Code.joinWords 512
              (Nat.shiftLeft
                (Code.joinWords 128
                  320264764516494097828545375625581428736
                  333605073160863581827449100124272197632)
                256)
              (Nat.shiftLeft
                (Code.joinWords 128
                  320264764516494107273278341364871856128
                  333605073160863581827449100124272197632)
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
                  330936232575575783176752679778462466048
                  29736151446819797204992)
                256))
            (Code.joinWords 512
              (Nat.shiftLeft
                (Code.joinWords 128
                  330936232575576689871117390750343495680
                  5337681170573812246862315965728686080)
                256)
              (Nat.shiftLeft
                (Code.joinWords 128
                  330936232575576689871117390750343495680
                  5337681170573802802129350226438258688)
                256)))
          2048))
      8192)
    16384)

/-- The block word is computed from the verified profile data. -/
theorem word_eq :
    Code.profileWord 64 4 (fun i q => Data.profiles (512 + i) q) = word := by
  decide +kernel

end Cslib.RelationAlgebra.Catalogue.I1S2N1.Coverage008
