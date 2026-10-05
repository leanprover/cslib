/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Data
public import Cslib.Foundations.RelationAlgebra.FastCatalogueCoverage

/-!
# Profile coverage for models 1281–1316 of the ⟨1, 2, 1⟩ row

The balanced word contains exactly the cycle profiles of this block and its atom renamings.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S2N1.Coverage020

/-- The cycle profiles covered by this block of models. -/
def word : ℕ :=
  (Nat.shiftLeft
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
                    333609960028494006205622197411005857792
                    128)
                  256)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    333609960028494015650355163150296285184
                    128)
                  256)))
            2048)
          4096)
        8192)
      16384)
    32768)

/-- The block word is computed from the verified profile data. -/
theorem word_eq :
    Code.profileWord 36 4 (fun i q => Data.profiles (1280 + i) q) = word := by
  decide +kernel

end Cslib.RelationAlgebra.Catalogue.I1S2N1.Coverage020
