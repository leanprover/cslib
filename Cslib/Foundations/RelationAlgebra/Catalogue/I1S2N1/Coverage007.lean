/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Data
public import Cslib.Foundations.RelationAlgebra.FastCatalogueCoverage

/-!
# Profile coverage for models 449–512 of the ⟨1, 2, 1⟩ row

The balanced word contains exactly the cycle profiles of this block and its atom renamings.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S2N1.Coverage007

/-- The cycle profiles covered by this block of models. -/
def word : ℕ :=
  (Nat.shiftLeft
    (Code.joinWords 8192
      (Nat.shiftLeft
        (Nat.shiftLeft
          (Nat.shiftLeft
            (Nat.shiftLeft
              (Code.joinWords 256
                (Nat.shiftLeft
                  213507246822952112085174009057530347520
                  128)
                (Code.joinWords 128
                  336273913746149590701248512874545938432
                  338947622184250777156543274031545057280))
              512)
            1024)
          2048)
        4096)
      (Code.joinWords 4096
        (Nat.shiftLeft
          (Code.joinWords 1024
            (Code.joinWords 512
              (Code.joinWords 256
                (Nat.shiftLeft
                  212676479325586542025792371079677739008
                  128)
                (Code.joinWords 128
                  74598633034081426735104
                  319014718988379813197791724255261491328))
              (Code.joinWords 256
                (Nat.shiftLeft
                  212676479325586542025792371079677739008
                  128)
                (Code.joinWords 128
                  34458517929689442418688
                  11529215046068469888)))
            (Code.joinWords 512
              (Code.joinWords 256
                (Nat.shiftLeft
                  213507246822952112085174009057530347520
                  128)
                (Code.joinWords 128
                  14167099448608935641088
                  11574251042342174720))
              (Code.joinWords 256
                (Nat.shiftLeft
                  213507246822952112085174009057530347520
                  128)
                (Code.joinWords 128
                  4722366482869645213696
                  11574251042342174720))))
          2048)
        (Code.joinWords 2048
          (Nat.shiftLeft
            (Nat.shiftLeft
              (Code.joinWords 256
                (Nat.shiftLeft
                  213510502149693498178277052591361753088
                  128)
                (Code.joinWords 128
                  336273913746149590701248512874545938432
                  338947637395825866137930083187747192832))
              512)
            1024)
          (Code.joinWords 1024
            (Code.joinWords 512
              (Code.joinWords 256
                (Nat.shiftLeft
                  212676479325586539664609129644855132160
                  128)
                (Nat.shiftLeft
                  11529215046068469760
                  128))
              (Code.joinWords 256
                (Nat.shiftLeft
                  213507246822952112085174009057530347520
                  128)
                (Code.joinWords 128
                  4722366482869645213696
                  11574251042342174720)))
            (Code.joinWords 512
              (Code.joinWords 256
                (Nat.shiftLeft
                  213510502189462926403229701237083471872
                  128)
                (Code.joinWords 128
                  5337681170573807524495833096083472384
                  11574392332279119872))
              (Code.joinWords 256
                (Nat.shiftLeft
                  213510502189462926403229701237083471872
                  128)
                (Code.joinWords 128
                  5337681170573807524495833096083472384
                  11574392332279119872)))))))
    16384)

/-- The block word is computed from the verified profile data. -/
theorem word_eq :
    Code.profileWord 64 4 (fun i q => Data.profiles (448 + i) q) = word := by
  decide +kernel

end Cslib.RelationAlgebra.Catalogue.I1S2N1.Coverage007
