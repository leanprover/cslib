/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Data
public import Cslib.Foundations.RelationAlgebra.FastCatalogueCoverage

/-!
# Profile coverage for models 833–896 of the ⟨1, 2, 1⟩ row

The balanced word contains exactly the cycle profiles of this block and its atom renamings.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S2N1.Coverage013

/-- The cycle profiles covered by this block of models. -/
def word : ℕ :=
  (Nat.shiftLeft
    (Nat.shiftLeft
      (Code.joinWords 8192
        (Code.joinWords 4096
          (Nat.shiftLeft
            (Nat.shiftLeft
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    312077810454701922002039723770670743552
                    128)
                  256)
                512)
              1024)
            2048)
          (Code.joinWords 2048
            (Code.joinWords 1024
              (Code.joinWords 512
                (Code.joinWords 256
                  (Nat.shiftLeft
                    319014718988379809514207517036385402880
                    128)
                  (Code.joinWords 128
                    14167099448608935641088
                    319014718988379813277343308073133932544))
                (Code.joinWords 256
                  (Nat.shiftLeft
                    320260870234428168145122390149808783360
                    128)
                  (Code.joinWords 128
                    320260870234428168127761013586295521280
                    1298074214633706924494000645818286080)))
              (Code.joinWords 512
                (Nat.shiftLeft
                  1012746966204940288
                  128)
                (Nat.shiftLeft
                  1012746966204940288
                  128)))
            (Code.joinWords 1024
              (Nat.shiftLeft
                (Nat.shiftLeft
                  9259400833873739776
                  256)
                512)
              (Code.joinWords 512
                (Code.joinWords 256
                  (Nat.shiftLeft
                    1012746966204940288
                    128)
                  9223372036854775808)
                (Code.joinWords 256
                  (Nat.shiftLeft
                    1012746966204940288
                    128)
                  9259400833873739776)))))
        (Code.joinWords 4096
          (Code.joinWords 2048
            (Nat.shiftLeft
              (Nat.shiftLeft
                (Code.joinWords 256
                  (Nat.shiftLeft
                    311039351013670314259490852105600630784
                    128)
                  (Nat.shiftLeft
                    312082353645128497759371915555732717568
                    128))
                512)
              1024)
            (Code.joinWords 1024
              (Code.joinWords 512
                (Nat.shiftLeft
                  4
                  128)
                (Nat.shiftLeft
                  4
                  128))
              (Code.joinWords 512
                (Nat.shiftLeft
                  723390690146385920
                  128)
                (Nat.shiftLeft
                  723390690146385920
                  128))))
          (Code.joinWords 2048
            (Code.joinWords 1024
              (Nat.shiftLeft
                170805797458361689668139207246024278016
                512)
              (Code.joinWords 512
                (Code.joinWords 128
                  170141183460469231731687303715884105728
                  1012746966204940288)
                (Code.joinWords 128
                  170805797458361689668139207246024278016
                  1012746966204940288)))
            (Code.joinWords 1024
              (Code.joinWords 512
                (Nat.shiftLeft
                  256
                  128)
                (Code.joinWords 256
                  (Code.joinWords 128
                    213341093323478997601061033174995304448
                    144678138029277440)
                  11565243843087433728))
              (Code.joinWords 512
                (Code.joinWords 256
                  (Code.joinWords 128
                    212679075474015807078423394893019742208
                    434034414087831808)
                  11529215048215953408)
                (Code.joinWords 256
                  (Code.joinWords 128
                    213343699613113066840710510396785557504
                    434034414087831808)
                  11565243845243305984))))))
      16384)
    32768)

/-- The block word is computed from the verified profile data. -/
theorem word_eq :
    Code.profileWord 64 4 (fun i q => Data.profiles (832 + i) q) = word := by
  decide +kernel

end Cslib.RelationAlgebra.Catalogue.I1S2N1.Coverage013
