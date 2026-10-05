/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Cslib.Foundations.RelationAlgebra.FastCatalogueCoverage

/-!
# Profile coverage for models 3009–3013 of the ⟨1, 4, 0⟩ row

The balanced word contains exactly the cycle profiles of this block and its atom renamings.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage047

/-- The cycle profiles covered by this block of models. -/
def word : ℕ :=
  (Nat.shiftLeft
    (Nat.shiftLeft
      (Nat.shiftLeft
        (Nat.shiftLeft
          (Nat.shiftLeft
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            170141183500083312998042844551658340352
                            128)
                          (Nat.shiftLeft
                            170141183500083312998042844551658340352
                            128))
                        512)
                      1024)
                    2048)
                  4096)
                8192)
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            170141183500083312998042844551658340352
                            128)
                          (Nat.shiftLeft
                            170141183500083312998042844551658340352
                            128))
                        512)
                      1024)
                    2048)
                  4096)
                8192))
            32768)
          65536)
        131072)
      262144)
    524288)

/-- The block word is computed from the verified profile data. -/
theorem word_eq :
    Code.profileWord 5 24 (fun i q => Data.profiles (3008 + i) q) = word := by
  decide +kernel

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage047
