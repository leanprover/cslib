/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Cslib.Foundations.RelationAlgebra.FastCatalogueCoverage

/-!
# Profile coverage for models 1–64 of the ⟨1, 4, 0⟩ row

The balanced word contains exactly the cycle profiles of this block and its atom renamings.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage000

/-- The cycle profiles covered by this block of models. -/
def word : ℕ :=
  (Code.joinWords 524288
    (Code.joinWords 262144
      (Code.joinWords 131072
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170151568054186301386944364708542545920
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170141183460469231731687303715884105728
                            128)
                          256)
                        512))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170141183460469231731687303715884105728
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170141183460469231731687303715884105728
                            128)
                          256)
                        512)))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170141183460469231731687303715884105728
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170141183460469231731687303715884105728
                            128)
                          256)
                        512))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            65536
                            131072)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            131072
                            170182721835337510352715547687054868480)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            65536
                            131072)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            131072
                            170182721835337510352715547687054868480)
                          256)))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170141183460469231731687303715884105728
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170141183460469231731687303715884105728
                            128)
                          256)
                        512))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170141183460469231731687303715884105728
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170141183460469231731687303715884105728
                            128)
                          256)
                        512)))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            17179869184
                            34359738368)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            170141183460469231731687303715884105728
                            170141183460469231731687303715884105728)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            17179869184
                            34359738368)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            170141183460469231731687303715884105728
                            170141183460469231731687303715884105728)
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1125899906842624
                            2251799813685248)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            170141183460469231731687303715884105728
                            170141183460469231731687303715884105728)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1125899906842624
                            2251799813685248)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            170141183460469231731687303715884105728
                            170141183460469231731687303715884105728)
                          256))))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 128
                          49152
                          14051230837395947520)
                        (Code.joinWords 256
                          (Code.joinWords 128
                            59479150325039755395543859200
                            196608)
                          (Nat.shiftLeft
                            255211775190703847597530955573826207756
                            128)))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            255215669413347748718252353446073073664
                            128)
                          256)
                        512))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            58028439341502200385896448
                            128)
                          (Nat.shiftLeft
                            255211775190703847597530955573826158592
                            128))
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            255215669413347748718252353446073073664
                            128)
                          256)
                        512)))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            216172782113783808
                            128)
                          (Nat.shiftLeft
                            255211775190703847597530955573826158592
                            128))
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            255215669413347748718252353446073073664
                            128)
                          256)
                        512))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            255211775190703847597530955573826158592
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            255211775190703847597530955573826158592
                            128)
                          (Nat.shiftLeft
                            255215669413347748718252353446073073664
                            128))
                        512))))
                (Code.joinWords 4096
                  (Code.joinWords 1024
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          255211775190703847597530955573826945024
                          128)
                        256)
                      512)
                    (Code.joinWords 512
                      (Code.joinWords 128
                        49152
                        14051230837395947520)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          196608
                          128)
                        (Nat.shiftLeft
                          12
                          128))))
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        256208696187542534502208810869036417024
                        512)
                      1024)
                    2048))))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170141183460469231731687303715884105728
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170141183460469231731687303715884105728
                            128)
                          256)
                        512))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            73786976294838206464
                            170141183460469231731687303715884105728)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            147573952589676412928
                            170141183460469231731687303715884105728)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            73786976294838206464
                            170141183460469231731687303715884105728)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            147573952589676412928
                            170141183460469231731687303715884105728)
                          256))))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170141183460469231731687303715884105728
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170141183460469231731687303715884105728
                            128)
                          256)
                        512))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            4835703278458516698824704
                            170141183460469231731687303715884105728)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            9671406556917033397649408
                            170141183460469231731687303715884105728)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            4835703278458516698824704
                            170141183460469231731687303715884105728)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            9671406556917033397649408
                            170141183460469231731687303715884105728)
                          256)))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            4
                            8)
                          256)
                        (Nat.shiftLeft
                          8
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            4
                            8)
                          256)
                        (Nat.shiftLeft
                          8
                          256)))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        1180591620717411303424
                        256)
                      (Nat.shiftLeft
                        1180591620717411303424
                        256)))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        4398046511104
                        256)
                      (Nat.shiftLeft
                        4398046511104
                        256))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        170141183460469231731687303715884105728
                        256)
                      (Nat.shiftLeft
                        170141183460469231731687303715884105728
                        256)))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 1024
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          255211775190703847597530955573826945024
                          128)
                        256)
                      512)
                    (Code.joinWords 512
                      49152
                      (Code.joinWords 256
                        (Code.joinWords 128
                          59479150325039755395543859200
                          196608)
                        (Nat.shiftLeft
                          12
                          128))))
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        271162511140122838072376640297190293504
                        128)
                      1024)
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 1024
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          65536
                          393216)
                        256)
                      (Nat.shiftLeft
                        393216
                        256))
                    (Code.joinWords 512
                      (Code.joinWords 256
                        255211775507616497654588305948002009088
                        (Code.joinWords 128
                          65536
                          393216))
                      (Nat.shiftLeft
                        393216
                        256)))
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            317592029649141266726696338473076457472
                            20769187434139310514121985316880384)
                          256)
                        (Nat.shiftLeft
                          20769187434139310514121985316880384
                          256))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            272221739699263942908596861548351242240
                            272221739699263942908596861548351193088)
                          (Code.joinWords 128
                            317592029649141266726696338473076457472
                            20769187434139310514121985316880384))
                        (Code.joinWords 256
                          272221739699263942908596861548351193088
                          20769187434139310514121985316880384)))
                    2048)))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          128)
                        256)
                      512)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          128)
                        256)
                      512))
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        1048576
                        256)
                      (Nat.shiftLeft
                        1048576
                        256))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          128)
                        256)
                      512)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          128)
                        256)
                      512))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        274877906944
                        256)
                      (Nat.shiftLeft
                        274877906944
                        256))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        18014398509481984
                        256)
                      (Nat.shiftLeft
                        18014398509481984
                        256)))))
              (Code.joinWords 8192
                (Code.joinWords 2048
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        255211775190703847597530955573826158592
                        255211775190703847597530955573826158592)
                      256)
                    512)
                  (Code.joinWords 512
                    (Code.joinWords 128
                      49152
                      14051230837395947520)
                    (Code.joinWords 128
                      58028439341502200385896448
                      196608)))
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 128
                      255211775190703847597530955573826158592
                      255211775190703847597530955573826158592)
                    256)
                  512)))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Code.joinWords 1024
                    (Nat.shiftLeft
                      1180591620717411303424
                      256)
                    (Nat.shiftLeft
                      1180591620717411303424
                      256))
                  2048)
                (Code.joinWords 1024
                  (Nat.shiftLeft
                    64
                    256)
                  (Nat.shiftLeft
                    64
                    256)))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          20769187434139310514121985316880384
                          20769187434139310514121985316880384)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          20769187434139310514121985316880384
                          20769187434139310514121985316880384)
                        256))
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          20769187434139310514121985316880384
                          20769187434139310514121985316880384)
                        256)
                      (Code.joinWords 256
                        (Code.joinWords 128
                          353076186380368278740073750386966528
                          353076186380368278740073750386966528)
                        (Code.joinWords 128
                          20769187434139310514121985316880384
                          20769187434139310514121985316880384)))
                    2048)
                  4096)))))
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          128)
                        256)
                      512)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        166154767123714712342377379238248448
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170143779608898499145501568964048715776
                            128)
                          256))
                      5070602400912917605986812821504))
                  (Code.joinWords 1024
                    (Code.joinWords 128
                      144116287587483648
                      2199023255552)
                    4398046511104))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          2417870085973332058963968
                          128)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            2478297967103477955566764032
                            128)
                          (Nat.shiftLeft
                            170307336959942346215800279598419148800
                            128)))
                      (Nat.shiftLeft
                        73786976294838206464
                        128))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          166154767123714712342377379238248448
                          128)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170143779608898499145501568964048715776
                            128)
                          256))
                      (Nat.shiftLeft
                        5070602400912917605986812821504
                        128)))
                  (Nat.shiftLeft
                    1099511627776
                    1024)))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 256
                      (Nat.shiftLeft
                        216172782113783808
                        128)
                      (Nat.shiftLeft
                        255211775190703847597530955573826158592
                        128))
                    512)
                  (Nat.shiftLeft
                    (Code.joinWords 128
                      72620548286316544
                      1108101562368)
                    512))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        255211775190703847597530955573826158592
                        128)
                      256)
                    512)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      4294967296
                      512)
                    1024))))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 1024
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          1099511627776
                          2199023255552)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          170141183460469231731687303715884105728
                          170141183460469231731687303715884105728)
                        256))
                    (Nat.shiftLeft
                      4398046511104
                      256))
                  (Nat.shiftLeft
                    4398046511104
                    256))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 256
                      (Nat.shiftLeft
                        92233720368547758080
                        128)
                      1099511627776)
                    1024)
                  (Code.joinWords 1024
                    (Nat.shiftLeft
                      1116691496960
                      256)
                    (Code.joinWords 256
                      (Nat.shiftLeft
                        4835703278458516698824704
                        128)
                      17179869184))))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        20769187434139310514121985316880384
                        512)
                      1024)
                    2048)
                  4096)
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        316912650057057350374175801344
                        128)
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          20769187434139310514121985316880384
                          20769187434139310514121985316880384)
                        256)
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            436152936116925520796561691654488064
                            436152936116925520796561691654488064)
                          (Code.joinWords 128
                            20769187434139310514121985316880384
                            20769187434139310514121985316880384))
                        20769187434139310514121985316880384))
                    2048)))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          128)
                        256)
                      512)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        166154767123714712342377379238248448
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170143779608898499145501568964048715776
                            128)
                          256))
                      5070602400912917605986812821504))
                  (Code.joinWords 2048
                    17592186044416
                    1099511627776))
                (Code.joinWords 2048
                  (Code.joinWords 1024
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        2417870085973332058963968
                        128)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          2478297967103477955566764032
                          128)
                        (Nat.shiftLeft
                          170307336959942346215800279598419148800
                          128)))
                    (Nat.shiftLeft
                      73786976294838206464
                      128))
                  (Code.joinWords 1024
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        166154767123714712342377379238248448
                        128)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170143779608898499145501568964048715776
                          128)
                        256))
                    (Nat.shiftLeft
                      5070602400912917605986812821504
                      128))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        255211775190703847597530955573826158592
                        255211775190703847597530955573826158592)
                      256)
                    512)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      4294967296
                      512)
                    2048))
                (Code.joinWords 2048
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        255211775190703847597530955573826158592
                        255211775190703847611366013629108322304)
                      256)
                    512)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        211930866253824
                        128)
                      256)
                    512))))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  17592186044416
                  256)
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      92233720368547758080
                      128)
                    1024)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      4835703278458516698824704
                      128)
                    1024)))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          20769187434139310514121985316880384
                          20769187434139310514121985316880384)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          20769187434139310514121985316880384
                          20769187434139310514121985316880384)
                        256))
                    2048)
                  4096)
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          4503599627370496
                          128)
                        256)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          316912650057057350374175801344
                          128)
                        (Nat.shiftLeft
                          4503599627370496
                          128)))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          20769187434139310514121985316880384
                          20769187434139310519751484851093504)
                        256)
                      (Code.joinWords 256
                        (Code.joinWords 128
                          436152936116925520796561691654488064
                          436152936116925520796561691654488064)
                        (Code.joinWords 128
                          20769187434139310514121985316880384
                          20769187434139310519751484851093504)))
                    2048)))))))
      (Code.joinWords 131072
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          128)
                        256)
                      512)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        38685921375573312943423488
                        590295810358705651712)
                      1180591620717411303424))
                  (Code.joinWords 1024
                    (Code.joinWords 512
                      2658476273979435397478038067811975168
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170143779608898499145501568964048715776
                          128)
                        256))
                    81129638414606681695789005144064))
                (Code.joinWords 2048
                  (Code.joinWords 1024
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          295147905179352825856
                          170141183460469231731687303715884105728)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          590295810358705651712
                          170141183460469231731687303715884105728)
                        256))
                    (Nat.shiftLeft
                      1180591620717411303424
                      256))
                  (Nat.shiftLeft
                    1180591620717411303424
                    256)))
              (Code.joinWords 8192
                (Code.joinWords 2048
                  (Nat.shiftLeft
                    (Code.joinWords 256
                      (Nat.shiftLeft
                        58028439341502200385896448
                        128)
                      (Nat.shiftLeft
                        255211775190703847597530955573826158592
                        128))
                    512)
                  (Code.joinWords 512
                    (Nat.shiftLeft
                      21760683199807398854262784
                      128)
                    (Nat.shiftLeft
                      332041393326771929088
                      128)))
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        20769187434139310514121985316880384
                        128)
                      1024)
                    2048)
                  4096)))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            562954248388608
                            36591755562319872)
                          (Nat.shiftLeft
                            172799639452039063477494917836444794880
                            128))
                        512)
                      (Nat.shiftLeft
                        17179869184
                        512))
                    (Nat.shiftLeft
                      295147905179352825856
                      1024))
                  (Code.joinWords 1024
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        2658476273979435397478038067811975168
                        (Nat.shiftLeft
                          170143779608898499145501568964048715776
                          128))
                      512)
                    (Nat.shiftLeft
                      81129638414606681695789005144064
                      512)))
                (Code.joinWords 2048
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        295147905179352825856
                        256)
                      21474836480)
                    1024)
                  (Code.joinWords 1024
                    (Nat.shiftLeft
                      368934881474191032320
                      256)
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        73786976294838206464
                        256)
                      1125899906842624))))
              (Code.joinWords 8192
                (Code.joinWords 2048
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        255211775190703847597530955573826158592
                        128)
                      256)
                    512)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      18446744073709551616
                      128)
                    1024))
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        316912650057057350374175801344
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          20769187434139310514121985316880384
                          256)
                        (Nat.shiftLeft
                          20769187434139310514121985316880384
                          256))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            6666909166358718675033157286718603264
                            20769187434139310514121985316880384)
                          20769187434139310514121985316880384)
                        (Code.joinWords 256
                          6666909166358718675033157286718603264
                          20769187434139310514121985316880384))))
                  4096))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          128)
                        256)
                      512)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        38685921375573312943423488
                        590295810358705651712)
                      1180591620717411303424))
                  (Code.joinWords 2048
                    324518553658426726783156020576256
                    (Code.joinWords 1024
                      (Code.joinWords 256
                        20282409603651670423947251286016
                        1114112)
                      (Nat.shiftLeft
                        1114112
                        256))))
                (Code.joinWords 2048
                  (Code.joinWords 1024
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          295147905179352825856
                          170141183460469231731687303715884105728)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          590295810358705651712
                          170141183460469231731687303715884105728)
                        256))
                    (Nat.shiftLeft
                      1180591620717411303424
                      256))
                  (Nat.shiftLeft
                    1180591620717411303424
                    256)))
              (Code.joinWords 8192
                (Code.joinWords 2048
                  (Code.joinWords 512
                    49152
                    (Code.joinWords 256
                      (Code.joinWords 128
                        58028439341502200385896448
                        196608)
                      (Nat.shiftLeft
                        49164
                        128)))
                  (Code.joinWords 512
                    (Code.joinWords 256
                      (Code.joinWords 128
                        49152
                        21760683199807398854262784)
                      (Code.joinWords 128
                        68719476736
                        211106232532992))
                    (Nat.shiftLeft
                      332041393326771929088
                      128)))
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        4503599627370496
                        256)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          20769187434139310514121985316880384
                          128)
                        4503599627370496))
                    2048)
                  4096)))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 2048
                  (Nat.shiftLeft
                    68719476736
                    512)
                  (Code.joinWords 1024
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        73786976294838206464
                        256)
                      73014444032)
                    (Code.joinWords 256
                      295147905179352825856
                      73786976294838206464)))
                (Code.joinWords 2048
                  (Code.joinWords 1024
                    (Nat.shiftLeft
                      4
                      256)
                    (Nat.shiftLeft
                      295147905179352825860
                      256))
                  (Code.joinWords 512
                    (Nat.shiftLeft
                      295147905179352825856
                      256)
                    (Nat.shiftLeft
                      68719476736
                      128))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        18446744073709551616
                        128)
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        20282409603651670423947251286016
                        20282409603651670423947251286016)
                      256)
                    512))
                (Code.joinWords 4096
                  (Code.joinWords 1024
                    (Nat.shiftLeft
                      65536
                      256)
                    (Nat.shiftLeft
                      65536
                      256))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          20282409603651670423947251286016
                          20282409603651670423947251286016)
                        256)
                      512)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        65536
                        256)
                      (Code.joinWords 256
                        (Code.joinWords 128
                          20769187434139310514121985316880384
                          20769187434139310514121985316880384)
                        65536))))))))
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          128)
                        256)
                      512)
                    324518553658426726783156020576256)
                  (Code.joinWords 2048
                    324518553658426726783156020576256
                    21550060203879899825443954491392))
                (Code.joinWords 2048
                  (Code.joinWords 512
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        170141183460469232026835208895236931584
                        128)
                      256)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        170141183460469232321983114074589757440
                        128)
                      256))
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      2596148429267413814265248164610048
                      128)
                    256)))
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          83078017387157470285889437970726912
                          128)
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            18446744073709551616
                            128)
                          (Nat.shiftLeft
                            88167159178098725746873140076609536
                            128))
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1267650600228229401496703205376
                            128)
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          83078017387157470285889437970726912
                          128)
                        256)))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          83078017387157470285889437970726912
                          128)
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          83078017387157470285889437970726912
                          128)
                        256)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          103845937170696552570609926584401920
                          128)
                        (Nat.shiftLeft
                          83078017387157470285889437970726912
                          128)))))
                8192))
            (Code.joinWords 16384
              (Code.joinWords 4096
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 128
                      170141183460469231731687304815395733504
                      170141183460469231731687305914907361280)
                    256)
                  512)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    2596148429267413814265248164610048
                    256)
                  512))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1329248278194519524574231007531630592
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1329248278194519524574231007531630592
                          256)
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          4294967296
                          (Code.joinWords 128
                            1334413479021474473799304511829835776
                            20282409603651670423947251286016))
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1329248278194519524574231007531630592
                          256)
                        512))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1329248278194519524574231007531630592
                          256)
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          1349997183219055183417929045597224960
                          1329248278194519524574231007531630592)
                        512))))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1267650600228229401496703205376
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1267650600228229401496703205376
                            128)
                          256))
                      (Nat.shiftLeft
                        18446744073709551616
                        128))
                    2048)
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            20282409603651670423947251286016
                            20282409603651670423947251286016)
                          256)
                        512)
                      (Nat.shiftLeft
                        4294967296
                        512))
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 128
                          20769187434139310514121985316880384
                          20769187434139310514121985316880384)
                        20769187434139310514121985316880384)
                      1024))))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          128)
                        256)
                      512)
                    324518553658426726783156020576256)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 256
                        1267650600228229401496703205376
                        (Nat.shiftLeft
                          1048576
                          128))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1048576
                          128)
                        256))
                    2048))
                (Code.joinWords 2048
                  (Code.joinWords 512
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        170141183460469232026835208895236931584
                        128)
                      256)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        170141183460469232321983114074589757440
                        128)
                      256))
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      2596148429267413814265248164610048
                      128)
                    256)))
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          17293822569102704640
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          83078017387157470285889437970726912
                          128)
                        256))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            49152
                            18446744073709551616)
                          (Nat.shiftLeft
                            88167159178098743108514617172688896
                            128))
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1267650600228229666410286022656
                            128)
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          83078017387157470308407779704963072
                          128)
                        256)))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            68719476736
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          83078017387157470285889437970726912
                          128)
                        256))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            83078017387157470309533696791674880
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            68719476736
                            128)
                          256))
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          103845937170696552570609926584401920
                          128)
                        (Nat.shiftLeft
                          83078017387157470309533696791674880
                          128)))))
                8192))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  17592186044416
                  256)
                512)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        68719476736
                        256)
                      512)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          20282409603651670423947251286016
                          20282409603651670423947251286016)
                        256)
                      512)
                    (Nat.shiftLeft
                      4294967296
                      512)))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1267650600228233923856747724800
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1267650600228229420257120354304
                            128)
                          256))
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          18446744073709551616
                          128)
                        (Nat.shiftLeft
                          4503668346847232
                          128)))
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          20282409603651670423947251286016
                          20282409603651670425115482390528)
                        256)
                      512)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            4503668346847232
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            68719476736
                            128)
                          256))
                      (Code.joinWords 256
                        (Code.joinWords 128
                          20769187434139310514121985316880384
                          20769187434139310514121985316880384)
                        (Nat.shiftLeft
                          4503668346847232
                          128)))))))))))
    (Code.joinWords 262144
      (Code.joinWords 131072
        (Code.joinWords 32768
          (Code.joinWords 16384
            (Code.joinWords 8192
              (Code.joinWords 4096
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      170141183460469231731687303715884105728
                      128)
                    256)
                  512)
                (Code.joinWords 2048
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        170141183460469231731687303715884105728
                        128)
                      256)
                    512)
                  (Code.joinWords 1024
                    (Nat.shiftLeft
                      16777216
                      256)
                    (Nat.shiftLeft
                      16777216
                      256))))
              (Nat.shiftLeft
                (Code.joinWords 1024
                  (Nat.shiftLeft
                    4398046511104
                    256)
                  (Nat.shiftLeft
                    4398046511104
                    256))
                4096))
            (Code.joinWords 8192
              (Code.joinWords 4096
                (Code.joinWords 512
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      255211775190703847597530955573826158592
                      128)
                    256)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      255211775190703847597530955573826158592
                      128)
                    256))
                (Code.joinWords 512
                  (Code.joinWords 128
                    49152
                    216172782113783808)
                  (Code.joinWords 128
                    59479150325039755395543859200
                    196608)))
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 1024
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        20769187434139310514121985316880384
                        256)
                      (Nat.shiftLeft
                        20769187434139310514121985316880384
                        256))
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        20769187434139310514121985316880384
                        256)
                      (Nat.shiftLeft
                        20769187434139310514121985316880384
                        256)))
                  2048)
                4096)))
          (Code.joinWords 16384
            (Code.joinWords 8192
              (Code.joinWords 4096
                (Code.joinWords 2048
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        170141183460469231731687303715884105728
                        128)
                      256)
                    512)
                  (Code.joinWords 1024
                    (Nat.shiftLeft
                      18889465931478580854784
                      256)
                    (Nat.shiftLeft
                      18889465931478580854784
                      256)))
                (Code.joinWords 2048
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        170141183460469231731687303715884105728
                        128)
                      256)
                    512)
                  (Code.joinWords 1024
                    (Nat.shiftLeft
                      1237940039285380274899124224
                      256)
                    (Nat.shiftLeft
                      1237940039285380274899124224
                      256))))
              (Code.joinWords 1024
                (Nat.shiftLeft
                  1024
                  256)
                (Nat.shiftLeft
                  1024
                  256)))
            (Code.joinWords 8192
              (Code.joinWords 512
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    255211775190703847597530955573826158592
                    128)
                  256)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    255211775190703847597530955573826158592
                    128)
                  256))
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 1024
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        20769187434139310514121985316880384
                        256)
                      (Nat.shiftLeft
                        20769187434139310514121985316880384
                        256))
                    (Code.joinWords 512
                      (Code.joinWords 256
                        5337681170573802802129350226438258688
                        20769187434139310514121985316880384)
                      (Code.joinWords 256
                        5337681170573802802129350226438258688
                        20769187434139310514121985316880384)))
                  2048)
                4096))))
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          128)
                        256)
                      512)
                    324518553658426726783156020576256)
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 128
                        144116287587483648
                        2199023255552)
                      4398046511104)
                    (Code.joinWords 1024
                      (Code.joinWords 256
                        1267650600228229401496703205376
                        16842752)
                      (Nat.shiftLeft
                        16842752
                        256))))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    4722366482869645213696
                    128)
                  (Code.joinWords 1024
                    (Code.joinWords 256
                      (Nat.shiftLeft
                        4740813226943354765312
                        128)
                      17179869184)
                    (Code.joinWords 256
                      1099511627776
                      17179869184))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 512
                    (Code.joinWords 128
                      49152
                      216172782113783808)
                    (Code.joinWords 256
                      (Nat.shiftLeft
                        196608
                        128)
                      (Nat.shiftLeft
                        49164
                        128)))
                  (Code.joinWords 512
                    (Code.joinWords 256
                      49152
                      4722366482869645213696)
                    (Code.joinWords 256
                      (Code.joinWords 128
                        72620548286316544
                        1108101562368)
                      906694364710971881029632)))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1267650600228229401496703205376
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1267650600228229401496703205376
                          128)
                        256))
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      4294967296
                      512)
                    1024))))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 1024
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          1099511627776
                          2199023255552)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          170141183460469231731687303715884105728
                          170141183460469231731687303715884105728)
                        256))
                    (Nat.shiftLeft
                      4398046511104
                      256))
                  (Nat.shiftLeft
                    4398046511104
                    256))
                (Code.joinWords 4096
                  (Code.joinWords 1024
                    (Nat.shiftLeft
                      4
                      256)
                    (Nat.shiftLeft
                      1099511627780
                      256))
                  (Code.joinWords 512
                    (Nat.shiftLeft
                      1099511627776
                      256)
                    (Nat.shiftLeft
                      4722366482869645213696
                      128))))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        309485009821345068724781056
                        256)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          309485009821345068724781056
                          256)
                        20769187434139310514121985316880384))
                    2048)
                  4096)
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        65536
                        256)
                      (Nat.shiftLeft
                        65536
                        256))
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1267650600228229401496703205376
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1267650600228229401496703205376
                          128)
                        256)))
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        65536
                        256)
                      (Code.joinWords 512
                        (Code.joinWords 256
                          20769187434139310514121985316880384
                          65536)
                        20769187434139310514121985316880384))
                    2048)))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    324518553658426726783156020576256
                    2048)
                  (Code.joinWords 2048
                    17592186044416
                    1267650600228229402596214833152))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    4722366482869645213696
                    128)
                  (Nat.shiftLeft
                    4740813226943354765312
                    128)))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      4294967296
                      512)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 512
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        1267650600228229401496703205376
                        128)
                      256)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        1267650600228229401496703205376
                        128)
                      256))
                  2048)))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  17592186044416
                  256)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      4722366482869645213696
                      128)
                    512)
                  4096))
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 512
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        1267650600228229401496703205376
                        128)
                      256)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        1267650600228229401496703205376
                        128)
                      256))
                  2048)
                8192)))))
      (Code.joinWords 131072
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          128)
                        256)
                      512)
                    75557863725914323419136)
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        2658476273979435397478038067811975168
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170143779608898499145501568964048715776
                            128)
                          256))
                      81129638414606681695789005144064)
                    295147905179352825856))
                (Nat.shiftLeft
                  75557863725914323419136
                  256))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 512
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        255211775190703847597530955573826158592
                        128)
                      256)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        255211775190703847597530955573826158592
                        128)
                      256))
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      18446744073709551616
                      128)
                    2048))
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          20769187434139310514121985316880384
                          256)
                        (Nat.shiftLeft
                          20769187434139310514121985316880384
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          20769187434139310514121985316880384
                          256)
                        (Nat.shiftLeft
                          20769187434139310514121985316880384
                          256)))
                    2048)
                  4096)))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 1024
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Code.joinWords 128
                          562954248388608
                          36591755562319872)
                        (Nat.shiftLeft
                          172799639452039063477494917836444794880
                          128))
                      512)
                    (Nat.shiftLeft
                      17179869184
                      512))
                  (Code.joinWords 1024
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        2658476273979435397478038067811975168
                        (Nat.shiftLeft
                          170143779608898499145501568964048715776
                          128))
                      512)
                    (Nat.shiftLeft
                      81129638414606681695789005144064
                      512)))
                (Code.joinWords 2048
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      21474836480
                      512)
                    1024)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      1125899906842624
                      512)
                    1024)))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 512
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        255211775190703847597530955573826158592
                        128)
                      256)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        255211775250124969483229208768984121344
                        128)
                      256))
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        963362762505407623593984
                        128)
                      256)
                    512))
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          309485009821345068724781056
                          256)
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          316912650057057350374175801344
                          309485009821345068724781056)
                        512))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          20769187434139310514121985316880384
                          256)
                        (Nat.shiftLeft
                          20769187748460023613925570740486144
                          256))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          6666909166358718675033157286718603264
                          20769187434139310514121985316880384)
                        (Code.joinWords 256
                          6666909166358718675033157286718603264
                          20769187748460023613925570740486144))))
                  4096))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    75557863725914323419136
                    2048)
                  (Code.joinWords 2048
                    324518553658426726783156020576256
                    20282409603946818329126604111872))
                (Nat.shiftLeft
                  75557863725914323419136
                  256))
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    18446744073709551616
                    128)
                  2048)
                4096))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 2048
                  (Nat.shiftLeft
                    68719476736
                    512)
                  (Nat.shiftLeft
                    73014444032
                    512))
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      68719476736
                      128)
                    512)
                  2048))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        20282409603651670423947251286016
                        20282409603651670423947251286016)
                      256)
                    512)
                  4096)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        20282409603651670423947251286016
                        20282409603651670423947251286016)
                      256)
                    512)
                  4096)))))
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        170141183460469231731687303715884105728
                        128)
                      256)
                    512)
                  (Code.joinWords 2048
                    324518553658426726783156020576256
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        20282409603651670423947251286016
                        (Nat.shiftLeft
                          16777216
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          16777216
                          256)
                        512))))
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    75557863725914323419136
                    128)
                  256))
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1267650600228229401496703205376
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1267650600228229401496703205376
                          128)
                        256))
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        4722366482869645213696
                        128)
                      256)
                    (Nat.shiftLeft
                      18446744073709551616
                      128)))
                8192))
            (Code.joinWords 16384
              (Code.joinWords 4096
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 128
                      170141183460469231731687304815395733504
                      170141183460469231731687305914907361280)
                    256)
                  512)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    2596148429267413814265248164610048
                    256)
                  512))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          74276402357122816493947453440
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1329248278194519524574231007531630592
                          256)
                        512))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            4722366482869645213696
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1329248278194519524574231007531630592
                          256)
                        512)))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        49152
                        (Code.joinWords 256
                          4294967296
                          (Code.joinWords 128
                            1334413557941356181695428796178497536
                            20282410807855123555706780778496)))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1329248279741968185513370699381604352
                          256)
                        512))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1329248279746803962578805510918635520
                            4722366482869645213696)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          1349997183219055183417929045597224960
                          1329248279746803962578805510918635520)
                        512))))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1267650600228229401496703205376
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1267650605245743789545701244928
                          128)
                        256))
                    2048)
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            20282719169236869882979297525760
                            20282409684227048537910572744704)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          4294967296
                          309489732187827938369994752)
                        512))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            309489732187827938369994752
                            4722366482869645213696)
                          256)
                        512)
                      (Code.joinWords 512
                        20769187434139310514121985316880384
                        (Code.joinWords 256
                          20769187434139310514121985316880384
                          309489732187827938369994752))))))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    75557863725914323419136
                    128)
                  256)
                8192)
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1267650600228229419157608726528
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1267650600228229419157608726528
                          128)
                        256))
                    2048)
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          4722366482869645213696
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          68719476736
                          128)
                        256))
                    (Code.joinWords 512
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          18446744073709551616
                          128)
                        (Nat.shiftLeft
                          68719476736
                          128))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          68719476736
                          128)
                        256))))
                8192))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  17592186044416
                  256)
                512)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          68719476736
                          4722366482869645213696)
                        256)
                      512)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          20282409683931900632731219918848
                          20282409683931900632731219918848)
                        256)
                      512)
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        4294967296
                        (Code.joinWords 128
                          4722366482869645213696
                          4722366482869645213696))
                      512)))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1267650600228229420257120354304
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1267650605245743808306118393856
                          128)
                        256))
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          20282409684227048537910572744704
                          20282409684227048539078803849216)
                        256)
                      512)
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          68719476736
                          128)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          4722366482869645213696
                          4722366482938364690432)
                        256)))))))))))

/-- The block word is computed from the verified profile data. -/
theorem word_eq :
    Code.profileWord 64 24 (fun i q => Data.profiles (0 + i) q) = word := by
  decide +kernel

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage000
