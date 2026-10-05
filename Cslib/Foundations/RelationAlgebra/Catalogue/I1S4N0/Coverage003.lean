/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Cslib.Foundations.RelationAlgebra.FastCatalogueCoverage

/-!
# Profile coverage for models 193–256 of the ⟨1, 4, 0⟩ row

The balanced word contains exactly the cycle profiles of this block and its atom renamings.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage003

/-- The cycle profiles covered by this block of models. -/
def word : ℕ :=
  (Code.joinWords 524288
    (Code.joinWords 262144
      (Code.joinWords 131072
        (Code.joinWords 65536
          (Nat.shiftLeft
            (Nat.shiftLeft
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            311874185193582540725673986137316655104
                            128)
                          256)
                        512)
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            311874185134161418853810790997440856064
                            128)
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            311870118580515271401665061267009699840
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            311874185203641710255949984769006108672
                            128)
                          256)
                        512))))
                8192)
              16384)
            32768)
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170141183460469231731687303715884105728
                            128)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170141183460469231731687303715884105728
                            128)
                          256)
                        512)
                      1024))
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
                          (Nat.shiftLeft
                            2097152
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            536870912
                            170141183460469231731687303716420976640)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            2097152
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            536870912
                            170141183460469231731687303716420976640)
                          256)))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170141183460469231731687303715884105728
                            128)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170141183460469231731687303715884105728
                            128)
                          256)
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            549755813888
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            170141183460469231731687303715884105728
                            170141183460469231731687303715884105728)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            549755813888
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            170141183460469231731687303715884105728
                            170141183460469231731687303715884105728)
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            36028797018963968
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            170141183460469231731687303715884105728
                            170141183460469231731687303715884105728)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            36028797018963968
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            170141183460469231731687303715884105728
                            170141183460469231731687303715884105728)
                          256))))))
              (Code.joinWords 8192
                (Code.joinWords 2048
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          255880293552445008480539468949838888960
                          255880293552445008480539468949838888960)
                        256)
                      512)
                    1024)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        1000830431289790764152071127895638016
                        256)
                      512)
                    1024))
                (Code.joinWords 2048
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          3909434451103859474215832685379584
                          15211807202738752817960438464512)
                        256)
                      512)
                    1024)
                  (Nat.shiftLeft
                    (Code.joinWords 128
                      49152
                      14051230837395947520)
                    1024))))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    170141183460469231731687303715884105728
                    128)
                  256)
                512)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          830767497365572420564879412675215360
                          10384593717069655257060992658440192)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          882690465950920696850184375967416320
                          10384593717069655257060992658440192)
                        256))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          218076468058462760398280845827244032
                          10384593717069655257060992658440192)
                        256)
                      (Code.joinWords 256
                        (Code.joinWords 128
                          49152
                          271162511140122838072376640297190293504)
                        (Code.joinWords 128
                          218076468058462760398280845827244032
                          10384593717069655257060992658440192)))
                    2048))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10384593717069655257060992658440192
                          128)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          51922968585348276285304963292200960
                          10384593717069655257060992658440192)
                        256))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        51922968585348276285304963292200960
                        256)
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            271868663512883574629856787797964275712
                            271868663512883574629856787797964226560)
                          51922968585348276285304963292200960)
                        20769187434139310514121985316880384))
                    2048))))))
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 8192
              (Code.joinWords 2048
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        170141183460469231731687303715884105728
                        128)
                      256)
                    512)
                  1024)
                (Nat.shiftLeft
                  (Code.joinWords 512
                    664613997892457936451903530140172288
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        170143779608898499145501568964048715776
                        128)
                      256))
                  1024))
              (Code.joinWords 2048
                (Nat.shiftLeft
                  (Code.joinWords 512
                    (Nat.shiftLeft
                      9671406556917033397649408
                      128)
                    (Code.joinWords 256
                      (Nat.shiftLeft
                        2475917857502623506959958016
                        128)
                      (Nat.shiftLeft
                        170141183460469231731687303715884105728
                        128)))
                  1024)
                (Nat.shiftLeft
                  (Code.joinWords 512
                    (Nat.shiftLeft
                      664613997892457936451903530140172288
                      128)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        170143779608898499145501568964048715776
                        128)
                      256))
                  1024)))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      12089258196146291747061760
                      128)
                    1024)
                  4096)
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        10547486819198982735153319020331008
                        256)
                      512)
                    1024)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        10384593717069655257060992658440192
                        256)
                      512)
                    1024))
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        872305872233851041593123383308976128
                        872305872233851041593123383308976128)
                      1024)
                    2048)
                  4096))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 2048
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          128)
                        256)
                      512)
                    1024)
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      664613997892457936451903530140172288
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170143779608898499145501568964048715776
                          128)
                        256))
                    1024))
                (Code.joinWords 2048
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        9671406556917033397649408
                        128)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          2475917857502623506959958016
                          128)
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          128)))
                    1024)
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        664613997892457936451903530140172288
                        128)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170143779608898499145501568964048715776
                          128)
                        256))
                    1024)))
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        4294967296
                        512)
                      1024)
                    2048)
                  4096)
                8192))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 512
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      35184372088832
                      128)
                    256)
                  (Nat.shiftLeft
                    (Code.joinWords 128
                      170141183460469231731687303715884105728
                      170141183460469231731687303715884105728)
                    256))
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      12089258196146291747061760
                      128)
                    1024)
                  4096))
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
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 128
                          872305872233851041593123383308976128
                          872305872233851041593123383308976128)
                        20769187434139310514121985316880384)
                      1024)
                    2048)
                  4096))))))
      (Code.joinWords 131072
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 4096
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        170141183460469231731687303715884105728
                        128)
                      256)
                    512)
                  1024)
                (Nat.shiftLeft
                  (Code.joinWords 512
                    10633823966279326983230456482242756608
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        170143779608898499145501568964048715776
                        128)
                      256))
                  1024))
              (Nat.shiftLeft
                (Code.joinWords 2048
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        10395368747171595206973714635685888
                        128)
                      256)
                    1024)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        10384593717069655257060992658440192
                        128)
                      256)
                    1024))
                8192))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Code.joinWords 128
                          2251799813685248
                          36029346774777856)
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          128))
                      512)
                    1024)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        10633823966279326983230456482242756608
                        (Nat.shiftLeft
                          170143779608898499145501568964048715776
                          128))
                      512)
                    1024))
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      2814749767106560
                      512)
                    1024)
                  2048))
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        13333818332717437350066314573437206528
                        13333818332717437350066314573437206528)
                      1024)
                    2048)
                  4096)
                8192)))
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        651572408517309912369305447563264
                        158456325028528675187087900672)
                      256)
                    512)
                  4096)
                (Code.joinWords 2048
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        10398062504697080194451895129997312
                        128)
                      256)
                    1024)
                  (Code.joinWords 1024
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          298411685053713613466904685032937357312
                          311745503445852172702669252801532526592)
                        256)
                      512)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        10387287474595140244539173152751616
                        128)
                      256))))
              16384)
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 2048
                  (Nat.shiftLeft
                    (Code.joinWords 256
                      (Code.joinWords 128
                        36028797018963968
                        36028934457917440)
                      (Nat.shiftLeft
                        170141183460469231731687303715884105728
                        128))
                    512)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      1125899906842624
                      512)
                    1024))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          68719476736
                          128)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          146028888064
                          128)
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          1125904201809920
                          68719476736)
                        512)))
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          128)
                        256)
                      512)
                    2048)))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          20282409603651670423947251286016
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            20282409603651670423947251286016
                            332306998946228968225951765070086144)
                          256)
                        (Nat.shiftLeft
                          20282409603651670423947251286016
                          256))
                      1024))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            43258576732788328326074996883456
                            158456325028528675187087900672)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          20282409603651670423947251286016
                          256)
                        512))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            332306998946228968225951765070086144
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          256))
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          20282409603651670423947251286016
                          332312069548629881143557751882907648)
                        256))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            20282409603651670423947251286016
                            332306998946228968225951765070086144)
                          256)
                        (Nat.shiftLeft
                          20282409603651670423947251286016
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          332306998946228968225951765070086144
                          128)
                        256)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          332312069548629881143557751882907648
                          128)
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            332306999023600220681288032251281408
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          (Code.joinWords 128
                            324518553658426726783156020576256
                            324518553658426726783156020576256)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            332312069626001133598894019064102912
                            128)
                          256)
                        20769187434139310514121985316880384))))))))
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Nat.shiftLeft
                (Code.joinWords 2048
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        10387921299895254359239921504354304
                        128)
                      256)
                    1024)
                  (Code.joinWords 1024
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          308380895081521604399381491180197904384
                          128)
                        (Nat.shiftLeft
                          311745503448482795286150685885693165568
                          128))
                      512)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        2693757525484987478180494311424
                        128)
                      256)))
                8192)
              16384)
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5316911983139663491615228241121378304
                          256)
                        512)
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          332306998946228968225951765070086144
                          128)
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            332306999023600220681288032251281408
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          (Code.joinWords 128
                            5316911983139663491903458617273090048
                            324518553658426726783156020576256)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            332312069626001133598894019064102912
                            128)
                          256)
                        (Nat.shiftLeft
                          5316993112778078098585154406278234112
                          256)))))
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        10425950817902101241284822600515584
                        256)
                      512)
                    1024)
                  (Code.joinWords 1024
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          298411685053713613480739743088219521024
                          128)
                        (Nat.shiftLeft
                          309253200894334333569723908972953468928
                          128))
                      512)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        40723275532331869523081590472704
                        256)
                      512)))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            332306998946228968225951765070086144
                            128)
                          256)
                        (Nat.shiftLeft
                          5316911983139663491615228241121378304
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            332306999023600220681288032251281408
                            128)
                          256)
                        (Nat.shiftLeft
                          5316993112778078098585154406278234112
                          256))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            332312069626001133598894019064102912
                            128)
                          256)
                        (Nat.shiftLeft
                          5316911983139663491903458617273090048
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            332306999023600220681288032251281408
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          (Code.joinWords 128
                            5316911983139663491903458617273090048
                            324518553658426726783156020576256)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            332312069626001133598894019064102912
                            128)
                          256)
                        (Nat.shiftLeft
                          5316993112778078098585154406278234112
                          256))))))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 1024
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        2228224
                        128)
                      256)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        2228224
                        128)
                      256))
                  2048)
                4096)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          255211775190703847597530955573826158592
                          128)
                        (Code.joinWords 128
                          298411685053713613466904685032937357312
                          311745503386431050816970999606374563840))
                      512)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        158456325028528675187087900672
                        128)
                      256)
                    512))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        49152
                        (Nat.shiftLeft
                          10387921299895271653062490607058944
                          128))
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            255211775190703847597530955573826158592
                            308380895081521604399381491180197904384)
                          (Code.joinWords 128
                            298411685113134735352602938228095320064
                            311745503448482795286150685885693165568))
                        512)
                      (Code.joinWords 512
                        (Code.joinWords 256
                          49152
                          (Nat.shiftLeft
                            2693757525502326601315856154624
                            128))
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            68719476736
                            128)
                          256))))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            68719476736
                            128)
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          47288517641895936
                          128)
                        256)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            47288517641895936
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            68719476736
                            128)
                          256)))))))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        170141183460469231731687303715884105728
                        170141183460469231731687338900256194560)
                      256)
                    512)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          332306998946228968225951765070086144
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          332306998946228968225951765070086144
                          128)
                        256))
                    2048))
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          332306998946228968225951765070086144
                          128)
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            332306998946228968225951765070086144
                            332306999023600220681288032251281408)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          (Code.joinWords 128
                            324518553658426726783156020576256
                            324518553658426726783156020576256)))
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          332306998946228968225951765070086144
                          332312069626001133598894019064102912)
                        256)))
                  4096))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          20282409603651670423947251286016
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          332306998946228968225951765070086144
                          332306998946228968225951765070086144)
                        256)
                      1024))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          40723275532331869523081590472704
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          20282409603651670423947251286016
                          256)
                        512))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            332306998946228968225951765070086144
                            332306999023600220681288032251281408)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            332312069548629881143557751882907648
                            332312069626001133598894019064102912)
                          256)
                        20769187434139310514121985316880384))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          332327281355832619896375712321372160
                          332306998946228968225951765070086144)
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            37520834297856
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            37520834297856
                            128)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            332306998946228968225951765070086144
                            332306999023600220681288032251281408)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            68719476736
                            128)
                          256))))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            332312069548629881143557751882907648
                            332312069626001133598894019064102912)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            68719476736
                            128)
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            332306998946228968225951765070086144
                            332306999023600220681288032251281408)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          (Code.joinWords 128
                            324518553658426726783156020576256
                            324518553658426726783156020576256)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            332312069548629881143557751882907648
                            332312069626001133598894019064102912)
                          256)
                        (Code.joinWords 256
                          20769187434139310514121989611847680
                          (Nat.shiftLeft
                            68719476736
                            128))))))))))))
    (Code.joinWords 262144
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
                          (Nat.shiftLeft
                            170141183460469231731687303715884105728
                            128)
                          256)
                        512)
                      1024)
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
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170141183460469231731687303715884105728
                            128)
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            536870912
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            33554432
                            170141183460469231731687303716420976640)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            536870912
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            33554432
                            170141183460469231731687303716420976640)
                          256)))))
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      170141183460469231731687303715884105728
                      128)
                    256)
                  512))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          265849655638903904914846201506326118400
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          265849655638903904914846201506326118400
                          128)
                        256))
                    1024)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        15954873560978135415612169962626482176
                        128)
                      256)
                    1024))
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          13292279957849158729038070602803445760
                          256)
                        (Nat.shiftLeft
                          10384593717069655257060992658440192
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          13344202926434507005323375566095646720
                          256)
                        (Nat.shiftLeft
                          10384593717069655257060992658440192
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          2710378960155180022092919083852890112
                          256)
                        (Nat.shiftLeft
                          10384593717069655257060992658440192
                          256))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          49152
                          2710378960155180022092919083852890112)
                        (Code.joinWords 256
                          256208696187542534502208810869036417024
                          10384593717069655257060992658440192))))
                  4096)))
            (Code.joinWords 16384
              (Code.joinWords 4096
                (Code.joinWords 2048
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          128)
                        256)
                      512)
                    1024)
                  (Code.joinWords 1024
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          128)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          37778931862957161709568
                          170141183460469231731687303715884105728)
                        256))
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          128)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          37778931862957161709568
                          170141183460469231731687303715884105728)
                        256))))
                (Code.joinWords 2048
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          128)
                        256)
                      512)
                    1024)
                  (Code.joinWords 1024
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          128)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          2475880078570760549798248448
                          170141183460469231731687303715884105728)
                        256))
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          128)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          2475880078570760549798248448
                          170141183460469231731687303715884105728)
                        256)))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          4137611559144940766485239262347264
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          243388915243820045087367015432192
                          128)
                        256))
                    1024)
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      49152
                      59479150325039755395543859200)
                    1024))
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10384593717069655257060992658440192
                          256)
                        512)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          51922968585348276285304963292200960
                          256)
                        (Nat.shiftLeft
                          10384593717069655257060992658440192
                          256)))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        51922968585348276285304963292200960
                        256)
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            266884058528690140106467511321912983552
                            20769187434139310514121985316880384)
                          51922968585348276285304963292200960)
                        266884058528690140106467511321912934400)))
                  4096))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
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
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 512
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        297747071055821155530452781502797185024
                        297747071055821155530452781502797185024)
                      256)
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        297747071055821155530452781502797185024
                        297747071055821155530452781502797185024)
                      256))
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        20769187434139310514121985316880384
                        256)
                      (Nat.shiftLeft
                        20769504346789367571472359492681728
                        256))
                    2048))
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        20769187434139310514121985316880384
                        256)
                      (Nat.shiftLeft
                        20769504346789367571472359492681728
                        256))
                    2048)
                  4096)))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    170141183460469231731687303715884105728
                    128)
                  256)
                512)
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        20769187434139310514121985316880384
                        256)
                      (Nat.shiftLeft
                        20769504346789367571472359492681728
                        256))
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        20769187434139310514121985316880384
                        256)
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            20769187434139310514121985316880384
                            20769187434139310514121985316880384)
                          20769504346789367571472359492681728)
                        20769187434139310514121985316880384))
                    2048)
                  4096)))))
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Code.joinWords 512
                    (Nat.shiftLeft
                      2475880078570760549798248448
                      128)
                    (Code.joinWords 256
                      (Nat.shiftLeft
                        2475889523303726289088675840
                        128)
                      (Nat.shiftLeft
                        170141183460469231731687303715884105728
                        128)))
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      4835703278458516698824704
                      128)
                    1024))
                8192)
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Code.joinWords 512
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        689601926524156794414206543724544
                        128)
                      256)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        158456325028528675187087900672
                        128)
                      256))
                  2048)
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1267650600228229401496703205376
                          128)
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            43258576732788328326074996883456
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            158456325028528675187087900672
                            128)
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1267650600228229401496703205376
                          128)
                        256)))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1267650600228229401496703205376
                            1267650600228229401496703205376)
                          256)
                        (Nat.shiftLeft
                          5316911983139663491615228241121378304
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            5316911983139663491615228241121378304
                            324518553658426726783156020576256)
                          256)
                        512)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          1267650600228229401496703205376
                          256)
                        (Nat.shiftLeft
                          5316993112778078098296924030126522368
                          256)))))))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        4722366482869645213696
                        128)
                      512)
                    1024)
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          9481626453886709530624
                          128)
                        512)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          4835721725202590408376320
                          128)
                        (Nat.shiftLeft
                          4722366482869645213696
                          128)))
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          128)
                        256)
                      512)))
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        10588210094731314604676400610803712
                        256)
                      512)
                    1024)
                  (Code.joinWords 1024
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          308380895022100482513683237985039941632
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          309253200894334333569111419423631081472
                          128)
                        256))
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        10425316992601987126584074248912896
                        256)
                      512)))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1267650600228229401496703205376
                            1267650600228229401496703205376)
                          256)
                        (Nat.shiftLeft
                          5316911983139663491615228241121378304
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5316993112778078098296924030126522368
                          256)
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5316911983139663491615228241121378304
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          (Code.joinWords 128
                            5316911983139663491903458617273090048
                            324518553658426726783156020576256)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          20769187434139310514121985316880384
                          128)
                        (Nat.shiftLeft
                          5316993112778078098585154406278234112
                          256))))))))
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
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1048576
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1048576
                          128)
                        256))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 512
                    (Nat.shiftLeft
                      2475880078570760549798248448
                      128)
                    (Code.joinWords 256
                      (Nat.shiftLeft
                        2475889523303726289088675840
                        128)
                      (Nat.shiftLeft
                        170141183460469231731687303715884105728
                        128)))
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      4835703278458516698824704
                      128)
                    1024)))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        319014718988379809496913694467282698240
                        63802943797675961899382738893456539648)
                      256)
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          692295684049641781892387038035968
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          158456325028528675187087900672
                          128)
                        256)))
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          20769504346789367571472359492681728
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          256))
                      (Nat.shiftLeft
                        20769504346789367571472359492681728
                        256))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          1267650600228229401496703205376
                          1267650600228229401496703205376)
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          49152
                          (Nat.shiftLeft
                            43258576732788328326074996883456
                            128))
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            158456325028528887117954154496
                            128)
                          256))
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          1267650600228229401496703205376
                          1267650600228229401496703205376)
                        256)))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          1267650600228229401496703205376
                          1267650600228229401496703205376)
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          316912650057057350374175801344
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            324518553658426726783156020576256
                            324518553658426726783156020576256)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          1584563250285286751870879006720
                          256)
                        4294967296))))))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 512
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      35184372088832
                      128)
                    256)
                  (Nat.shiftLeft
                    (Code.joinWords 128
                      170141183460469231731687303715884105728
                      170141183460469231731687303715884105728)
                    256))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        4722366482869645213696
                        128)
                      512)
                    1024)
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          9481626453886709530624
                          128)
                        512)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          4835721725202590408376320
                          128)
                        (Nat.shiftLeft
                          4722366482869645213696
                          128)))
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          128)
                        256)
                      512))))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          256))
                      (Nat.shiftLeft
                        20769187434139310514121985316880384
                        512))
                    2048)
                  4096)
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          1267650600228229401496703205376
                          1267650600228229401496703205376)
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          4503599627370496
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          4503599627370496
                          128)
                        256)))
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            324518553658426726783156020576256
                            324518553658426731286755647946752)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          (Code.joinWords 128
                            324518553658426726783156020576256
                            324518553658426726783156020576256)))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            20769187434139310514121985316880384
                            20769187434139310514121985316880384)
                          (Nat.shiftLeft
                            4503599627370496
                            128))
                        20769187434139310514121985316880384))
                    2048)))))))
      (Code.joinWords 131072
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          128)
                        256)
                      512)
                    1024)
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      10633823966279326983230456482242756608
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170143779608898499145501568964048715776
                          128)
                        256))
                    1024))
                (Code.joinWords 512
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      170141183460469231731687303715884105728
                      128)
                    256)
                  (Nat.shiftLeft
                    (Code.joinWords 128
                      151115727451828646838272
                      170141183460469231731687303715884105728)
                    256)))
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        20769187434139310514121985316880384
                        128)
                      1024)
                    2048)
                  4096)
                8192))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Code.joinWords 128
                          2251799813685248
                          36029346774777856)
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          128))
                      512)
                    1024)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        10633823966279326983230456482242756608
                        (Nat.shiftLeft
                          170143779608898499145501568964048715776
                          128))
                      512)
                    1024))
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      2814749767106560
                      512)
                    1024)
                  2048))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        18446744073709551616
                        128)
                      1024)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 128
                          13333818332717437350066314573437206528
                          20769187434139310514121985316880384)
                        13333818332717437350066314573437206528)
                      1024)
                    2048)
                  4096))))
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
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          16777216
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          16777216
                          256)
                        512))
                    2048))
                (Code.joinWords 512
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      170141183460469231731687303715884105728
                      128)
                    256)
                  (Nat.shiftLeft
                    (Code.joinWords 128
                      151115727451828646838272
                      170141183460469231731687303715884105728)
                    256)))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 512
                    (Nat.shiftLeft
                      319014718988379809496913694467282698240
                      256)
                    (Nat.shiftLeft
                      63802943797675961899382738893456539648
                      256))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          692295684049641781892387038035968
                          158456325028528675187087900672)
                        256)
                      512)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          20769504346789367571472359492681728
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          256))
                      (Nat.shiftLeft
                        20769504346789367571472359492681728
                        256))))
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            324518553658426726783156020576256
                            324518553658426726783156020576256)
                          256)
                        512)
                      (Nat.shiftLeft
                        20769187434139310514121985316880384
                        128))
                    2048)
                  4096)))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 2048
                  (Nat.shiftLeft
                    (Code.joinWords 256
                      (Code.joinWords 128
                        36028797018963968
                        36028934457917440)
                      (Nat.shiftLeft
                        170141183460469231731687303715884105728
                        128))
                    512)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      1125899906842624
                      512)
                    1024))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          68719476736
                          128)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          146028888064
                          128)
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          1125904201809920
                          68719476736)
                        512)))
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          128)
                        256)
                      512)
                    2048)))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          20282409603651670423947251286016
                          256)
                        (Nat.shiftLeft
                          20282409603651670423947251286016
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          20282409603651670423947251286016
                          256)
                        (Nat.shiftLeft
                          20282409603651670423947251286016
                          256))
                      1024))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        49152
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            43258576732788328326074996883456
                            158457288391291180594711494656)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          20282409603651670423947251286016
                          256)
                        (Nat.shiftLeft
                          20282409603651670423947251286016
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            316912650057057350374175801344
                            324518553658426726783156020576256)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          256))
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          18446744073709551616
                          128)
                        20599322253708727774321427087360))))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        20282409603651670423947251286016
                        256)
                      (Nat.shiftLeft
                        20282409603651670423947251286016
                        256))
                    1024)
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          309485009821345068724781056
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          309485009821345068724781056
                          256)
                        512))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            324518553658426726783156020576256
                            324518553658426726783156020576256)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          (Code.joinWords 128
                            324518863143436548128224745357312
                            324518553658426726783156020576256)))
                      (Code.joinWords 512
                        (Code.joinWords 128
                          20769187434139310514121985316880384
                          20769187434139310514121985316880384)
                        (Code.joinWords 256
                          20769187434139310514121985316880384
                          309485009821345068724781056)))))))))
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          33685504
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          33685504
                          256)
                        512))
                    2048)
                  4096)
                (Code.joinWords 4096
                  (Code.joinWords 512
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        170141183460469231731687303715884105728
                        128)
                      256)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        170141183460469382847414755544530944000
                        128)
                      256))
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5316911983139663491615228241121378304
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5316911983139663491615228241121378304
                          256)
                        512))
                    2048)))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          158456325028528675187087900672
                          128)
                        256)
                      512)
                    2048)
                  (Code.joinWords 512
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        308380895022100482513683237985039941632
                        128)
                      256)
                    (Code.joinWords 256
                      (Nat.shiftLeft
                        255211775190703847597530955573826158592
                        128)
                      (Nat.shiftLeft
                        309253200894334333555276361368348917760
                        128))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1267650600228229401496703205376
                          128)
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          2693757525484987478180494311424
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1267650600228229401496703205376
                          128)
                        256)))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          5316911983139663491615228241121378304
                          256)
                        (Nat.shiftLeft
                          5316911983139663491615228241121378304
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          5316911983139663491615228241121378304
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          (Code.joinWords 128
                            5316911983139663491903458617273090048
                            324518553658426726783156020576256)))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            20769187434139310514121985316880384
                            128)
                          5316993112778078098296924030126522368)
                        (Nat.shiftLeft
                          5316993112778078098585154406278234112
                          256)))))))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5316911983139663491615228241121378304
                          256)
                        512)
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            5316911983139663491615228241121378304
                            324518553658426726783156020576256)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          (Code.joinWords 128
                            5316911983139663491903458617273090048
                            324518553658426726783156020576256)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          5316911983139663491615228241121378304
                          256)
                        (Nat.shiftLeft
                          5316993112778078098585154406278234112
                          256)))
                    2048))
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        49152
                        (Nat.shiftLeft
                          10426025094304458364101316547969024
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            4722366482869645213696
                            128)
                          256)
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            255211775190703847597530955573826158592
                            128)
                          (Nat.shiftLeft
                            308380895022100482527518296040322105344
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            298411685053713613480739743088219521024
                            128)
                          (Nat.shiftLeft
                            309253200894334333569723908972953468928
                            128)))
                      (Code.joinWords 512
                        49152
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            40800647965378826507674089160704
                            4722366482869645213696)
                          256)))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          3104568876009149006774009856
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            3104568876009149006774009856
                            4722366482869645213696)
                          256)
                        512))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          5316913250790263719844629737824583680
                          256)
                        (Nat.shiftLeft
                          5316911983139663491615228241121378304
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          5316993112778078098296924030126522368
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            5316993112778078098585154406278234112
                            4722366482869645213696)
                          256))
                      1024))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            161150756227926642917376
                            161150756227926642917376)
                          256)
                        512)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          5316911983139663491615228241121378304
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            5316911983139663491903458617273090048
                            4722366482869645213696)
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            5316911983139663491615228241121378304
                            324518553658426726783156020576256)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          (Code.joinWords 128
                            5316911983139663491903458617273090048
                            324518553658426726783156020576256)))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            20769187434139328960866059026432000
                            128)
                          5316993112778078098296924030126522368)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            5316993112778078098585154406278234112
                            4722366482869645213696)
                          256))))))))
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
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            65536
                            1048576)
                          256)
                        (Nat.shiftLeft
                          16777216
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            65536
                            1048576)
                          256)
                        (Nat.shiftLeft
                          16777216
                          256)))
                    2048))
                (Code.joinWords 512
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      170141183460469231731687303715884105728
                      128)
                    256)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      170141183460469382847414755544530944000
                      128)
                    256)))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      49152
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          49164
                          128)
                        256))
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          2693757525484987478180494311424
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          158456325028528675187087900672
                          128)
                        256)))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          40723275532331869523081590472704
                          158456325028528675187087900672)
                        256)
                      512)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          128)
                        256)
                      512)))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          1267650600228229401496703205376
                          1267650600228229401496703205376)
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          49152
                          (Nat.shiftLeft
                            2693757525484992229032798978048
                            128))
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            247252677296128
                            128)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1267650600228229401496703205376
                            1267650600228233905165050052608)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            68719476736
                            128)
                          256))))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            68719476736
                            128)
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            4503599627370496
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          (Code.joinWords 128
                            324518553658426726783156020576256
                            324518553658426726783156020576256)))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            20769187434139310514121985316880384
                            128)
                          (Nat.shiftLeft
                            4503668346847232
                            128))
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            68719476736
                            128)
                          256)))))))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 128
                      170141183460469231731687303715884105728
                      170141183460469231731687338900256194560)
                    256)
                  512)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          128)
                        256)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          128)
                        (Code.joinWords 128
                          324518553658426726783156020576256
                          324518553658426726783156020576256)))
                    2048)
                  4096))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          20282409603651670423947251286016
                          256)
                        (Nat.shiftLeft
                          20282409603651670423947251286016
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            4722366482869645213696
                            128)
                          256)
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        49152
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            40723586141264913791125876113408
                            1123923222922975560859648)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          20282409603651670423947251286016
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            20282719093383858251885621280768
                            4722366482869645213696)
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          (Code.joinWords 128
                            309485009821345068724781056
                            324518553658426726783156020576256)))
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          20769187434139310514121985316880384
                          (Code.joinWords 128
                            309489732187827938369994752
                            4722366482869645213696))
                        512))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        65536
                        256)
                      (Nat.shiftLeft
                        21550060203879899825443954556928
                        256))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            4541120461668352
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            37520834297856
                            128)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            4503668346847232
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            4722366482938364690432
                            128)
                          256))))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            309646160577572995367698432
                            161150756227926642917376)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            309489732187827938369994752
                            4722366482938364690432)
                          256)
                        512))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            324518553658426726783156020641792
                            324518553658426731286755647946752)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          (Code.joinWords 128
                            324518863143436548128224745357312
                            324518553658426726783156020576256)))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            20769187434139310514121985316880384
                            20769187434139328960866059026432000)
                          (Code.joinWords 128
                            65536
                            4503668346847232))
                        (Code.joinWords 256
                          20769187434139310514121989611847680
                          (Code.joinWords 128
                            309489732187827938369994752
                            4722366482938364690432)))))))))))))

/-- The block word is computed from the verified profile data. -/
theorem word_eq :
    Code.profileWord 64 24 (fun i q => Data.profiles (192 + i) q) = word := by
  decide +kernel

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage003
