/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Cslib.Foundations.RelationAlgebra.FastCatalogueCoverage

/-!
# Profile coverage for models 2113–2176 of the ⟨1, 4, 0⟩ row

The balanced word contains exactly the cycle profiles of this block and its atom renamings.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage033

/-- The cycle profiles covered by this block of models. -/
def word : ℕ :=
  (Code.joinWords 524288
    (Code.joinWords 262144
      (Nat.shiftLeft
        (Nat.shiftLeft
          (Nat.shiftLeft
            (Nat.shiftLeft
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            317023473143131703101372249125026791424
                            128)
                          256)
                        512)
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            314362421003132603956450118940038791168
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            317024943617827967864627912584097431552
                            128)
                          256)
                        512))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            317023473212456345318503251903625822208
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            338458826248823699816229503589576343552
                            128)
                          256)
                        512))))
                8192)
              16384)
            32768)
          65536)
        131072)
      (Code.joinWords 131072
        (Nat.shiftLeft
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            170141183460469231731687303715884105728
                            332971612944121426162403668600226316288)
                          256)
                        512)
                      1024)
                    2048)
                  4096)
                8192)
              16384)
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            36029346774777856
                            36029346774777856)
                          (Nat.shiftLeft
                            170141183460469231731687303715884105728
                            128))
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          10097857501017186569656778880
                          562949953552384)
                        512)
                      1024))
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          38685626227668133592694784
                          131072)
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          38687987410909568415301632
                          131072)
                        512))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            549755863168
                            563680097992840)
                          (Code.joinWords 128
                            49280
                            2184))
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          2814749767106560
                          563095982440448)
                        512)
                      1024))
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2596148429267413814265248164610048
                            2596148429267413814265248164610048)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          256)
                        512))
                    2048)))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          131072
                          128)
                        512)
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          131072
                          128)
                        512)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170141183460469231731687303715884105728
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485644288
                            128)
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128))))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          131072
                          128)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170141183460469231731687303715884105728
                            128)
                          256)
                        (Nat.shiftLeft
                          131072
                          128))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170143779608898499145501568964048715776
                            128)
                          256)
                        (Nat.shiftLeft
                          131072
                          128))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170143779608898499145501568964048715776
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            2596148429267413814265248164610048
                            128)
                          (Code.joinWords 128
                            2596148429267413814265248164610048
                            2596148429267413814265248164610048)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170143779608898499145501568964048715776
                            128)
                          256)
                        (Code.joinWords 256
                          (Code.joinWords 128
                            41538374868278621028243970633760768
                            21267647932558653966460912964485513216)
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)))))))))
          65536)
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            319014718988379809496913694467282698240
                            128)
                          (Nat.shiftLeft
                            330313156952551594416596054479665627136
                            128))
                        512)
                      1024)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            332306999005650090111650018265244106752
                            128)
                          (Code.joinWords 128
                            170141183460469231731687303715884105728
                            332971613006018428126672682345182527488))
                        512)
                      1024)
                    2048)
                  4096))
              16384)
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            131080
                            128)
                          (Nat.shiftLeft
                            8
                            128))
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170143779608898499145501568964048715776
                          256)
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170143779608898499145501568964048715776
                          128)
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            170143779608898499145501568964048715776
                            170143779648512580402633737760820690944)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            2596148429267413814265248164610048
                            128)
                          (Code.joinWords 128
                            170143779608898499154724941000903491584
                            2596148429267413814265248164610048)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            170143779608898499145501568964048715776
                            170143779648512580402633737760820690944)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Code.joinWords 128
                            170143779608898499154724941000903491584
                            21267647932558653966460912964485513216))))))
                8192)
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170141183460469231731687303715884105728
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            319845486485745381931313631935240077312
                            128)
                          (Nat.shiftLeft
                            330479310452024708914580117214501797888
                            128)))
                      1024)
                    2048)
                  4096)
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          131072
                          128)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            170141183460469231731687303715884105728
                            170141183460469231731687303715884105728)
                          256)
                        (Nat.shiftLeft
                          170143779608898499154724941000903491584
                          256))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            170141183460469231731687303715884105728
                            170143779648512580402633737760820690944)
                          256)
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            170143779608898499145501568964048715776
                            170143779648512580402633737760820690944)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            2596148429267413814265248164610048
                            128)
                          (Code.joinWords 128
                            170143779608898499154724941000903491584
                            2596148429267413814265248164610048)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            170143779608898499145501568964048715776
                            170143779648512580402633737760820690944)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Code.joinWords 128
                            170143779608898499154724941000903491584
                            21267647932558653966460912964485513216)))))))))
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            297747071055821155530452781502797185024
                            332306998946228968225951765070086144000)
                          (Code.joinWords 128
                            298411685053713613466904685032937357312
                            332971612944121426162403668600226316288))
                        512)
                      1024)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            297747071055821155530452781502797185024
                            332306999005650090111650018265244106752)
                          (Code.joinWords 128
                            319679333045693389319063851192580833280
                            338330063364026370239316154556937666560))
                        512)
                      1024)
                    2048)
                  4096))
              16384)
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          170141183460469231731687303715884105728
                          170141183460469231731687303715884105728)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          170143779608898499145501568964048715776
                          170143779608898499145501568964048715776)
                        256))
                    2048)
                  4096)
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            131080
                            128)
                          (Code.joinWords 128
                            128
                            8))
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316911983139663491615228241121378304
                            128)
                          256)
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          170143779608898499145501568964048715776
                          170143779608898499145501568964048715776)
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            170143779608898499145501568964048715776
                            170143779648512580402633737760820690944)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            2596148429267413814265248164610048
                            128)
                          (Code.joinWords 128
                            2596148429267413814265248164610048
                            5319508131568930905717723865437700096)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            170143779608898499145501568964048715776
                            170143779648512580402633737760820690944)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Nat.shiftLeft
                            26584559915698317458364371581758603264
                            128)))))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            170141183460469231731687303715884105728
                            170141183460469231731687303715884105728)
                          256)
                        (Nat.shiftLeft
                          131072
                          128))
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            170141183460469231731687303715884105728
                            170143779648512580402633737760820690944)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            2596148429267413814265248164610048
                            128)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            170143779608898499145501568964048715776
                            170143779648512580402633737760820690944)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128))))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170141183460469231731687303715884105728
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            131072
                            128)
                          (Nat.shiftLeft
                            5316911983139663491903458617273090048
                            128)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            170141183460469231731687303715884105728
                            170141183460469231731687303715884105728)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316911983139663491903458754712043520
                            128)
                          256))
                      1024))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170141183460469231731687303715884105728
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            255876389188596305547817917159248494592
                            128)
                          (Nat.shiftLeft
                            314403959378000882577516643507505201152
                            128)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            170143779608898499145501568964048715776
                            170143779648512580402633737760820690944)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316911983139663491903458617273090048
                            128)
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            170143779608898499145501568964048715776
                            170143779648512580402633737760820690944)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            2596148429267413814265248164610048
                            128)
                          (Code.joinWords 128
                            2596148429267413814265248164610048
                            5319508131568930905717723865437700096)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            170143779608898499145501568964048715776
                            170143779648512580402633737760820690944)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            26584641045336732065046067370763747328))))))))))))
    (Code.joinWords 262144
      (Code.joinWords 131072
        (Nat.shiftLeft
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 512
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        536870912
                        536870912)
                      256)
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        536870912
                        170141183460469231731687303716420976640)
                      256))
                  2048)
                4096)
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      16384
                      1024)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      16384
                      1024)
                    2048)
                  4096)))
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      16384
                      1024)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      85070591730234615865843651857942069248
                      1024)
                    2048)
                  4096))
              16384))
          65536)
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        2475917857502623506959958016
                        128)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          2475917857502623506959958016
                          128)
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          128)))
                    1024)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          3106977138368098788242933760
                          128)
                        (Nat.shiftLeft
                          2417851639229258349543424
                          128))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          144115188109410304
                          128)
                        (Nat.shiftLeft
                          131072
                          128))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          144123984202432512
                          128)
                        (Nat.shiftLeft
                          131072
                          128)))))
                8192)
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          131072
                          128)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          131072
                          128)
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485644288
                            128)
                          (Code.joinWords 128
                            170141183460469231731687303715884105728
                            21267647932558653966460912964485513216))
                        512)))
                  4096)
                8192))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          37778931862957161760768
                          128)
                        (Nat.shiftLeft
                          51200
                          128))
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          2465259771498691897198600
                          128)
                        (Nat.shiftLeft
                          2184
                          128)))
                    1024)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          12089258196146291747061760
                          128)
                        (Nat.shiftLeft
                          2427333265683145059074048
                          128))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            2596148429267413814265248164610048
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            2596148429267413814265248164610048
                            128)
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          256)
                        512))))
                8192)
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170141183460469231731687303715884105728
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            330479310452024708900709030362200670208
                            128)
                          256))
                      1024)
                    2048)
                  4096)
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          131072
                          128)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            131072
                            128)
                          170143779608898499145501568964048715776)
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            131072
                            128)
                          170141183460469231731687303715884105728)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            2596148429267413814265248164610048
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            2596148429267413814265248164610048
                            128)
                          (Code.joinWords 128
                            170143779608898499145501568964048715776
                            2596148429267413814265248164610048)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          41538374868278621028243970633760768
                          128)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Code.joinWords 128
                            170143779608898499145501568964048715776
                            21267647932558653966460912964485513216)))))))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            16140901068253954048
                            3026418950163398656)
                          (Code.joinWords 128
                            536870912
                            572653568))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            131072
                            128)
                          (Nat.shiftLeft
                            131072
                            128)))
                      (Code.joinWords 128
                        4611756388245323776
                        70368744177664))
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        4611756387171581952
                        70368744194048)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 128
                          2305843009213693952
                          144115188109410304)
                        (Nat.shiftLeft
                          131072
                          128))
                      70368744194048))
                  4096))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          131072
                          128)
                        512)
                      (Code.joinWords 512
                        16384
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128))))
                    2048)
                  4096)
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      16384
                      1024)
                    (Nat.shiftLeft
                      16384
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        16384
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316911983139663491903458617273090048
                            128)
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            131072
                            128)
                          (Nat.shiftLeft
                            5319508131568930905717723865437700096
                            128))
                        512)
                      (Code.joinWords 512
                        16384
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            26584641045336732065046067370763747328))))))))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Code.joinWords 256
                        (Code.joinWords 128
                          16384
                          16384)
                        (Code.joinWords 128
                          16384
                          16384))
                      (Nat.shiftLeft
                        16384
                        256))
                    1024)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2596148429267413814265248164610048
                            2596148429267413814265248164610048)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2596148429267413814265248164610048
                            2596148429267413814265248164610048)
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          256)
                        512))
                    2048))
                8192)
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            2596148429267413814265248164610048
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            131072
                            128)
                          (Nat.shiftLeft
                            2596148429267413814265248164610048
                            128)))
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128))
                        512))
                    2048)
                  4096)
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        16384
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316911983139663491903458617273090048
                            128)
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316911983139663491903458617273090048
                            128)
                          256)
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            308380895022100482528094756792625528832
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            314403959378000882577516643507505201152
                            128)
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316911983139663491903458617273090048
                            128)
                          256)
                        512))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2596148429267413814265248164610048
                            2596148429267413814265248164610048)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            2596148429267413814265248164610048
                            128)
                          (Code.joinWords 128
                            2596148429267413814265248164610048
                            5319508131568930905717723865437700096)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            26584641045336732065046067370763747328)))))))))))
      (Code.joinWords 131072
        (Code.joinWords 65536
          (Nat.shiftLeft
            (Nat.shiftLeft
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            309377816078592405061425355276951748608
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            309548036211134166701516995322856865792
                            128)
                          256)
                        512))
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            309546565666841551316288334410949853184
                            128)
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            309546565736436992916004207808152076288
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            333474145205865053342844240568665505792
                            128)
                          256)
                        512))))
                8192)
              16384)
            32768)
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 1024
                    (Code.joinWords 512
                      (Code.joinWords 256
                        69324642199981295398109052928
                        536870912)
                      (Code.joinWords 256
                        (Code.joinWords 128
                          10096948445421382867684950016
                          131072)
                        (Code.joinWords 128
                          572653568
                          131072)))
                    (Code.joinWords 512
                      19807342860020988056753422336
                      302231454903657293676544))
                  2048)
                4096)
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          131072
                          128)
                        512)
                      (Code.joinWords 512
                        16384
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128))))
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            131072
                            128)
                          (Code.joinWords 128
                            2596148429267413814265248164610048
                            2596148429267413814265248164610048))
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128))
                        512))
                    2048)
                  4096)))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        19807342860020988055679680512
                        302231454903657293692928)
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        9903520314283042199192993792
                        (Code.joinWords 128
                          38685626227668133592694784
                          131072))
                      302231454903657293692928)
                    2048))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Code.joinWords 256
                        16384
                        (Code.joinWords 128
                          16384
                          16384))
                      (Code.joinWords 256
                        16384
                        16384))
                    1024)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2596148429267413814265248164610048
                            2596148429267413814265248164610048)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2596148429267413814265248164610048
                            2596148429267413814265248164610048)
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          256)
                        512))
                    2048)))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      16384
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        16384
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            332306999023600220681288032251281408
                            128)
                          256))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      16384
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            131072
                            128)
                          (Nat.shiftLeft
                            334903147452867634495553280415891456
                            128))
                        512)
                      (Code.joinWords 512
                        (Code.joinWords 256
                          16384
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Nat.shiftLeft
                            21599960002184655100059806983549616128
                            128))))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        16384
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            332306999023600220681288032251281408
                            128)
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            298411685113289477857513610762457710592
                            309419354455946235167581276830781407232)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            332306999023600220681288032251281408
                            128)
                          256)
                        512)))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            332306999023600220681288032251281408
                            128)
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2596148429267413814265248164610048
                            2596148429267413814265248164610048)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            2596148429267413814265248164610048
                            128)
                          (Code.joinWords 128
                            2596148429267413814265248164610048
                            334903147452867634495553280415891456)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            21599960002184655100059806983549616128))))))))))
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          256)
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          170143779608898499145501568964048715776
                          256)
                        (Nat.shiftLeft
                          170143779608898499145501568964048715776
                          256)))
                    2048)
                  4096)
                8192)
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            297747071055821155530452781502797185024
                            128)
                          (Nat.shiftLeft
                            308380895022100482513683237985039941632
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            319845486485745381917478573879957913600
                            128)
                          (Nat.shiftLeft
                            330479310452024708900709030362200670208
                            128)))
                      1024)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            131072
                            128)
                          170141183460469231731687303715884105728))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            170143779608898499154724941000903491584
                            2596148429267413814265248164610048)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          170143779608898499145501568964048715776
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Code.joinWords 128
                            170143779608898499154724941000903491584
                            21267647932558653966460912964485513216)))))
                  4096)))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            2048
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            131080
                            128)
                          (Nat.shiftLeft
                            8
                            128)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          170143779608898499145501568964048715776
                          256)
                        (Nat.shiftLeft
                          170143779608898499145501568964048715776
                          256))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            332306998946228968225951765070086144
                            128)
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            170143779608898499145501568964048715776
                            2596148429267413814265248164610048)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            2596148429267413814265248164610048
                            128)
                          (Code.joinWords 128
                            170143779608898499154724941000903491584
                            334903147452867634495553280415891456)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          170143779608898499145501568964048715776
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Code.joinWords 128
                            170143779608898499154724941000903491584
                            21599954931582254187142200996736794624))))))
                8192)
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            297747071055821155530452781502797185024
                            128)
                          (Nat.shiftLeft
                            329648542954659136493979209004807618560
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            319845486485745381931313631935240077312
                            128)
                          (Nat.shiftLeft
                            330853155825839216503834312950205644800
                            128)))
                      1024)
                    2048)
                  4096)
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            131072
                            128)
                          (Code.joinWords 128
                            170141183460469231731687303715884105728
                            332306999023600220681288032251281408))
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            265845599216404296466459665251226877952
                            128)
                          (Code.joinWords 128
                            170141183460469231731687303715884105728
                            309419354455946235167581276830781407232))
                        512)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          170143779608898499145501568964048715776
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            170143779608898499154724941000903491584
                            332306999023600220681288032251281408)
                          256))))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            170141183460469231731687303715884105728
                            332306999023609665414253771541708800)
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            170143779608898499145501568964048715776
                            2596148429267413814265248164610048)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            2596148429267413814265248164610048
                            128)
                          (Code.joinWords 128
                            170143779608898499154724941000903491584
                            334903147452867634495553280415891456)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            170143779608898499145501568964048715776
                            21267647932558653966460912964485513216)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Code.joinWords 128
                            170143779608898499154724941000903491584
                            21599960002184655100059806983549616128)))))))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          2228224
                          128)
                        256)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          131072
                          128)
                        (Code.joinWords 128
                          33685504
                          131072)))
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316911983139663491615228241121378304
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316911983139663491615228241121378304
                            128)
                          256)
                        512))
                    2048)
                  4096))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            131072
                            128)
                          (Nat.shiftLeft
                            2596148429267413814265248164610048
                            128))
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128))
                        512))
                    2048)
                  4096)
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      16384
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        16384
                        (Nat.shiftLeft
                          70368744177664
                          128))
                      1024))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170141183460469231731687303715884105728
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            314403959378000882562778613726935252992
                            128)
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316911983139663491903458617273090048
                            128)
                          256)
                        512))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            9007199254740992
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2596148429267413814265248164610048
                            5319508131568930905717723865437700096)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316911983139663491615228241121378304
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            26584641045336732065046067370763747328))))))))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            332306998946228968225951765070086144
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            332306998946228968225951765070086144
                            128)
                          256)
                        512))
                    2048)
                  4096)
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        16384
                        16384)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316911983139663491615228241121378304
                            128)
                          256)
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            332306998946228968225951765070086144
                            128)
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2596148429267413814265248164610048
                            2596148429267413814265248164610048)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            2596148429267413814265248164610048
                            128)
                          (Code.joinWords 128
                            2596148429267413814265248164610048
                            5651815130592531126399011897688981504)))
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Nat.shiftLeft
                            26916866914721917679045659614009884672
                            128))
                        512)))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      16384
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            170141183460469231731687303715884105728
                            309419354393807448039389337250883960832)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            332306999023600220681288032251281408
                            128)
                          256)
                        512)))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        16384
                        (Nat.shiftLeft
                          302231454903657293676544
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            2596148429267413814265248164610048
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            618970019642690137449562112
                            334903147452867634495553280415891456)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Code.joinWords 128
                            332306998946228968225951765070086144
                            21599960002184655100059806983549616128))))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          16384
                          (Nat.shiftLeft
                            5316911983139663491615228241121378304
                            128))
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            332306998946228968225951765070086144
                            5649218982163263712584746649524371456)
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            255211775190703847597530955573826158592
                            265845599216404296466459665251226877952)
                          (Code.joinWords 128
                            298743992112235706825739562527527796736
                            317394722430655730405004119192463474688))
                        512)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316911983139663491615228241121378304
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            332306998946228968225951765070086144
                            5649300111801678319266442438529515520)
                          256))))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            255211775190703847597530955573826158592
                            128)
                          (Nat.shiftLeft
                            313697807005240146019709985033746907136
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            255876389188596305547817917159248494592
                            128)
                          (Nat.shiftLeft
                            314902419876420226029855571155110330368
                            128)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316911983139663491615228241121378304
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            332306998946228968225951765070086144
                            5649224052765664625502352636337192960)
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2596148429267413814265248164610048
                            5319508131568930905429493489285988352)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            2596148429267413814265248164610048
                            128)
                          (Code.joinWords 128
                            334903147375496382040217013234696192
                            5651815130592531126399011897688981504)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            26584641045336732064757836994612035584)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Code.joinWords 128
                            21599960002107283847604470716368420864
                            26916953114962733198644961389827850240)))))))))))))

/-- The block word is computed from the verified profile data. -/
theorem word_eq :
    Code.profileWord 64 24 (fun i q => Data.profiles (2112 + i) q) = word := by
  decide +kernel

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage033
