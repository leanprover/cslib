/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Cslib.Foundations.RelationAlgebra.FastCatalogueCoverage

/-!
# Profile coverage for models 385–448 of the ⟨1, 4, 0⟩ row

The balanced word contains exactly the cycle profiles of this block and its atom renamings.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage006

/-- The cycle profiles covered by this block of models. -/
def word : ℕ :=
  (Code.joinWords 524288
    (Code.joinWords 262144
      (Code.joinWords 131072
        (Nat.shiftLeft
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            256212605621993638370906398738576572416
                            128)
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            256208696187542534516046120724132265984
                            256208696187542534516047246624039108608)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            256208696187542534502208810869036417024
                            256208696187542534502424983651150200832)
                          (Code.joinWords 128
                            256212605621993638375520547663050178560
                            256212605621993638375521673614496628736))
                        512)))
                  4096)
                8192)
              16384)
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
                          170141183460469231731687303715884105728
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          128)
                        256)))
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          128)
                        256))
                    2048))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          128)
                        256))
                    2048)
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          140737488355328
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          140737488355328
                          128)
                        256))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          128)
                        256)))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          13835058055282163712
                          128)
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          297747071055821155530452781502797185024
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          297747071055821155530452781502797185024
                          128)
                        256)))
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          297747071055821155546593682567293042688
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          297747071055821155546593682567293042688
                          128)
                        256))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          16140901064495857664
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          16140901064495857664
                          128)
                        256))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          311039351013670314259490852105600630784
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          311039351013670314259490852105600630784
                          128)
                        256)))
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          311039351013670314275631753170096488448
                          128)
                        256)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            311039351013670314276208213922399911936
                            128)
                          256)
                        41538374868278621028243970633760768))
                    2048)))))
          65536)
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      255876389188596305533982859103966330880
                      512)
                    1024)
                  4096)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          255464902197858620900880620263282049024
                          128)
                        (Nat.shiftLeft
                          256212605621993638361683026701721796608
                          128))
                      512)
                    1024)
                  2048))
              16384)
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        10633823966279326983230456482242756608
                        256)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        10633823966279326983230456482242756608
                        256)
                      (Nat.shiftLeft
                        10633823966279326983230456482242756608
                        256))))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10141204801825835211973625643008
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          12676506002282294014967032053760
                          128)
                        256))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          830767497365572420564879412675215360
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          830767497365572420564879412675215360
                          128)
                        256))
                    2048)))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          255876389188596305533982859103966330880
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10675524600424434817622092030886805504
                          256)
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          298577838553186727951017660915472400384
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10675362341147605604258700452876517376
                          256)
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          10675362341147605604258700452876517376
                          10675524600424434817622092030886805504)
                        512))))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          830767497365572420564879412675215360
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          830767497365572420564879412675215360
                          128)
                        256))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          830767497365572420564879412675215360
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          830767497365572420564879412675215360
                          128)
                        256))
                    2048)))))
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            170141183460469231731687303715884105728
                            128)
                          (Code.joinWords 128
                            256208696187542534502208810869036417024
                            256208696187542534502208810869036417024))
                        512)
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        211655988346880
                        128)
                      256)
                    512))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            255464899662557420444421817269875638272
                            255464902197858620901096793045395832832)
                          (Code.joinWords 128
                            256212605621993638361683026701721796608
                            256212605621993638375572339883398660096))
                        512)
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          72057594037927936
                          1099511627776)
                        512)
                      1024)
                    2048)))
              16384)
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10141204801825835211973625643008
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10141204801825835211973625643008
                          128)
                        256))
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        140737488355328
                        128)
                      256)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          830767497365572420564879412675215360
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          830767497365572420564879412675215360
                          128)
                        256))))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10141204801825835211973625643008
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          12676506002282294014967032053760
                          128)
                        256))
                    2048)
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          35734127902720
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          549755813888
                          128)
                        256))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          830767497365572420564879412675215360
                          128)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          664613997892457936451903530140172288
                          830767497365572420564879412675215360)
                        256)))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          664613997892457936451903530140172288
                          830767497365572420564879412675215360)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          664613997892457936451903530140172288
                          830767497365572420564879412675215360)
                        256))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          664613997892457936451903530140172288
                          830767497365572420564879412675215360)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          664613997892457936451903530140172288
                          830767497365572420564879412675215360)
                        256))
                    2048))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          664613997892457936451903530140172288
                          830767497365572420609915408948920320)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          664613997892457936523961124178100224
                          830767497365572420609915408948920320)
                        256))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          664613997892457936523961124178100224
                          830767497365572420609915408948920320)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          664613997892457936523961124178100224
                          830767497365572420609915408948920320)
                        256))
                    2048)))))))
      (Code.joinWords 131072
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          128)
                        256)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          128)
                        256)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        664613997892457936451903530140172288
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        664613997892457936451903530140172288
                        256)
                      (Nat.shiftLeft
                        664613997892457936451903530140172288
                        256))))
                8192)
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      265845599156983174580761412056068915200
                      128)
                    1024)
                  2048)
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          265845599156983174580761412056068915200
                          128)
                        256)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          311039351013670314259490852105600630784
                          128)
                        256)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          706162513965538383315359474399576064
                          128)
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          706152372760736557480147500773933056
                          128)
                        256)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          706152372760736557480147500773933056
                          128)
                        (Nat.shiftLeft
                          706162513965538383315359474399576064
                          128)))))))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          162259276829213363391578010288128
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          202824096036516704239472512860160
                          256)
                        512))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          13292279957849158729038070602803445760
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          13292279957849158729038070602803445760
                          256)
                        512)))
                  4096)
                8192)
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          259203393965521703640304622521416679424
                          128)
                        (Nat.shiftLeft
                          271166648751681983013143125536452640768
                          128))
                      512)
                    1024)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          13292279957849158729038070602803445760
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          13292279957849158729038070602803445760
                          256)
                        512))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          13292279957849158729038070602803445760
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          13292279957849158729038070602803445760
                          256)
                        512)))
                  4096))))
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
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        2596148429267413814265248164610048
                        128)
                      256)
                    512))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          128)
                        256)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          128)
                        256)
                      1024))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          649037107316853453566312041152512
                          128)
                        256)
                      (Nat.shiftLeft
                        664613997892457936451903530140172288
                        256))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        706152372760736557480147500773933056
                        256)
                      (Nat.shiftLeft
                        706152372760736557480147500773933056
                        256)))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        255211775190703847597530955573826158592
                        128)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        265845599156983174580761412056068915200
                        128)
                      1024))
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        3904363848702946556609845872558080
                        128)
                      256)
                    512))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          265845599156983174580761412056068915200
                          128)
                        256)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          311039351013670314259490852105600630784
                          128)
                        256)
                      1024))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            649037107316853453566312041152512
                            651572408517309912369305447563264)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          706162513965538383315359474399576064
                          128)
                        256))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          706152372760736557480147500773933056
                          128)
                        256)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          706172655170340209150571448025219072
                          128)
                        (Nat.shiftLeft
                          706162513965538383315359474399576064
                          128)))))))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        2596148429267413814265248164610048
                        128)
                      256)
                    512)
                  4096)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        651572408517309912369305447563264
                        128)
                      256)
                    512)
                  4096))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          3904363848702946556821501860904960
                          128)
                        256)
                      512)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            20282409603651670423947251286016
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            20282409603651670423947251286016
                            128)
                          256))
                      1024))
                  4096)
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1329227995784915872903807060280344576
                            20282409603651670423947251286016)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            20282409603651670423947251286016
                            128)
                          (Code.joinWords 128
                            1329227995784915872975864654318272512
                            20282409603651670423947251286016)))
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          649037107316853453566312041152512
                          651572408517309912369305447563264)
                        256)
                      512)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          1329227995784915872903807060280344576
                          256)
                        (Nat.shiftLeft
                          1329227995784915872975864654318272512
                          256))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          1370766370653194493932051030914105344
                          (Code.joinWords 128
                            1329227995784915872903807060280344576
                            20282409603651670423947251286016))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            1329227995784915872903807060280344576
                            20282409603651670423947251286016)
                          (Code.joinWords 128
                            1329227995784915872975864654318272512
                            20282409603651670423947251286016))))))))))
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      170141183460469231731687303715884105728
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      170141183460469231731687303715884105728
                      1024)
                    (Nat.shiftLeft
                      11298437964171784919682360012382928896
                      1024)))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          128)
                        256)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          128)
                        256)
                      1024))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          649037107316853453566312041152512
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          706152372760736557480147500773933056
                          128)
                        256))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          706152372760736557480147500773933056
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          706152372760736557480147500773933056
                          128)
                        256)))))
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          265845599156983174580761412056068915200
                          128)
                        (Nat.shiftLeft
                          265845599156983174580761412056068915200
                          128))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          265845599156983174580761412056068915200
                          128)
                        (Nat.shiftLeft
                          311039351013670314259490852105600630784
                          128))
                      1024))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            651572408517309912369305447563264
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          706162513965538383315359474399576064
                          128)
                        256))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          706152372760736557480147500773933056
                          128)
                        256)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          706172655170340209150571448025219072
                          128)
                        (Nat.shiftLeft
                          706162513965538383315359474399576064
                          128)))))
                8192))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          649037107316853453566312041152512
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10675362341147605604258700452876517376
                          256)
                        512)))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10675362341147605604258700452876517376
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10675362341147605604258700452876517376
                          256)
                        512))))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          689601926524156794414206543724544
                          128)
                        256)
                      512)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        651572408517309912369305447563264
                        128)
                      256)
                    512)))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          255876389188596305533982859103966330880
                          255876389188596305533982859103966330880)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            689601926524156794414206543724544
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10675524600424434817622092030886805504
                          256)
                        512)))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          255876389188596305533982859103966330880
                          298577838553186727951017660915472400384)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10675362341147605604258700452876517376
                          256)
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          10675363608798205832488101949579722752
                          10675524600424434817622092030886805504)
                        512))))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            689601926524156794414206543724544
                            128)
                          256)
                        512)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            20282409603651670423947251286016
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            20282409603651670423947251286016
                            128)
                          (Nat.shiftLeft
                            20282409603651670423947251286016
                            128))))
                    2048)
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            651572408517309912369305447563264
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1267650600228229401496703205376
                            128)
                          (Code.joinWords 128
                            1267650600228229401496703205376
                            1267650600228229401496703205376))
                        512))
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            20282409603651670423947251286016
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21550060203879899825443954491392
                            128)
                          (Code.joinWords 128
                            1267650600228229401496703205376
                            21550060203879899825443954491392)))
                      1024))))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      170141183460469231731687303715884105728
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          2596148429267413814265248164610048
                          128)
                        256)
                      512)
                    (Nat.shiftLeft
                      664613997892457936451903530140172288
                      1024)))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          128)
                        256)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          128)
                        256)
                      1024))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          649037107316853453566312041152512
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          706152372760736557480147500773933056
                          128)
                        256))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          706152372760736557480147500773933056
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          706162513965538383315359474399576064
                          128)
                        256)))))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        4067256950832274034702172234448896
                        128)
                      256)
                    512)
                  4096)
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          265845599156983174580761412056068915200
                          128)
                        (Nat.shiftLeft
                          265845599156983174580761412056068915200
                          128))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            308380895022100482513683237985039941632
                            128)
                          (Nat.shiftLeft
                            311039351013670314259490852105600630784
                            128))
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            137438953472
                            128)
                          256))
                      1024))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            649037107316853453566312041152512
                            651572408517309912404627258605568)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          706162513965538383315359474399576064
                          128)
                        256))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          706152372760736557480147500773933056
                          128)
                        256)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          706172655170340209150571448025219072
                          128)
                        (Nat.shiftLeft
                          706162513965538383315359474399576064
                          128)))))))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        689601926524156794414206543724544
                        256)
                      512)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        2596148429267413814265248164610048
                        128)
                      256)
                    512))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          689601926524156794414206543724544
                          128)
                        256)
                      512)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        651572408517309912369305447563264
                        128)
                      256)
                    512)))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          319014718988379809510892867710640717824
                          319014718988379809510964925304678645760)
                        256)
                      512)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          689601926524156794414206543724544
                          128)
                        256)
                      512))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            4067256950832274034913828222795776
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          1267650600228229401496703205376
                          17179869184)
                        512))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          20769504346789367572598259399524352
                          256)
                        512)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            20282409603651670423947251286016
                            128)
                          256)
                        (Code.joinWords 256
                          1267650600228229401496703205376
                          (Code.joinWords 128
                            20769504346789367572598259399524352
                            20282409603651670423947251286016))))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          1329227995784915872903807060280344576
                          256)
                        (Nat.shiftLeft
                          1329227995784915872903807060280344576
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            689601926524156794414206543724544
                            128)
                          256)
                        512)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1329227995784915872903807060280344576
                            20282409603651670425184201867264)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            20282409603651670423947251286016
                            128)
                          (Code.joinWords 128
                            1329227995784915872975864654318272512
                            20282409603651670425046762913792)))))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            649037107316853453566329221021696
                            651572408517309912404627258605568)
                          256)
                        512)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          1329227995784915872903807060280344576
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1267650600228229401496703205376
                            128)
                          (Code.joinWords 128
                            1329229263435516101133208574163419136
                            1267650600228229401496703205376))))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          1329227995784915872903807060280344576
                          256)
                        (Nat.shiftLeft
                          1349997500131705240548462913717796864
                          256))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          1329227995784915872903807060280344576
                          (Code.joinWords 128
                            1329227995784915872903807060280344576
                            20282409603651670425046762913792))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            1329227995784915872903807060280344576
                            21550060203879899825443954491392)
                          (Code.joinWords 128
                            1349998767782305468777864410421002240
                            21550060203879899826543466119168))))))))))))
    (Code.joinWords 262144
      (Code.joinWords 131072
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
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
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          256)
                        512))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          256)
                        512))))
                8192)
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        59421121885698253195157962752
                        256)
                      512)
                    1024)
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          297747071055821155530452781502797185024
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          297747071055821155530452781502797185024
                          256)
                        512))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          297747071125145797730434076897148141568
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          297747071125145797730434076897148141568
                          256)
                        512))))
                8192))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          604462909807314587353088
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          604462909807314587353088
                          256)
                        512))
                    2048)
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          256)
                        512))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          256)
                        512))))
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            271166648791296064270275294333224615936
                            128)
                          256)
                        512)
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            271162511199553631364631810525745905664
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            271162511199558467067910269042444730368
                            128)
                          256))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            271162511140122838072376640297190293504
                            128)
                          (Nat.shiftLeft
                            271166648811113682999763006736889282560
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            271162511140180866511718142497576189952
                            128)
                          (Nat.shiftLeft
                            271166648811118518924402394138102726656
                            128))))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 1024
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        69324642199981295394350956544
                        256)
                      512)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        69324642199981295394350956544
                        256)
                      512))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          298577838553186727951017660915472400384
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          298577838553186727951017660915472400384
                          256)
                        512))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          298577838622511370150998956309823356928
                          256)
                        512)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          41538374868278621028243970633760768
                          128)
                        (Nat.shiftLeft
                          298577838622666112655909628844185747456
                          256))))))))
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
                  2048)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      170141183460469231731687303715884105728
                      128)
                    256)
                  512))
              (Code.joinWords 4096
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        906694364710971881029632
                        128)
                      256)
                    512)
                  2048)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      211106232532992
                      128)
                    256)
                  512)))
            (Nat.shiftLeft
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        19342813185891660833226752
                        256)
                      (Code.joinWords 256
                        5649218982085892459841180006191464448
                        19342813185891660833226752))
                    2048)
                  4096)
                8192)
              16384)))
        (Code.joinWords 65536
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
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        2596148429267413814265248164610048
                        128)
                      256)
                    512))
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        2596148429267413814265248164610048
                        128)
                      256)
                    512)
                  2048))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        255211775190703847597530955573826158592
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          4056481920730334084789450257203200
                          128)
                        256)
                      512))
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      255876389188596305533982859103966330880
                      512)
                    1024))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          4056481921674807381363379299942400
                          128)
                        256)
                      512)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1267650600228229401496703205376
                            1267650600228229401496703205376)
                          256)
                        512)
                      1024)
                    2048))))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          649037107316853453566312041152512
                          256)
                        512)
                      (Nat.shiftLeft
                        10633823966279326983230456482242756608
                        256)))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        10675362341147605604258700452876517376
                        256)
                      (Nat.shiftLeft
                        10675362341147605604258700452876517376
                        256))))
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        689601926524156794414206543724544
                        128)
                      256)
                    512)
                  2048))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          255876389188596305533982859103966330880
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            649037107316853453566312041152512
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            689601926524156794414206543724544
                            128)
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10675524600424434817622092030886805504
                          256)
                        512)))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          298577838553186727951017660915472400384
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10675362341147605604258700452876517376
                          256)
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          10675363608798205832488101949579722752
                          10675524600424434817622092030886805504)
                        512))))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          649037107316853453566312041152512
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          689601926524156794414206543724544
                          128)
                        256))
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            83076749736557242056487941267521536
                            83076749755900055170322008062820352)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1267650600228229401496703205376
                            128)
                          (Code.joinWords 128
                            1267650600228229401496703205376
                            1267650600228229401496703205376)))
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          83076749736557242056487941267521536
                          83076749755900055170322008062820352)
                        256)
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            124615124604835863084731911901282304
                            83076749736557242056487941267521536)
                          (Code.joinWords 128
                            83076749736557242056487941267521536
                            83076749755900055170322008062820352))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1267650600228229401496703205376
                            128)
                          (Code.joinWords 128
                            1267650600228229401496703205376
                            1267650600228229401496703205376)))))))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        2596148429267413814265248164610048
                        128)
                      256)
                    512)
                  2048)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        2596148429267413814265248164610048
                        128)
                      256)
                    512)
                  2048))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          4056481920730334084789450257203200
                          128)
                        256)
                      512)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        211655988346880
                        128)
                      256)
                    512))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          4056481921674807381363379299942400
                          128)
                        256)
                      512)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          20769504346789367571472359492681728
                          256)
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            72057594037927936
                            1099511627776)
                          (Code.joinWords 128
                            20770771997389595800873856195887104
                            1267650600228229401496703205376))
                        512))
                    2048))))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        649037107316853453566312041152512
                        256)
                      512)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      140737488355328
                      128)
                    256))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          689601926524156794414206543724544
                          128)
                        256)
                      512)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      35184372088832
                      128)
                    256)))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          319014718988379809496913694467282698240
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          319014718988379809506137066504137474048
                          128)
                        256))
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          649037107316853453566312041152512
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          689601926524156794414206543724544
                          128)
                        256)))
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        1267650600228229401496703205376
                        512)
                      1024)
                    2048))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            649037107316853453566312041152512
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            689601926524156794414206543724544
                            128)
                          256))
                      (Nat.shiftLeft
                        72057594037927936
                        256))
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            83076749736557242056487941267521536
                            83076749755900055170322008062820352)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1267650600228229401496703205376
                            128)
                          (Code.joinWords 128
                            1267650600228229401496703205376
                            1267650600228229401496703205376)))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            83076749736557242128545535305449472
                            83076749755900055170322008062820352)
                          256)
                        (Nat.shiftLeft
                          20769504346789367571472359492681728
                          256))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            83076749736557242056487941267521536
                            83076749736557242056487941267521536)
                          (Code.joinWords 128
                            83076749736557242128545535305449472
                            83076749755900055170322008062820352))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1267650600228229401496703205376
                            128)
                          (Code.joinWords 128
                            20770771997389595801999756102729728
                            1267650600228229401496703205376)))))))))))
      (Code.joinWords 131072
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        604462909807314587353088
                        256)
                      512)
                    2048)
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          162259276829213363391578010288128
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          162259276829213363391578010288128
                          256)
                        512))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          13292279957849158729038070602803445760
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          13292279957849158729038070602803445760
                          256)
                        512))))
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          944473296573929042739200
                          128)
                        256)
                      512)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          271162511140122838072376640297190293504
                          128)
                        256)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          128)
                        (Nat.shiftLeft
                          271162511140122838072376640297190293504
                          128)))
                    1024))
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          10633823966279326983230456482242756608
                          256)
                        (Nat.shiftLeft
                          13292279957849158729038070602803445760
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          10633823966279326983230456482242756608
                          256)
                        (Nat.shiftLeft
                          13292279957849158729038070602803445760
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          10633823966279326983230456482242756608
                          256)
                        (Nat.shiftLeft
                          13292279957849158729038070602803445760
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          10633823966279326983230456482242756608
                          256)
                        (Nat.shiftLeft
                          13292279957849158729038070602803445760
                          256))))
                  4096)))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          188894659314785808547840
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          37778931862957161709568
                          256)
                        512))
                    2048)
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          162259276829213363391578010288128
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          202824096036516704239472512860160
                          256)
                        512))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          13292279957849158729038070602803445760
                          256)
                        512)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          10633823966279326983230456482242756608
                          256)
                        (Nat.shiftLeft
                          13292279957849158729038070602803445760
                          256)))))
                8192)
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            259203353400702496336963774626914107392
                            128)
                          (Nat.shiftLeft
                            271166648751681983013143125536452640768
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            259203393965579732079646124721802575872
                            128)
                          (Nat.shiftLeft
                            271166648814817888379460024963931570176
                            128)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          19342813113834066795298816
                          128)
                        (Nat.shiftLeft
                          295147905179352825856
                          128))
                      1024))
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          10633823966279326983230456482242756608
                          256)
                        (Nat.shiftLeft
                          13292279960944008827251521290051256320
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          10633823966298669796344290549038055424
                          256)
                        (Nat.shiftLeft
                          13292279960944008827251521290051256320
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          10633823966298669796344290549038055424
                          256)
                        (Nat.shiftLeft
                          13292279960944008827251521290051256320
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          10633823966298669796344290549038055424
                          256)
                        (Nat.shiftLeft
                          13292279960944008827251521290051256320
                          256))))
                  4096))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        2596148429267413814265248164610048
                        128)
                      256)
                    512)
                  4096)
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        604462909807314587353088
                        256)
                      512)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      649037107316853453566312041152512
                      128)
                    256)))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          944473296573929042739200
                          128)
                        256)
                      512)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        3904363848702946556609845872558080
                        128)
                      256)
                    512))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        319014718988379809496913694467282698240
                        319014719027993890754045863264054673408)
                      256)
                    512)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          649037107316853453566312041152512
                          651572408517309912369305447563264)
                        256)
                      512)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        20282409603651670423947251286016
                        128)
                      1024)))))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        2596148429267413814265248164610048
                        128)
                      256)
                    512)
                  4096)
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        151115727451828646838272
                        256)
                      512)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        651572408517309912369305447563264
                        128)
                      256)
                    512)))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          3904363848702946556821501860904960
                          128)
                        256)
                      512)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          20769504346789367571472359492681728
                          128)
                        256)
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            19342813113834066795298816
                            128)
                          (Nat.shiftLeft
                            20789786756393019241896306743967744
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            295147905179352825856
                            128)
                          (Nat.shiftLeft
                            20282409603651670423947251286016
                            128)))))
                  4096)
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1329227995784915872903807060280344576
                            20282409603651670423947251286016)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            20282409603651670423947251286016
                            128)
                          (Code.joinWords 128
                            1329227995784915872975864654318272512
                            20282409603651670423947251286016)))
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            649037107316853453566312041152512
                            651572408517309912369305447563264)
                          256)
                        512)
                      (Nat.shiftLeft
                        19342813113834066795298816
                        256))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1329227995804258686017641127075643392
                            20769504346789367571472359492681728)
                          256)
                        (Nat.shiftLeft
                          1329227995784915872975864654318272512
                          256))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          1329227995784915872903807060280344576
                          (Code.joinWords 128
                            1329227995804258686017641127075643392
                            20789786761228722520354823442792448))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            1329227995784915872903807060280344576
                            20282409603651670423947251286016)
                          (Code.joinWords 128
                            1329227995784915872975864654318272512
                            20282409603651670423947251286016))))))))))
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          2596148429267413814265248164610048
                          128)
                        256)
                      512)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      170141183460469231731687303715884105728
                      1024)
                    (Nat.shiftLeft
                      10633823966279326983230456482242756608
                      1024)))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          2596148429267413814265248164610048
                          128)
                        256)
                      512)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      651572408517309912369305447563264
                      128)
                    256)))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        4067256950832274034702172234448896
                        128)
                      256)
                    512)
                  2048)
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          319014719047839617008839615796031258624
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          319014719047858959821953449862826557440
                          128)
                        256))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            4067256951776747331276101277188096
                            128)
                          256)
                        512)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          20282409603651670423947251286016
                          128)
                        (Nat.shiftLeft
                          73786976294838206464
                          128))))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          651572408517309912369305447563264
                          128)
                        256)
                      512)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          20769504351625070849930876191506432
                          128)
                        256)
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            20282409603651670423947251286016
                            128)
                          (Nat.shiftLeft
                            20769504351625070849930876191506432
                            128))
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1267650600228229401496703205376
                            1267650600228229401496703205376)
                          256)))))))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          649037107316853453566312041152512
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10675362341147605604258700452876517376
                          256)
                        512)))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10675362341147605604258700452876517376
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10675524600424434817622092030886805504
                          256)
                        512))))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          689601926524156794414206543724544
                          128)
                        256)
                      512)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        651572408517309912369305447563264
                        128)
                      256)
                    512)))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          255876389188596305533982859103966330880
                          255876389188596305533982859103966330880)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            649037107316853453566312041152512
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            689601926684717254831774480990208
                            128)
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10675524600424434817622092030886805504
                          256)
                        512)))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          298411685053713613466904685032937357312
                          (Code.joinWords 128
                            298577838553186727951017660915472400384
                            9444732965739290427392))
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10675362341147605604258700452876517376
                          256)
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          10675363608798205832488101949579722752
                          10675524600424434817622092030886805504)
                        512))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          83076749736557242056487941267521536
                          83076749736557242056487941267521536)
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            649037107316927240542606879358976
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            689601926684717254831774480990208
                            128)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            83076749736557242056487941267521536
                            83097032146160967513888183357014016)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            20282409603651670423947251286016
                            128)
                          (Nat.shiftLeft
                            20282409603651670423947251286016
                            128)))))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            651572408517309912369305447563264
                            128)
                          256)
                        512)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            83076749736557242056487941267521536
                            83076749755900055170322008062820352)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1267650600228229401496703205376
                            128)
                          (Code.joinWords 128
                            1267650609968110272415346458624
                            1267650600523377306676056031232))))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          83076749736557242056487941267521536
                          103846254107525126020252884254326784)
                        256)
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            83076749736557242056487941267521536
                            83076749736557242056487941267521536)
                          (Code.joinWords 128
                            83076749736557242056487941267521536
                            103866536517128777690676831505612800))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21550060203879899825443954491392
                            128)
                          (Code.joinWords 128
                            1267650600523377306676056031232
                            21550060204175047730623307317248)))))))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          2596148429267413814265248164610048
                          128)
                        256)
                      512)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        2596148429267413814265248164610048
                        128)
                      256)
                    512))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          2596148429267413814265248164610048
                          128)
                        256)
                      512)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      651572408517309912369305447563264
                      128)
                    256)))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          4067256950832274034702172234448896
                          128)
                        256)
                      512)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          4067256950832274034702172234448896
                          128)
                        256)
                      512)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            20769504351625070849930876191506432
                            128)
                          256)
                        (Nat.shiftLeft
                          20769504346789367572598259399524352
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            20769504351625070849930876191506432
                            128)
                          256)
                        (Nat.shiftLeft
                          20769504346789367572598259399524352
                          256)))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          319014719047800931382611947662440660992
                          319014719047839617026133438365133963264)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          319014719047858959821953449862826557440
                          319014719047858959839247272431930048512)
                        256))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            9007199254740992
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            4067256951779108514517536099794944
                            128)
                          256))
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          20282409603651670423947251286016
                          128)
                        (Nat.shiftLeft
                          73786994161902157824
                          128))))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            649037107316853453566329221021696
                            651572408517309912404627258605568)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          17179869184
                          256)
                        512))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            20769504351625070851056930717171712
                            128)
                          256)
                        (Nat.shiftLeft
                          20769504346789367572598259399524352
                          256))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            20282409603651670423947251286016
                            128)
                          (Nat.shiftLeft
                            20769504351625070851056793278218240
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1267650600228229401496703205376
                            128)
                          (Code.joinWords 128
                            20770771997389595801999756102729728
                            1267650600228229401496703205376))))))))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        689601926524156794414206543724544
                        256)
                      512)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        2596148429267413814265248164610048
                        128)
                      256)
                    512))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          649037107316853453566312041152512
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          689601926524156794414206543724544
                          128)
                        256))
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        649037107316853453566312041152512
                        651572408517309912369305447563264)
                      256)
                    512)))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          319014718988379809510748752522564861952
                          319014718988379809510964925304678645760)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          319014719062656211868015684204588171264
                          319014719062656211868087741798626885632)
                        256))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            649037107316927240542606879358976
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            689601926684717254831774480990208
                            128)
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          73786976294838206464
                          128)
                        256)))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            618970019642690137449562112
                            4067256950832274034922624315817984)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          1267650600228229401496703205376
                          94447329657410084143104)
                        512))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            20769504351625070849930876191506432
                            128)
                          256)
                        (Nat.shiftLeft
                          20769504351634589370998810226982912
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            20789786761228722520354823442792448
                            128)
                          256)
                        (Code.joinWords 256
                          (Code.joinWords 128
                            1267650600228229401496703205376
                            20282409603651670423947251286016)
                          (Code.joinWords 128
                            20769504351625144638033070936555520
                            20282409603651670423947251286016))))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            262144
                            128)
                          256)
                        (Nat.shiftLeft
                          262144
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1412304745521473114960295001547866112
                            83076749736557242056487941267783680)
                          256)
                        (Nat.shiftLeft
                          1329227995784915872903807060280606720
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            649037107316927240542606879358976
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            689601926684717254831774480990208
                            128)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1412304745521473114960295001547866112
                            83097032165503780627723349663940608)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            20282409603651670423947251286016
                            128)
                          (Code.joinWords 128
                            1329227995784915872975864654318272512
                            20282409603651670425046762913792)))))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            649037107316853453566329221021696
                            651572408517309912404627258605568)
                          256)
                        512)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1412304745521473114960295001547866112
                            83076749755900055170322008062820352)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1267650600228229401496703205376
                            128)
                          (Code.joinWords 128
                            1329229263435516396353171347554172928
                            1267650600523377306676056031232))))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1412304745521473114960295001547866112
                            103846254107525126021378801341038592)
                          256)
                        (Nat.shiftLeft
                          1349997500136541017613897725254828032
                          256))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            1412304745521473114960295001547866112
                            83076749736557242056487941267521536)
                          (Code.joinWords 128
                            1412304745521473114960295001547866112
                            103866536517128777691803848103952384))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            1329227995784915872903807060280344576
                            21550060203879899825443954491392)
                          (Code.joinWords 128
                            1349998767787141540991204401310859264
                            21550060204175047731722818945024)))))))))))))

/-- The block word is computed from the verified profile data. -/
theorem word_eq :
    Code.profileWord 64 24 (fun i q => Data.profiles (384 + i) q) = word := by
  decide +kernel

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage006
