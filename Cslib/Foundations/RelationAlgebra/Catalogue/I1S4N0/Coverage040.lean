/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Cslib.Foundations.RelationAlgebra.FastCatalogueCoverage

/-!
# Profile coverage for models 2561–2624 of the ⟨1, 4, 0⟩ row

The balanced word contains exactly the cycle profiles of this block and its atom renamings.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage040

/-- The cycle profiles covered by this block of models. -/
def word : ℕ :=
  (Code.joinWords 524288
    (Nat.shiftLeft
      (Nat.shiftLeft
        (Nat.shiftLeft
          (Nat.shiftLeft
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            170143779608898499145501568964048715776
                            170143779608898499145501568964048715776)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            225971517691141795033074648060281225216
                            225971517691141795033074648060281225216)
                          256)
                        512)
                      1024))
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            225972207293068319177619271280377200640
                            128)
                          (Code.joinWords 128
                            212679724511123123931876961205060894720
                            225972207293068319177619271280377200640))
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            225972207332682400443974812116151435264
                            128)
                          (Code.joinWords 128
                            225972207293068319189869062266824949760
                            225972207345061800839855033814735650816))
                        512)
                      1024))
                  4096))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            212679075474015807087646907667362873344
                            212679724511123123941100473979404025856)
                          (Code.joinWords 128
                            225972207293068319187419244807023755264
                            225972207293068319187419253603116777472))
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            225971355431864965816684978270166319104
                            225972207293068319186842784054720331776)
                          (Code.joinWords 128
                            225972207342586525224194221314865627136
                            225972207345681413101339543757515653120))
                        512)
                      1024))
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            212679075474015807087646907667362873344
                            225972207332682400443974952851492306944)
                          (Code.joinWords 128
                            225972207342586525224194221314865627136
                            225972207345681413101339581138763513856))
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            225971355431864965816684978270166319104
                            225972207332683004906884760168227143680)
                          (Code.joinWords 128
                            225972207342586525224194221317013110784
                            225972207345681413101339581140910997504))
                        512)
                      1024))
                  4096)))
            32768)
          65536)
        131072)
      262144)
    (Code.joinWords 262144
      (Code.joinWords 131072
        (Nat.shiftLeft
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      170141183460469231731687303715884105728
                      128)
                    256)
                  512)
                1024)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128)
                          256)
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128)
                          (Nat.shiftLeft
                            85070591750041656499021422275829170176
                            128))
                        512)
                      1024)))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85070591750041656494409736256328040448
                            128)
                          256)
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85070591730234615870455337876369440768
                            128)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128)
                          (Nat.shiftLeft
                            85070591750041656499021422275829170176
                            128))
                        512)
                      1024)))))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          170141183460469231731687303715884105728
                          170141183460469231731687303715884105728)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          170141183460469231731687303715884105728
                          170141183460469231731687303715884105728)
                        256))
                    2048)
                  4096)
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85070591750041656494409736256328040448
                            128)
                          256)
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85070591730234615870455337876369440768
                            128)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128)
                          (Nat.shiftLeft
                            85070591750041656499021422275829170176
                            128))
                        512)
                      1024)))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85070591750041656494409736256328040448
                            128)
                          256)
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85070591730234615870455337876369440768
                            128)
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            181481159839123376538753448534675030016
                            181481159839278119044240581821340844032)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            181481159839278119044240581821340844032
                            181481159839278119044240581821340844032)
                          256))
                      (Code.joinWords 512
                        41538374868278621028243970633760768
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128)
                          (Nat.shiftLeft
                            85070591750041656499021422275829170176
                            128)))))))))
          65536)
        (Nat.shiftLeft
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128)
                          256)
                        512)
                      1024)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128)
                          256)
                        512)
                      1024))
                  4096))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128)
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128))
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128)
                          (Nat.shiftLeft
                            85070591750041656499021422275829170176
                            128))
                        512)
                      1024)))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85070591750041656494409736256328040448
                            128)
                          (Nat.shiftLeft
                            85070591750041656499021422274755428352
                            128))
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85070591750041656494409736256328040448
                            128)
                          (Nat.shiftLeft
                            85070591750041656499021422274755428352
                            128))
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85070591750041656494409736256328040448
                            128)
                          (Nat.shiftLeft
                            85070591750041656499021422274755428352
                            128))
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85070591750041656494409736256328040448
                            128)
                          (Nat.shiftLeft
                            85070591750041656499021422275829170176
                            128))
                        512)
                      1024)))))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128)
                          256)
                        512)
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128)
                          256)
                        512)
                      1024)
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128)
                          256)
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128)
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            170805797458361689668139207246024278016
                            181481159841763670519568426613231058944)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            170805797458361689668139207246024278016
                            181481159841763670519568426613231058944)
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85070591750041656494409736256328040448
                            128)
                          256)
                        512)))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85070591730234615870455337876369440768
                            128)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128)
                          (Nat.shiftLeft
                            85070591750041656499021422274755428352
                            128))
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85070591730234615870455337876369440768
                            128)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128)
                          (Nat.shiftLeft
                            85070591750041656499021422275829170176
                            128))
                        512)
                      1024)))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85070591750041656494409736256328040448
                            128)
                          (Nat.shiftLeft
                            85070591750041656499021422274755428352
                            128))
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85070591750041656494409736256328040448
                            128)
                          (Nat.shiftLeft
                            85070591750041656499021422274755428352
                            128))
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85070591750041656494409736256328040448
                            128)
                          (Nat.shiftLeft
                            85070591750041656499021422274755428352
                            128))
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            170141183460469231731687303715884105728
                            180775007426748558714917760198126862336)
                          (Code.joinWords 128
                            181481159839123376538753448534675030016
                            181481159841763670529406540001369391104))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            170805797458361689668139207246024278016
                            181481159839123376529530076495672770560)
                          (Code.joinWords 128
                            181481159839278119044278862418173493248
                            181481159841763670529406540001369391104)))
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85070591750041656494409736256328040448
                            128)
                          (Nat.shiftLeft
                            85070591750041656499021422275829170176
                            128))
                        512)))))))
          65536))
      (Code.joinWords 131072
        (Nat.shiftLeft
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128)
                          256)
                        512)
                      1024)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128)
                          256)
                        512)
                      1024))
                  4096))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128)
                          256)
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128)
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128))
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128)
                          (Nat.shiftLeft
                            85070591750041656499021422275829170176
                            128))
                        512)
                      1024)))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85070591750041656494409736256328040448
                            128)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85070591750041656494409736256328040448
                            128)
                          256)
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128)
                          (Nat.shiftLeft
                            85070591750041656499021422274755428352
                            128))
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128)
                          (Nat.shiftLeft
                            85070591750041656499021422275829170176
                            128))
                        512)
                      1024)))))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128)
                          256)
                        512)
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128)
                          256)
                        512)
                      1024)
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128)
                          256)
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128)
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            180775007426748558714917760198126862336
                            180775007426748558714917760198126862336)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            181481159799509295282236021084891643904
                            181481159799509295282236021084891643904)
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85070591730234615870455337876369440768
                            128)
                          256)
                        512)))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85070591730234615870455337876369440768
                            128)
                          (Nat.shiftLeft
                            85070591750041656499021422274755428352
                            128))
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85070591730234615870455337876369440768
                            128)
                          (Nat.shiftLeft
                            85070591750041656499021422274755428352
                            128))
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85070591730234615870455337876369440768
                            128)
                          (Nat.shiftLeft
                            85070591750041656499021422274755428352
                            128))
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85070591730234615870455337876369440768
                            128)
                          (Nat.shiftLeft
                            85070591750041656499021422275829170176
                            128))
                        512)
                      1024)))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85070591730234615870455337876369440768
                            128)
                          (Nat.shiftLeft
                            85070591750041656499021422274755428352
                            128))
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85070591730234615870455337876369440768
                            128)
                          (Nat.shiftLeft
                            85070591750041656499021422274755428352
                            128))
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85070591730234615870455337876369440768
                            128)
                          (Nat.shiftLeft
                            85070591750041656499021422274755428352
                            128))
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            170141183460469231731687303715884105728
                            180775007426748558714917760198126862336)
                          (Code.joinWords 128
                            181481159839123376538753448534675030016
                            181481159841763670529368259404536741888))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            170805797458361689668139207246024278016
                            181481159799509295281621279735755571200)
                          (Code.joinWords 128
                            181481159841763670529406540001369391104
                            181481159841763670529406540001369391104)))
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85070591730234615870455337876369440768
                            128)
                          (Nat.shiftLeft
                            85070591750041656499021422275829170176
                            128))
                        512)))))))
          65536)
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170143779608898499145501568964048715776
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170143779608898499145501568964048715776
                            128)
                          256))
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            213509853162297211027377037943238557696
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            213509853162297211027377037943238557696
                            128)
                          256))
                      1024)
                    2048))
                8192)
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            212679075513630492798465371004379070464
                            128)
                          (Nat.shiftLeft
                            213510504724764126859688504230489882624
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            212679724550737809651918937316420222976
                            128)
                          (Nat.shiftLeft
                            213510504724764129220871745665312489472
                            128)))
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            213509843010996065219030250417054285824
                            128)
                          (Nat.shiftLeft
                            213510504734706332811728570346830299136
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            213510504724609384354777831696127492096
                            128)
                          (Nat.shiftLeft
                            213510504734706335172956848329829908480
                            128)))
                      1024)
                    2048))
                8192))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            212679724511123123931876961205060894720
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            213510504684994698634735855584768163840
                            128)
                          (Nat.shiftLeft
                            213510504684994698634735855584768163840
                            128)))
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            213510504734705728337289407248686120960
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            213510504724608779901091396420542398464
                            128)
                          (Nat.shiftLeft
                            213510504734705728348854651093921038336
                            128)))
                      1024)
                    2048))
                8192)
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            212679075513630492798465371004379070464
                            128)
                          (Nat.shiftLeft
                            213510504734706332811728570346830299136
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            213510504724609384364001203732982267904
                            128)
                          (Nat.shiftLeft
                            213510504734706486878980110515034914816
                            128)))
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            213509843010996065219030250417054285824
                            128)
                          (Nat.shiftLeft
                            213510504734706332811728570348977782784
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            213510504724609384364001344472618106880
                            128)
                          (Nat.shiftLeft
                            213510504734706486878980110517182398464
                            128)))
                      1024)
                    2048))
                8192)))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128)
                          256)
                        512)
                      1024)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85070591750041656494409736256328040448
                            128)
                          256)
                        512)
                      1024))
                  4096))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128)
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128))
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128)
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128))
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128)
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128))
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128)
                          (Nat.shiftLeft
                            85070591750041656499021422275829170176
                            128))
                        512)
                      1024)))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85070591750041656494409736256328040448
                            128)
                          (Nat.shiftLeft
                            85070591750041656499021422274755428352
                            128))
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            137438953472
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85070591750041656494409736256328040448
                            128)
                          (Nat.shiftLeft
                            85070591750041656499021422274755428352
                            128)))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85070591750041656494409736256328040448
                            128)
                          (Nat.shiftLeft
                            85070591750041656499021422274755428352
                            128))
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85070591750041656494409736256328040448
                            128)
                          (Nat.shiftLeft
                            85070591750041656499021422275829170176
                            128))
                        512)
                      1024)))))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128)
                          256)
                        512)
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85070591730234615870455337876369440768
                            128)
                          256)
                        512)
                      1024)
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128)
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128))
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128)
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128))
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            181481159799509295272397907698900795392
                            181481159841763670519568426613231058944)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            181439621464255097917725204564041269248
                            128)
                          (Code.joinWords 128
                            181481159799509295282236021084891643904
                            181481159841763670529406540001369391104)))
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85070591750041656499021422275829170176
                            128)
                          (Nat.shiftLeft
                            85070591750041656499021422275829170176
                            128))
                        512)))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85070591730234615870455337876369440768
                            128)
                          (Nat.shiftLeft
                            85070591750041656499021422274755428352
                            128))
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85070591730234615870455337876369440768
                            128)
                          (Nat.shiftLeft
                            85070591750041656499021422274755428352
                            128))
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85070591730234615870455337876369440768
                            128)
                          (Code.joinWords 128
                            9444732965739290427392
                            85070591750041656499021422274755428352))
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85070591730234615870455337876369440768
                            128)
                          (Nat.shiftLeft
                            85070591750041656499021422275829170176
                            128))
                        512)
                      1024)))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85070591750041656499021422274755428352
                            128)
                          (Nat.shiftLeft
                            85070591750041656499021422274755428352
                            128))
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85070591750041656499021422274755428352
                            128)
                          (Nat.shiftLeft
                            85070591750041656499021422274755428352
                            128))
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85070591750041656499021422274755428352
                            128)
                          (Nat.shiftLeft
                            85070591750041656499021422274755428352
                            128))
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            170141183460469231731687303715884105728
                            180775007466362639972049928994898837504)
                          (Code.joinWords 128
                            181481159839123376538753448534675030016
                            181481159841763670529406540001369391104))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            170805797458361689677362579282879053824
                            181481159839123376538753448534675030016)
                          (Code.joinWords 128
                            181481159841763670529406540001369391104
                            181481159841763670529406540001369391104)))
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85070591750041656499021422275829170176
                            128)
                          (Nat.shiftLeft
                            85070591750041656499021422275829170176
                            128))
                        512)))))))))))

/-- The block word is computed from the verified profile data. -/
theorem word_eq :
    Code.profileWord 64 24 (fun i q => Data.profiles (2560 + i) q) = word := by
  decide +kernel

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage040
