/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Cslib.Foundations.RelationAlgebra.FastCatalogueCoverage

/-!
# Profile coverage for models 1153–1216 of the ⟨1, 4, 0⟩ row

The balanced word contains exactly the cycle profiles of this block and its atom renamings.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage018

/-- The cycle profiles covered by this block of models. -/
def word : ℕ :=
  (Code.joinWords 524288
    (Code.joinWords 262144
      (Nat.shiftLeft
        (Code.joinWords 65536
          (Nat.shiftLeft
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            319845486485745381917478573879957962944
                            333189689412179888922801949446053609664)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            319849390849594084864035183725830471680
                            333193756669130721196836651618288009216)
                          256)
                        512)
                      1024))
                  (Code.joinWords 1024
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          3713820117856140824898699264
                          128)
                        (Code.joinWords 128
                          320177793484691610885704525645027999744
                          333521996411126117891027901211123646464))
                      512)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        1237940039285380274966233088
                        128)
                      512)))
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316911983139663491615228241121509376
                            128)
                          (Nat.shiftLeft
                            4951760157159535498105978880
                            128))
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            6189309760042031079839960135412875264
                            128)
                          (Nat.shiftLeft
                            274877906944
                            128))
                        512))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            6189309760042031079839960135412875264
                            128)
                          (Nat.shiftLeft
                            4951760157141521099596496896
                            128))
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            6189309760042031079839960135412875264
                            128)
                          (Nat.shiftLeft
                            274877906944
                            128))
                        512))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          6189309760042031079839960135412744192
                          128)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316911983139663491615228241121509376
                            128)
                          (Code.joinWords 128
                            2332864606977916928
                            2476979795053772800))
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            6189309760042031079839960135412875264
                            128)
                          (Nat.shiftLeft
                            274877906944
                            128))
                        512)))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            6189309760042031079839960135412744192
                            128)
                          (Nat.shiftLeft
                            274877906944
                            128))
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            6189309760042031079839960135412875264
                            128)
                          303412046524374704979968)
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            6189309760042031079839960135412875264
                            128)
                          (Nat.shiftLeft
                            274877906944
                            128))
                        512))))))
            32768)
          (Nat.shiftLeft
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        64
                        64)
                      256)
                    512)
                  1024)
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            131072
                            128)
                          (Code.joinWords 128
                            4951760159474385706574413824
                            2476979795053772800))
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            274877906944
                            274877906944)
                          256)
                        512))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            4952063569188045474301476864
                            303412046524374704979968)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            274877906944
                            274877906944)
                          256)
                        512))
                    2048))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            131072
                            128)
                          (Code.joinWords 128
                            4951760159474385706574413824
                            2476979795053772800))
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            274877906944
                            274877906944)
                          256)
                        512))
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            274877906944
                            274877906944)
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          4951760157141521099596496896
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            274877906944
                            274877906944)
                          256)
                        512))))))
            32768))
        131072)
      (Code.joinWords 131072
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            332306998946228968225951765070217216
                            128)
                          (Nat.shiftLeft
                            1237940040438301779505971200
                            128))
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            13666293295368196558687964651682136064
                            128)
                          (Nat.shiftLeft
                            18889465931478580854784
                            128))
                        512))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            13666293295368196558687964651682136064
                            128)
                          (Nat.shiftLeft
                            1152921504606846976
                            128))
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            13666293295368196558687964651682136064
                            128)
                          (Nat.shiftLeft
                            18889465931478580854784
                            128))
                        512)))
                  4096)
                8192)
              16384)
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            332306998946228968225951765070086196224
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            333189689412179888922801949446053612544
                            128)
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            337623910929368631717566993311207522304
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            54043195541028864
                            128)
                          (Nat.shiftLeft
                            338506601395319552414417177687174938624
                            128)))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          18014398513676288
                          128)
                        512)))
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          332311055428149698560036554520343347200
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          333193756669130721196836651618288009216
                          128)
                        256))
                    1024))
                8192)
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          13666293295368196558687964651682004992
                          128)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            13666293295368196558687964651682004992
                            128)
                          (Nat.shiftLeft
                            18889465931478580854784
                            128))
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            11760430373211112611541680128
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            332306998946228968225951765070217216
                            128)
                          (Nat.shiftLeft
                            11799115999438780745132277760
                            128)))
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            13666293295368196558687964651682136064
                            128)
                          (Nat.shiftLeft
                            18889465931478580854784
                            128))
                        512))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            74766790688768
                            128)
                          256)
                        (Nat.shiftLeft
                          13666293295368196558687964651682136064
                          128))
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            13666293295368196558687964651682136064
                            128)
                          (Nat.shiftLeft
                            18889465931478580854784
                            128))
                        512))))
                8192)))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          59654145879203835120816488448
                          (Nat.shiftLeft
                            317243101849350145328672662683929018368
                            128))
                        512)
                      (Nat.shiftLeft
                        77372433046956984592498688
                        512))
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          298581742917035430897574270761344958464
                          317243101849350145328672662683929018368)
                        256)
                      512)
                    2048)
                  4096))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          1197957500880551936
                          1200209300694237184)
                        256)
                      512)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            332306998946228968225951765070086144
                            131072)
                          (Code.joinWords 128
                            1197957500880551936
                            1200209300694237184))
                        512)
                      (Nat.shiftLeft
                        332312069548629881143557751882907648
                        512))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            332306998946228968225951765070086144
                            131072)
                          (Code.joinWords 128
                            1197957500880551936
                            1200209300694237184))
                        512)
                      (Nat.shiftLeft
                        332312069548629881143557751882907648
                        512)))
                  4096)))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          74276402357122816493947453440
                          (Nat.shiftLeft
                            316356262996809977751106080346722009088
                            128))
                        (Code.joinWords 256
                          74276402357122816493947453440
                          (Nat.shiftLeft
                            317238953462760898447956264722689425408
                            128)))
                      24758800785707605497982484480)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        24758800785707605497982484480
                        5029434821643381741482672128)
                      (Code.joinWords 512
                        24758800785707605497982484480
                        77372433046956984592498688))
                    2048))
                (Code.joinWords 2048
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        17408
                        128)
                      256)
                    1024)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      18014398513676288
                      128)
                    512)))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2332864606977916928
                            2476979795053772800)
                          256)
                        512)
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            106339537737007903539211697446509871104
                            128)
                          (Code.joinWords 128
                            4611756387171565568
                            4899991161369788416))
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            274877906944
                            274877906944)
                          256)))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            106338239662793269832304564822427566080
                            128)
                          (Code.joinWords 128
                            70368744177664
                            74766790688768))
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            303412046524374704979968
                            128)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          106339537737007903539211697446509871104
                          128)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            274877906944
                            274877906944)
                          256)))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            106339537737007903539211697446509871104
                            106339537737007903539211697446509871104)
                          (Code.joinWords 128
                            4611686018427387904
                            4899916394579099648))
                        332312069548629881143557751882907648)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            4951760159474385706574413824
                            2476979795053772800)
                          256)
                        512)
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            106339537737007903539211697446509871104
                            106339537737007903539211697446509871104)
                          (Code.joinWords 128
                            4611756387171565568
                            4899991161369788416))
                        (Code.joinWords 256
                          332312069548629881143557751882907648
                          (Code.joinWords 128
                            274877906944
                            274877906944)))))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 128
                          106338239662793269832304564822427566080
                          106338239662793269832304564822427566080)
                        332306998946228968225951765070086144)
                      (Code.joinWords 512
                        (Code.joinWords 128
                          106339537737007903539211697446509871104
                          106339537737007903539211697446509871104)
                        (Code.joinWords 256
                          332312069548629881143557751882907648
                          (Code.joinWords 128
                            274877906944
                            274877906944))))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            106338239662793269832304564822427566080
                            106338239662793269832304564822427566080)
                          (Code.joinWords 128
                            70368744177664
                            74766790688768))
                        (Code.joinWords 256
                          332306998946228968225951765070086144
                          4951760157141521099596496896))
                      (Code.joinWords 512
                        (Code.joinWords 128
                          106339537737007903539211697446509871104
                          106339537737007903539211697446509871104)
                        (Code.joinWords 256
                          332312069548629881143557751882907648
                          (Code.joinWords 128
                            274877906944
                            274877906944))))))))))
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 256
                      (Nat.shiftLeft
                        805306368
                        128)
                      (Nat.shiftLeft
                        317575413918898775209816220436617232384
                        128))
                    512)
                  2048)
                4096)
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            131072
                            128)
                          (Code.joinWords 128
                            1197957500880551936
                            1237940040485589575593361408))
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            19884715293067945040272162816
                            18889465931478580854784)
                          256)
                        512))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            131072
                            128)
                          (Code.joinWords 128
                            303413244481875585531904
                            1200209300694237184))
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            18889465931478580854784
                            128)
                          256)
                        512)))
                  4096)
                8192))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          17408
                          128)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          16448
                          1088)
                        256))
                    1024)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      16384
                      16384)
                    2048))
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            8046610255354971786844307456
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            131072
                            128)
                          (Nat.shiftLeft
                            8056281661929903218751438848
                            128)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            4899991161369788416
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            274877906944
                            128)
                          256)))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            8046610255355046553634996224
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            131072
                            128)
                          (Nat.shiftLeft
                            8056281661911888820241956864
                            128)))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            274877906944
                            128)
                          256)
                        512))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          106339537737007903539211697446509871104
                          (Nat.shiftLeft
                            4899916394579099648
                            128))
                        (Nat.shiftLeft
                          19884411881021420665567182848
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        106338239662793269832304564822427566080
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            131072
                            128)
                          (Code.joinWords 128
                            2332864606977916928
                            2476979795053772800)))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          106339537737007903539211697446509871104
                          (Nat.shiftLeft
                            4899991161369788416
                            128))
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            18889465931753458761728
                            128)
                          256))))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          106338239662793269832304564822427566080
                          (Nat.shiftLeft
                            11760430373211112611541680128
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            131072
                            128)
                          (Nat.shiftLeft
                            11799115999438780745132277760
                            128)))
                      (Code.joinWords 512
                        106339537737007903539211697446509871104
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            19884715293067945040272162816
                            18889465931753458761728)
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          106338239662793269832304564822427582464
                          (Nat.shiftLeft
                            74766790688768
                            128))
                        (Nat.shiftLeft
                          303412046524374704979968
                          256))
                      (Code.joinWords 512
                        106339537737007903539211697446509887488
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            18889465931753458761728
                            128)
                          256))))))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 256
                      (Nat.shiftLeft
                        268435456
                        128)
                      (Nat.shiftLeft
                        268435456
                        128))
                    512)
                  2048)
                4096)
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          332306998946228968225951765070086144
                          (Code.joinWords 128
                            1197957500880551936
                            1200209300694237184))
                        512)
                      (Nat.shiftLeft
                        332312069548629881143557751882907648
                        512))
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            332306998946228968225951765070086144
                            131072)
                          (Code.joinWords 128
                            1197957500880551936
                            1200209300694237184))
                        512)
                      (Nat.shiftLeft
                        332312069548629881143557751882907648
                        512))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            332306998946228968225951765070086144
                            131072)
                          (Code.joinWords 128
                            1197957500880551936
                            1200209300694237184))
                        512)
                      (Nat.shiftLeft
                        332312069548629881143557751882907648
                        512)))
                  4096)))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Code.joinWords 512
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        297747071055821155530452781502797185024
                        316356262996809977751106080346722009088)
                      256)
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        298577838553186727951017660915472400384
                        317238953462760898447956264722689425408)
                      256))
                  2048)
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          17408
                          128)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          64
                          64)
                        256))
                    1024)
                  (Nat.shiftLeft
                    16384
                    2048)))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            131072
                            128)
                          (Code.joinWords 128
                            4951760159474385706574413824
                            2476979795053772800))
                        512)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            4611756387171565568
                            4899991161369788416)
                          256)
                        (Code.joinWords 256
                          332312069548629881143557751882907648
                          (Code.joinWords 128
                            274877906944
                            274877906944))))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            70368744177664
                            74766790688768)
                          256)
                        (Code.joinWords 256
                          332306998946228968225951765070086144
                          (Code.joinWords 128
                            4952063569188045474301476864
                            303412046524374704979968)))
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          332312069548629881143557751882907648
                          (Code.joinWords 128
                            274877906944
                            274877906944))
                        512))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            4611686018427387904
                            4899916394579099648)
                          256)
                        332312069548629881143557751882907648)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            131072
                            128)
                          (Code.joinWords 128
                            4951760159474385706574413824
                            2476979795053772800))
                        512)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            4611756387171565568
                            4899991161369788416)
                          256)
                        (Code.joinWords 256
                          332312069548629881143557751882907648
                          (Code.joinWords 128
                            274877906944
                            274877906944)))))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        332306998946228968225951765070086144
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          332312069548629881143557751882907648
                          (Code.joinWords 128
                            274877906944
                            274877906944))
                        512))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          16384
                          (Code.joinWords 128
                            70368744177664
                            74766790688768))
                        (Code.joinWords 256
                          332306998946228968225951765070086144
                          4951760157141521099596496896))
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          332312069548629881143557751882907648
                          (Code.joinWords 128
                            274877906944
                            274877906944))
                        512))))))))))
    (Code.joinWords 262144
      (Nat.shiftLeft
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          14699973484109365248
                          128)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            312258420806120697111519296405685403648
                            128)
                          256))
                      (Nat.shiftLeft
                        288234774198222848
                        128))
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 128
                          17293822569102704640
                          17293822569102704640)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            298910145552132956919243612680542486528
                            312254348478567463924566988246638133248)
                          256))
                      5764607523034234880)
                    (Code.joinWords 1024
                      (Code.joinWords 128
                        5764607523034234880
                        1441226647549247488)
                      (Code.joinWords 128
                        5764607523034234880
                        288234774198222848)))
                  4096))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          8046610255354971786844307456
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          8056281661911888820241956864
                          128)
                        256))
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            11760430373211112611541680128
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            11799115999438780745132277760
                            128)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            19807342860020988055679664128
                            18889465931478580854784)
                          256)
                        (Code.joinWords 256
                          106339537737007903539211697446509871104
                          (Code.joinWords 128
                            19884715293067945040272162816
                            18889465931478580854784))))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          302231454903657293676544
                          256)
                        (Code.joinWords 256
                          106338239662793269832304564822427566080
                          (Code.joinWords 128
                            303412046524374704979968
                            74766790688768)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            18889465931478580854784
                            128)
                          256)
                        (Code.joinWords 256
                          106339537737007903539211697446509871104
                          (Nat.shiftLeft
                            18889465931478580854784
                            128)))))
                  4096)))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          311043407495591044593575641555857833984
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          312258420806120697111519296405685403648
                          128)
                        256))
                    2048)
                  4096)
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        16448
                        256)
                      512)
                    1024)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      1237940039285380274966233088
                      128)
                    512)))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316911983139663491615228241121378304
                            128)
                          (Nat.shiftLeft
                            8046610255354971786844307456
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            131072
                            128)
                          (Nat.shiftLeft
                            8056281661911888820241956864
                            128)))
                      (Nat.shiftLeft
                        5316993112778078098296924030126522368
                        128))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316911983139663491615228241121378304
                            128)
                          (Nat.shiftLeft
                            8046610255354971786844307456
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            131072
                            128)
                          (Nat.shiftLeft
                            8056281661911888820241956864
                            128)))
                      (Nat.shiftLeft
                        5316993112778078098296924030126522368
                        128))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            106339537737007903539211697446509871104
                            5316993112778078098296924030126522368)
                          19807040628566084398385987584)
                        (Code.joinWords 256
                          106339537737007903539211697446509871104
                          19884411881021420665567182848))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 128
                          106338239662793269832304564822427566080
                          5316911983139663491615228241121378304)
                        106338239662793269832304564822427566080)
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            106339537737007903539211697446509871104
                            5316993112778078098296924030126522368)
                          (Nat.shiftLeft
                            18889465931478580854784
                            128))
                        (Code.joinWords 256
                          106339537737007903539211697446509871104
                          (Nat.shiftLeft
                            18889465931478580854784
                            128)))))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            11760430374364034116148527104
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            11799115999438780745132277760
                            128)
                          256))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            106339537737007903539211697446509871104
                            5316993112778078098296924030126522368)
                          (Code.joinWords 128
                            19807342860020988055679664128
                            18889465931478580854784))
                        (Code.joinWords 256
                          106339537737007903539211697446509871104
                          (Code.joinWords 128
                            19884715293067945040272162816
                            18889465931478580854784))))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            106338239662793269832304564822427566080
                            5316911983139663491615228241121378304)
                          (Code.joinWords 128
                            302231454903657293676544
                            1152921504606846976))
                        (Code.joinWords 256
                          106338239662793269832304564822427566080
                          303412046524374704979968))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            106339537737007903539211697446509871104
                            5316993112778078098296924030126522368)
                          (Nat.shiftLeft
                            18889465931478580854784
                            128))
                        (Code.joinWords 256
                          106339537737007903539211697446509871104
                          (Nat.shiftLeft
                            18889465931478580854784
                            128)))))))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      74766790688768
                      128)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 128
                      1152921504606846976
                      1152921504606846976)
                    (Code.joinWords 128
                      1152921504606846976
                      1152996271397535744))
                  4096))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          4952062388596424756890173440
                          302231454903657293676544)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          4952063569188115843045654528
                          303412046599141495668736)
                        256))
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        4951760157141521099596496896
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          4951760157141591468340674560
                          74766790688768)
                        256))
                    2048)
                  4096)))
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        4951760157141521099596496896
                        256)
                      (Nat.shiftLeft
                        4951760157141521099596496896
                        256))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          4952062389749346261497020416
                          302232607825161900523520)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          4952063569188045474301476864
                          303412046524374704979968)
                        256))
                    2048))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        4951760157141521099596496896
                        256)
                      (Nat.shiftLeft
                        4951760157141521099596496896
                        256))
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        1152921504606846976
                        1152921504606846976)
                      256)
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          4951760158294442604203343872
                          1152921504606846976)
                        256)
                      (Nat.shiftLeft
                        4951760157141521099596496896
                        256)))))
              16384)))
        131072)
      (Code.joinWords 131072
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            11760430374364034116148527104
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            131072
                            128)
                          (Nat.shiftLeft
                            11799115999438780745132277760
                            128)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            18889465931478580854784
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            18889465931478580854784
                            128)
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1152996271397535744
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            74766790688768
                            128)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            18889465931478580854784
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            18889465931478580854784
                            128)
                          256))))
                  4096)
                8192)
              16384)
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 512
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        1024
                        128)
                      256)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        1024
                        128)
                      256))
                  1024)
                8192)
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            18889465931478580854784
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            18889465931478580854784
                            128)
                          256))
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            11760430374364034116148527104
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            131072
                            128)
                          (Nat.shiftLeft
                            11799115999438780745132277760
                            128)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            18889465931478580854784
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            18889465931478580854784
                            128)
                          256)))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1152921504606846976
                          128)
                        256)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            18889465931478580854784
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            18889465931478580854784
                            128)
                          256)))))
                8192)))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    303412046524374704979968
                    512)
                  2048)
                4096)
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          1152991873351024640
                          302232607899928691212288)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          70368744177664
                          303412046599141495668736)
                        256))
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        1152921504606846976
                        1152921504606846976)
                      256)
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          4951760158294512972947521536
                          1152996271397535744)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          4951760157141591468340674560
                          74766790688768)
                        256)))
                  4096)))
            (Code.joinWords 16384
              (Code.joinWords 4096
                (Nat.shiftLeft
                  (Code.joinWords 512
                    4951760157141521099596496896
                    4951760157141521099596496896)
                  2048)
                (Nat.shiftLeft
                  (Code.joinWords 512
                    4951760157141521099596496896
                    4952063569188045474301476864)
                  2048))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          1152921504606846976
                          302232607825161900523520)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          303412046524374704979968
                          128)
                        256))
                    2048)
                  4096)
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        4951760157141521099596496896
                        256)
                      (Nat.shiftLeft
                        4951760157141521099596496896
                        256))
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        1152921504606846976
                        1152921504606846976)
                      256)
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          4951760158294442604203343872
                          1152921504606846976)
                        256)
                      (Nat.shiftLeft
                        4951760157141521099596496896
                        256))))))))
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          268435456
                          128)
                        (Nat.shiftLeft
                          268435456
                          128))
                      512)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 512
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        297747071055821155530452781502797185024
                        311039351013670314259490852105600630784)
                      256)
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        298910145552132956919243612680542486528
                        312254348478567463924566988246638133248)
                      256))
                  4096))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316911983139663491615228241121378304
                            128)
                          (Nat.shiftLeft
                            8046610255354971786844307456
                            128))
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            8056281661911888820241956864
                            128)
                          256))
                      (Nat.shiftLeft
                        5316993112778078098296924030126522368
                        128))
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            11760430374364034116148527104
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            131072
                            128)
                          (Nat.shiftLeft
                            11799115999438780745132277760
                            128)))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316993112778078098296924030126522368
                            128)
                          (Code.joinWords 128
                            19807342860020988055679664128
                            18889465931478580854784))
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            19884715293067945040272162816
                            18889465931478580854784)
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316911983139663491615228241121378304
                            128)
                          (Code.joinWords 128
                            302231454903657293676544
                            1152996271397535744))
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            303412046524374704979968
                            74766790688768)
                          256))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316993112778078098296924030126522368
                            128)
                          (Nat.shiftLeft
                            18889465931478580854784
                            128))
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            18889465931478580854784
                            128)
                          256))))
                  4096)))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1024
                          128)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          16448
                          1024)
                        256))
                    1024)
                  (Nat.shiftLeft
                    16384
                    2048))
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316911983139663491615228241121378304
                            128)
                          (Nat.shiftLeft
                            8046610255354971786844307456
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            131072
                            128)
                          (Nat.shiftLeft
                            8056281661911888820241956864
                            128)))
                      (Nat.shiftLeft
                        5316993112778078098296924030126522368
                        128))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316911983139663491615228241121378304
                            128)
                          (Nat.shiftLeft
                            8046610255354971786844307456
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            131072
                            128)
                          (Nat.shiftLeft
                            8056281661911888820241956864
                            128)))
                      (Nat.shiftLeft
                        5316993112778078098296924030126522368
                        128))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316993112778078098296924030126522368
                            128)
                          19807040628566084398385987584)
                        (Nat.shiftLeft
                          19884411881021420665567182848
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        5316911983139663491615228241121378304
                        128)
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316993112778078098296924030126522368
                            128)
                          (Nat.shiftLeft
                            18889465931478580854784
                            128))
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            18889465931478580854784
                            128)
                          256))))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            11760430374364034116148527104
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            131072
                            128)
                          (Nat.shiftLeft
                            11799115999438780745132277760
                            128)))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316993112778078098296924030126522368
                            128)
                          (Code.joinWords 128
                            19807342860020988055679664128
                            18889465931478580854784))
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            19884715293067945040272162816
                            18889465931478580854784)
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            16384
                            5316911983139663491615228241121378304)
                          (Code.joinWords 128
                            302231454903657293676544
                            1152921504606846976))
                        (Nat.shiftLeft
                          303412046524374704979968
                          256))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316993112778078098296924030126522368
                            128)
                          (Nat.shiftLeft
                            18889465931478580854784
                            128))
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            18889465931478580854784
                            128)
                          256))))))))
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          4952062389749416630241198080
                          302232607899928691212288)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          4952063569188115843045654528
                          303412046599141495668736)
                        256))
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        1152921504606846976
                        1152921504606846976)
                      256)
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          4951760158294512972947521536
                          1152996271397535744)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          4951760157141591468340674560
                          74766790688768)
                        256)))
                  4096))
              16384)
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        4951760157141521099596496896
                        256)
                      (Nat.shiftLeft
                        4951760157141521099596496896
                        256))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          4952062389749346261497020416
                          302232607825161900523520)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          4952063569188045474301476864
                          303412046524374704979968)
                        256))
                    2048))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        4951760157141521099596496896
                        256)
                      (Nat.shiftLeft
                        4951760157141521099596496896
                        256))
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        1152921504606846976
                        1152921504606846976)
                      256)
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          4951760158294442604203343872
                          1152921504606846976)
                        256)
                      (Nat.shiftLeft
                        4951760157141521099596496896
                        256)))))
              16384))))))

/-- The block word is computed from the verified profile data. -/
theorem word_eq :
    Code.profileWord 64 24 (fun i q => Data.profiles (1152 + i) q) = word := by
  decide +kernel

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage018
