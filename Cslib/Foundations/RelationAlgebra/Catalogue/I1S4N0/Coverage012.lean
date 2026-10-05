/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Cslib.Foundations.RelationAlgebra.FastCatalogueCoverage

/-!
# Profile coverage for models 769–832 of the ⟨1, 4, 0⟩ row

The balanced word contains exactly the cycle profiles of this block and its atom renamings.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage012

/-- The cycle profiles covered by this block of models. -/
def word : ℕ :=
  (Code.joinWords 524288
    (Code.joinWords 262144
      (Code.joinWords 131072
        (Nat.shiftLeft
          (Nat.shiftLeft
            (Nat.shiftLeft
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            311043407495591044602799013592712609792
                            128)
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            311039351082994956475613048567668670464
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            311043407564916593504639220848342859776
                            128)
                          256)
                        512)))
                  4096)
                8192)
              16384)
            32768)
          65536)
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 8192
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 1024
                    (Code.joinWords 512
                      (Code.joinWords 128
                        4026580992
                        14699973484965003264)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          50528256
                          128)
                        (Code.joinWords 128
                          808452096
                          256212605621993638361683026702530248704)))
                    (Code.joinWords 512
                      (Code.joinWords 128
                        4026580992
                        288234775053860864)
                      (Nat.shiftLeft
                        65536
                        128)))
                  2048)
                4096)
              (Nat.shiftLeft
                (Code.joinWords 2048
                  (Code.joinWords 1024
                    (Code.joinWords 512
                      (Code.joinWords 128
                        17293822569102753792
                        17293822569354415104)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          3728384117450239695101558784
                          128)
                        (Code.joinWords 128
                          256208696187542534502208810869036417024
                          256208696187542534502208810869036417024)))
                    (Code.joinWords 512
                      (Code.joinWords 128
                        5764607523034284032
                        83887104)
                      (Nat.shiftLeft
                        4835777065434811537096704
                        128)))
                  (Code.joinWords 1024
                    (Code.joinWords 512
                      (Code.joinWords 128
                        5764607523034284032
                        1441226647566024704)
                      (Nat.shiftLeft
                        65536
                        128))
                    (Code.joinWords 512
                      (Code.joinWords 128
                        5764607523034284032
                        288234774215000064)
                      (Nat.shiftLeft
                        65536
                        128))))
                4096))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Code.joinWords 1024
                    (Code.joinWords 512
                      (Code.joinWords 128
                        49152
                        4642275147320176030871768064)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          4642275147320176030872701964
                          128)
                        (Code.joinWords 128
                          319014718988379809496913694467282747584
                          319014718988379809496913694467282747584)))
                    (Code.joinWords 512
                      (Code.joinWords 128
                        16384
                        1547425049106725343623906304)
                      (Nat.shiftLeft
                        327684
                        128)))
                  (Code.joinWords 1024
                    (Code.joinWords 512
                      (Code.joinWords 128
                        16384
                        1547425049106725343623906304)
                      (Nat.shiftLeft
                        314339676352711358842732544
                        128))
                    (Code.joinWords 512
                      (Code.joinWords 128
                        16384
                        1547425049106725343623906304)
                      (Nat.shiftLeft
                        4835777065434811537096704
                        128))))
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 128
                          16384
                          5316911983139663491615228241121378304)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            65536
                            128)
                          (Code.joinWords 128
                            4951760157141521099596496896
                            274877906944)))
                      (Code.joinWords 512
                        (Code.joinWords 128
                          16384
                          5316911983139663491615228241121378304)
                        (Nat.shiftLeft
                          65536
                          128)))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 128
                          16384
                          5316911983139663491615228241121378304)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            20769504346789367571472359492747264
                            128)
                          4952063569188045474301476864))
                      (Code.joinWords 512
                        (Code.joinWords 128
                          16384
                          5316911983139663491615228241121378304)
                        (Nat.shiftLeft
                          20769504346789367571472359492747264
                          128)))
                    2048))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 128
                          106338239662793269832304564822427582464
                          5316911983139663491615228241121378304)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            65536
                            128)
                          (Code.joinWords 128
                            4503599627370496
                            4503874505277440)))
                      (Code.joinWords 512
                        (Code.joinWords 128
                          106338239662793269832304564822427582464
                          5316911983139663491615228241121378304)
                        (Nat.shiftLeft
                          65536
                          128)))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 128
                          106338239662793269832304564822427582464
                          5316911983139663491615228241121378304)
                        (Nat.shiftLeft
                          20769504346789367571472359492747264
                          128))
                      (Code.joinWords 512
                        (Code.joinWords 128
                          106338239662793269832304564822427582464
                          5316911983139663491615228241121378304)
                        (Nat.shiftLeft
                          20769504346789367571472359492747264
                          128)))
                    2048)))))
          (Code.joinWords 32768
            (Code.joinWords 8192
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 1024
                    (Code.joinWords 512
                      (Code.joinWords 128
                        268484608
                        74767075901440)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          65536
                          128)
                        (Code.joinWords 128
                          1048576
                          1048576)))
                    (Code.joinWords 512
                      (Code.joinWords 128
                        268435456
                        285212672)
                      (Nat.shiftLeft
                        65536
                        128)))
                  2048)
                4096)
              (Nat.shiftLeft
                (Code.joinWords 2048
                  (Code.joinWords 1024
                    (Code.joinWords 512
                      (Code.joinWords 128
                        1152921504606896128
                        1152921504858557440)
                      (Nat.shiftLeft
                        65536
                        128))
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        83887104
                        128)
                      (Nat.shiftLeft
                        65536
                        128)))
                  (Code.joinWords 1024
                    (Code.joinWords 512
                      (Code.joinWords 128
                        1152921504606896128
                        1152996271414312960)
                      (Nat.shiftLeft
                        65536
                        128))
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        16777216
                        128)
                      (Nat.shiftLeft
                        65536
                        128))))
                4096))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Code.joinWords 1024
                    (Code.joinWords 512
                      (Code.joinWords 128
                        49152
                        52224)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          68620
                          128)
                        (Code.joinWords 128
                          64
                          64)))
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        65536
                        128)
                      512))
                  (Code.joinWords 1024
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        65536
                        128)
                      512)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        65536
                        128)
                      512)))
                8192)
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Code.joinWords 512
                    16384
                    (Code.joinWords 256
                      (Nat.shiftLeft
                        65536
                        128)
                      (Nat.shiftLeft
                        274877906944
                        128)))
                  2048)
                (Nat.shiftLeft
                  (Code.joinWords 512
                    16384
                    (Code.joinWords 256
                      (Nat.shiftLeft
                        65536
                        128)
                      (Code.joinWords 128
                        4503599627370496
                        4503874505277440)))
                  2048))))))
      (Code.joinWords 131072
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 1024
                    (Code.joinWords 512
                      (Code.joinWords 256
                        4026580992
                        (Nat.shiftLeft
                          855638016
                          128))
                      (Code.joinWords 256
                        (Code.joinWords 128
                          59654145879203835121624940544
                          3342336)
                        (Nat.shiftLeft
                          271166648751681983013143125537308278784
                          128)))
                    (Code.joinWords 512
                      4026580992
                      (Code.joinWords 128
                        77372433046956985400950784
                        65536)))
                  2048)
                4096)
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          16384
                          (Nat.shiftLeft
                            1152921504606846976
                            128))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            332306998946228968225951765070086144
                            65536)
                          (Nat.shiftLeft
                            18889465931478580854784
                            128)))
                      (Code.joinWords 512
                        16384
                        (Code.joinWords 128
                          332306998946228968225951765070086144
                          65536)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          16384
                          (Nat.shiftLeft
                            1152996271397535744
                            128))
                        (Code.joinWords 128
                          332306998946228968225951765070086144
                          20769504346789367571472359492747264))
                      (Code.joinWords 512
                        16384
                        (Code.joinWords 128
                          332306998946228968225951765070086144
                          20769504346789367571472359492747264))))
                  4096)
                8192))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          74276402357122816493947502592
                          (Nat.shiftLeft
                            271162511140122838072376640297190293504
                            128))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            74276402357122816493963231424
                            57421771425644544)
                          (Nat.shiftLeft
                            271162511140122838072376640297190293504
                            128)))
                      (Code.joinWords 512
                        24758800785707605497982533632
                        (Code.joinWords 128
                          5242944
                          1125917086777344)))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        24758800785707605497982533632
                        (Code.joinWords 128
                          5029434821643381741483720704
                          65536))
                      (Code.joinWords 512
                        24758800785707605497982533632
                        (Code.joinWords 128
                          77372433046956984593547264
                          65536)))
                    2048))
                (Code.joinWords 2048
                  (Code.joinWords 1024
                    (Code.joinWords 512
                      (Code.joinWords 256
                        49152
                        (Nat.shiftLeft
                          319014718988379809496913694467282750464
                          128))
                      (Code.joinWords 256
                        (Code.joinWords 128
                          67553994410606784
                          67553994411540684)
                        (Nat.shiftLeft
                          319014718988379809496913694467282750464
                          128)))
                    (Code.joinWords 512
                      16384
                      (Code.joinWords 128
                        22517998136852544
                        327684)))
                  (Code.joinWords 1024
                    (Code.joinWords 512
                      16384
                      (Code.joinWords 128
                        22517998136852544
                        5629791592054784))
                    (Code.joinWords 512
                      16384
                      (Code.joinWords 128
                        22517998136852544
                        1125917086777344)))))
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          106338239662793269832304564822427582464
                          (Nat.shiftLeft
                            309485009821345068724781056
                            128))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            332306998946228968225951765070086144
                            65536)
                          (Nat.shiftLeft
                            309503899287276547305635840
                            128)))
                      (Code.joinWords 512
                        106338239662793269832304564822427582464
                        (Code.joinWords 128
                          332306998946228968225951765070086144
                          65536)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        106338239662793269832304564822427582464
                        (Code.joinWords 128
                          332306998946228968225951765070086144
                          20769504346789367571472359492747264))
                      (Code.joinWords 512
                        106338239662793269832304564822427582464
                        (Code.joinWords 128
                          332306998946228968225951765070086144
                          20769504346789367571472359492747264))))
                  4096)
                8192)))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 1024
                    (Code.joinWords 512
                      (Code.joinWords 256
                        268451840
                        (Nat.shiftLeft
                          285212672
                          128))
                      (Code.joinWords 128
                        1048576
                        1114112))
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        65536
                        128)
                      512))
                  2048)
                4096)
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      (Code.joinWords 256
                        16384
                        (Nat.shiftLeft
                          1152921504606846976
                          128))
                      (Nat.shiftLeft
                        65536
                        128))
                    (Code.joinWords 512
                      (Code.joinWords 256
                        16384
                        (Nat.shiftLeft
                          1152996271397535744
                          128))
                      (Nat.shiftLeft
                        65536
                        128)))
                  4096)
                8192))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Code.joinWords 512
                    16384
                    (Code.joinWords 128
                      1048640
                      292058890240))
                  2048)
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      (Code.joinWords 256
                        49152
                        (Nat.shiftLeft
                          17408
                          128))
                      (Code.joinWords 128
                        4503599627370560
                        4503599627436100))
                    (Code.joinWords 512
                      16384
                      (Code.joinWords 128
                        4503599627370560
                        4503891685212160)))
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            649037107316853453566312041152512
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          256)
                        512))
                    2048)))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          256)
                        512)
                      1024)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            649037107316853453566312041152512
                            128)
                          (Code.joinWords 128
                            649037107316853453566312041152512
                            649037107316853453566312041152512))
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128))
                        512))
                    2048)
                  4096)))))
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 1024
                    (Code.joinWords 512
                      (Code.joinWords 256
                        268451840
                        (Nat.shiftLeft
                          285212672
                          128))
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          65536
                          128)
                        (Code.joinWords 128
                          269484032
                          17825792)))
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        65536
                        128)
                      512))
                  2048)
                4096)
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            265845599216404296466459665251226877952
                            128)
                          (Nat.shiftLeft
                            311039351075567316223759865850556841984
                            128))
                        512)
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      (Code.joinWords 256
                        16384
                        (Nat.shiftLeft
                          1152921504606846976
                          128))
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          65536
                          128)
                        (Code.joinWords 128
                          303412051027974332350464
                          18889470435078208225280)))
                    (Code.joinWords 512
                      (Code.joinWords 256
                        16384
                        (Nat.shiftLeft
                          1152996271397535744
                          128))
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          65536
                          128)
                        (Code.joinWords 128
                          4503599627370496
                          4503599627370496)))))
                8192))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      (Code.joinWords 256
                        49152
                        (Nat.shiftLeft
                          17408
                          128))
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          65540
                          128)
                        (Code.joinWords 128
                          16448
                          1088)))
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10633823966279326983230456482242756608
                          256)
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          664613997892457936451903530140172288
                          128)
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            664613998047200441362576064502562816
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            649037107316853453566312041152512
                            128)
                          (Code.joinWords 128
                            10633823966279326983806917234546180096
                            649037107316853453566312041152512)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            664613998047200441362576064502562816
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          (Code.joinWords 128
                            10633823966279326983806917234546180096
                            324518553658426726783156020576256))))))
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Code.joinWords 256
                        16384
                        (Nat.shiftLeft
                          309485009821419835515469824
                          128))
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          65536
                          128)
                        (Code.joinWords 128
                          4951760157141521099596496896
                          309485009821345343602688000)))
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            255876389188596305547817917159248494592
                            128)
                          (Nat.shiftLeft
                            298577838553186727964888747767773528064
                            128))
                        512)
                      1024)
                    (Code.joinWords 512
                      (Code.joinWords 256
                        16384
                        (Nat.shiftLeft
                          309485009821345068724781056
                          128))
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          65536
                          128)
                        (Code.joinWords 128
                          4952063569188045474301476864
                          309485009821345068724781056)))))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          16384
                          (Nat.shiftLeft
                            74766790688768
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            65536
                            128)
                          (Code.joinWords 128
                            4503599627370496
                            4503874505277440)))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10633986225556156197170308812556468224
                          256)
                        512))
                    2048)
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          16384
                          (Nat.shiftLeft
                            309485009821345068724781056
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            65536
                            128)
                          (Code.joinWords 128
                            303412046524374704979968
                            309503899287276547305635840)))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          664624139252002267197788038128205824
                          128)
                        256))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            664613998047200441362576064502562816
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            649037107316853453566312041152512
                            128)
                          (Code.joinWords 128
                            10633823966279326983806917234546180096
                            649037107316853453566312041152512)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            664624139252002267197788038128205824
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          (Code.joinWords 128
                            10633986225556156197170308812556468224
                            324518553658426726783156020576256)))))))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 1024
                    (Code.joinWords 512
                      (Code.joinWords 256
                        268451840
                        (Nat.shiftLeft
                          285212672
                          128))
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          65536
                          128)
                        (Code.joinWords 128
                          1048576
                          1048576)))
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        65536
                        128)
                      512))
                  2048)
                4096)
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          128)
                        (Code.joinWords 128
                          297747071055821155530452781502797185024
                          311039351013670314259490852105600630784))
                      512)
                    1024)
                  2048)
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            255211775190703847597530955573826158592
                            308380895081521604399381491180197904384)
                          (Code.joinWords 128
                            297747071115242277416151034697955147776
                            311039351075567316223759865850556841984))
                        512)
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      (Code.joinWords 256
                        16384
                        (Nat.shiftLeft
                          1152921504606846976
                          128))
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          65536
                          128)
                        (Code.joinWords 128
                          4503599627370496
                          4503599627370496)))
                    (Code.joinWords 512
                      (Code.joinWords 256
                        16384
                        (Nat.shiftLeft
                          1152996271397535744
                          128))
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          65536
                          128)
                        (Code.joinWords 128
                          4503599627370496
                          4503599627370496)))))))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          664613997892457936451903530140172288
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          664613997892457936451903530140172288
                          128)
                        256))
                    2048)
                  4096)
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      (Code.joinWords 256
                        49152
                        (Nat.shiftLeft
                          17408
                          128))
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          65540
                          128)
                        (Code.joinWords 128
                          64
                          64)))
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5316911983139663491615228241121378304
                          256)
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          664613997892457936451903530140172288
                          128)
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            664613998047200441362576064502562816
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            649037107316853453566312041152512
                            128)
                          (Code.joinWords 128
                            5316911983139663491903458617273090048
                            649037107316853453566312041152512)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            664613997892457936451903530140172288
                            664624139252002267197788038128205824)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          (Code.joinWords 128
                            5316911983139663491903458617273090048
                            324518553658426726783156020576256)))))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Code.joinWords 256
                        16384
                        (Nat.shiftLeft
                          74766790688768
                          128))
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          65536
                          128)
                        (Nat.shiftLeft
                          274877906944
                          128)))
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          255876389188596305547817917159248494592
                          128)
                        (Nat.shiftLeft
                          266551751529743911152112646409143975936
                          128))
                      512)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          664613997892457936451903530140172288
                          664613998047200441362576064502562816)
                        256)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            664624139097259762287115503765815296
                            664624139252002267197788038128205824)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          256)))))
                (Code.joinWords 4096
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
                        (Code.joinWords 256
                          16384
                          (Nat.shiftLeft
                            74766790688768
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            65536
                            128)
                          (Code.joinWords 128
                            4503599627370496
                            4503874505277440)))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5316911983139663491903458617273090048
                          256)
                        512)))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            664624139097259762287115503765815296
                            664624139252002267197788038128205824)
                          256)
                        (Nat.shiftLeft
                          5316911983139663491615228241121378304
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            664613997892457936451903530140172288
                            664613998047200441362576064502562816)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            649037107316853453566312041152512
                            128)
                          (Code.joinWords 128
                            5317561020246980345357024929314242560
                            649037107316853453566312041152512)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            664624139097259762287115503765815296
                            664624139252002267197788038128205824)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          (Code.joinWords 128
                            5316911983139663491903458617273090048
                            324518553658426726783156020576256))))))))))))
    (Code.joinWords 262144
      (Code.joinWords 131072
        (Nat.shiftLeft
          (Nat.shiftLeft
            (Nat.shiftLeft
              (Code.joinWords 4096
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          298581742956649512154706439558116933632
                          128)
                        256)
                      512)
                    1024)
                  2048)
                (Nat.shiftLeft
                  (Code.joinWords 1024
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          298577838622511370167139857377540440064
                          128)
                        256)
                      512)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          298581742986515722312972061835888951296
                          128)
                        256)
                      512))
                  2048))
              8192)
            16384)
          32768)
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 128
                          268451840
                          16777216)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            16842752
                            128)
                          269484032))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          65536
                          128)
                        512))
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 512
                    (Code.joinWords 128
                      16384
                      16778240)
                    (Nat.shiftLeft
                      18963252907773435904000
                      128))
                  4096))
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          256)
                        512)
                      1024)
                    2048)
                  4096)
                8192))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Code.joinWords 512
                    (Code.joinWords 128
                      49152
                      309485009821345068724782080)
                    (Code.joinWords 256
                      (Nat.shiftLeft
                        309485009821345068724847620
                        128)
                      16448))
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      (Code.joinWords 128
                        16384
                        309485009821345068724782080)
                      (Nat.shiftLeft
                        309503973074252842143907840
                        128))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            649037107316853453566312041152512
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          256)
                        512))))
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      16384
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          65536
                          128)
                        4951760157141521099596496896))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      16384
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          65536
                          128)
                        4952063569188045474301476864))
                    2048))
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            649037107316853453566312041152512
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            649037107316853453566312041152512
                            128)
                          (Nat.shiftLeft
                            649037107316853453566312041152512
                            128)))
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128))
                        512))
                    2048)
                  4096))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      65536
                      128)
                    512)
                  4096)
                8192)
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            324518553658426726783156020576256
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
                          5316911983139663491615228241121378304
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5316911983139663491615228241121378304
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            5316911983139663491615228241121378304
                            324518553658426726783156020576256)
                          256)
                        512)))
                  4096)))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Code.joinWords 512
                    (Nat.shiftLeft
                      1024
                      128)
                    (Nat.shiftLeft
                      66564
                      128))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        65536
                        128)
                      512)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            649037107316853453566312041152512
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          256)
                        512))))
                8192)
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          265845599156983174580761412056068915200
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          266551751529743911147464931593697624064
                          128)
                        256))
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          256)
                        512)
                      1024))
                  4096)
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5316911983139663491615228241121378304
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5316911983139663491615228241121378304
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
                          (Code.joinWords 128
                            649037107316853453566312041152512
                            649037107316853453566312041152512)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            649037107316853453566312041152512
                            128)
                          (Code.joinWords 128
                            5317561020246980345068794553162530816
                            649037107316853453566312041152512)))
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          (Code.joinWords 128
                            5316911983139663491903458617273090048
                            324518553658426726783156020576256))
                        512)))))))))
      (Code.joinWords 131072
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 1024
                    (Code.joinWords 512
                      (Code.joinWords 256
                        268484608
                        (Nat.shiftLeft
                          16777216
                          128))
                      (Code.joinWords 256
                        (Code.joinWords 128
                          303412046524374974464000
                          65536)
                        (Nat.shiftLeft
                          16777216
                          128)))
                    (Code.joinWords 512
                      268435456
                      (Code.joinWords 128
                        269484032
                        65536)))
                  2048)
                4096)
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 512
                    16384
                    (Code.joinWords 256
                      (Nat.shiftLeft
                        65536
                        128)
                      (Nat.shiftLeft
                        18889465931478580854784
                        128)))
                  4096)
                8192))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        4951760157141521099596546048
                        (Code.joinWords 128
                          4951760157141521099612274880
                          65536))
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          5242944
                          65536)
                        512))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        4951760157141521099596546048
                        (Code.joinWords 128
                          4952063569188045474302525440
                          65536))
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          1048576
                          65536)
                        512))
                    2048))
                (Code.joinWords 2048
                  (Code.joinWords 1024
                    (Code.joinWords 512
                      (Code.joinWords 256
                        49152
                        (Nat.shiftLeft
                          1024
                          128))
                      (Code.joinWords 256
                        (Code.joinWords 128
                          49344
                          65740)
                        (Nat.shiftLeft
                          1024
                          128)))
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        65536
                        128)
                      512))
                  (Code.joinWords 1024
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        65536
                        128)
                      512)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        65536
                        128)
                      512))))
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 512
                    (Code.joinWords 256
                      16384
                      (Nat.shiftLeft
                        309485009821345068724781056
                        128))
                    (Code.joinWords 256
                      (Nat.shiftLeft
                        65536
                        128)
                      (Nat.shiftLeft
                        309503899287276547305635840
                        128)))
                  4096)
                8192)))
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          256)
                        512)
                      1024)
                    2048)
                  4096)
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          255876389188596305533982859103966330880
                          266551751569357992395373728353614823424)
                        256)
                      512)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          256)
                        512)
                      1024)
                    2048)))
              16384)
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      65536
                      128)
                    512)
                  2048)
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        64
                        65604)
                      512)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        65536
                        128)
                      512))
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            649037107316853453566312041152512
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            324518553658426726783156020576256
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
                          332306998946228968225951765070086144
                          128)
                        256)
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          332306998946228968225951765070086144
                          128)
                        256)
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
                          256)))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          332306998946228968225951765070086144
                          128)
                        256)
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
                          332306998946228968225951765070086144
                          128)
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            649037107316853453566312041152512
                            332956036053545821679518077111238656)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            649037107316853453566312041152512
                            128)
                          (Code.joinWords 128
                            649037107316853453566312041152512
                            649037107316853453566312041152512)))
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
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128))))))))))
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          268451840
                          (Nat.shiftLeft
                            16777216
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            65536
                            128)
                          (Code.joinWords 128
                            269484032
                            16777216)))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          65536
                          128)
                        512))
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10633823966279326983230456482242756608
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10633823966279326983230456482242756608
                          256)
                        512))
                    2048)
                  4096))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          297747071055821155530452781502797185024
                          128)
                        256)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          128)
                        (Nat.shiftLeft
                          298577838553186727951017660915472400384
                          128)))
                    1024)
                  4096)
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          265845599216404296466459665251226877952
                          128)
                        (Nat.shiftLeft
                          266551751591640913102510573301799059456
                          128))
                      512)
                    2048)
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      16384
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          65536
                          128)
                        (Code.joinWords 128
                          303412046524374704979968
                          18889465931478580854784)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          10633823966279326983230456482242756608
                          256)
                        (Nat.shiftLeft
                          10633823966279326983806917234546180096
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          10633986225556156196593848060253044736
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            10633986225556156197170308812556468224
                            324518553658426726783156020576256)
                          256)))))))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      (Code.joinWords 256
                        49152
                        (Nat.shiftLeft
                          1024
                          128))
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          65540
                          128)
                        (Code.joinWords 128
                          16448
                          1024)))
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10633823966279326983230456482242756608
                          256)
                        512)
                      1024))
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
                            649037107316853453566312041152512
                            128)
                          (Code.joinWords 128
                            10633823966279326983806917234546180096
                            649037107316853453566312041152512)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            10633823966279326983230456482242756608
                            332306999023600220681288032251281408)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          (Code.joinWords 128
                            10633986225556156197170308812556468224
                            324518553658426726783156020576256))))))
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Code.joinWords 256
                        16384
                        (Nat.shiftLeft
                          309485009821345068724781056
                          128))
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          65536
                          128)
                        (Code.joinWords 128
                          4951760157141521099596496896
                          309485009821345068724781056)))
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            255211775190703847597530955573826158592
                            128)
                          (Nat.shiftLeft
                            297747071055821155544287839558079348736
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            298411685053713613480739743088219521024
                            128)
                          (Nat.shiftLeft
                            298577838553186727964888747767773528064
                            128)))
                      1024)
                    (Code.joinWords 512
                      (Code.joinWords 256
                        16384
                        (Nat.shiftLeft
                          309485009821345068724781056
                          128))
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          65536
                          128)
                        (Code.joinWords 128
                          4952063569188045474301476864
                          309485009821345068724781056)))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          332306998946228968225951765070086144
                          128)
                        256)
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            10633986225556156196593848060253044736
                            332306998946228968225951765070086144)
                          256)
                        (Nat.shiftLeft
                          10633986225556156197170308812556468224
                          256))
                      1024))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          16384
                          (Nat.shiftLeft
                            309485009821345068724781056
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            65536
                            128)
                          (Code.joinWords 128
                            303412046524374704979968
                            309503899287276547305635840)))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          332306999023600220681288032251281408
                          128)
                        256))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            10633823966279326983230456482242756608
                            332956036130917074134854344292433920)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            649037107316853453566312041152512
                            128)
                          (Code.joinWords 128
                            10633823966279326983806917234546180096
                            649037107316853453566312041152512)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            10633986225556156196593848060253044736
                            332306999023600220681288032251281408)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          (Code.joinWords 128
                            10633986225556156197170308812556468224
                            324518553658426726783156020576256)))))))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
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
                    2048)
                  4096)
                8192)
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          256)
                        512)
                      1024)
                    2048)
                  4096)
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Code.joinWords 128
                          255211775190703847597530955573826158592
                          265845599216404296466459665251226877952)
                        (Code.joinWords 128
                          255876389248017427419681112299124293632
                          266551751591795655607421245836161449984))
                      512)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5316911983139663491615228241121378304
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5316911983139663491903458617273090048
                          256)
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          (Code.joinWords 128
                            5316911983139663491903458617273090048
                            324518553658426726783156020576256))
                        512))))))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
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
                    2048)
                  4096)
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        65540
                        128)
                      512)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5316911983139663491615228241121378304
                          256)
                        512)
                      1024))
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
                            332956036130917074134854344292433920
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            649037107316853453566312041152512
                            128)
                          (Code.joinWords 128
                            5317561020246980345357024929314242560
                            649037107316853453566312041152512)))
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
                            324518553658426726783156020576256)))))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          332306998946228968225951765070086144
                          128)
                        256)
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          255211775190703847597530955573826158592
                          128)
                        (Nat.shiftLeft
                          265845599156983174594596470111351078912
                          128))
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          255876389188596305547817917159248494592
                          128)
                        (Nat.shiftLeft
                          266551751529743911152689107161447399424
                          128)))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          332306999023600220681288032251281408
                          128)
                        256)
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
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128))))))
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
                          5316911983139663491903458617273090048
                          256))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            332306999023600220681288032251281408
                            128)
                          256)
                        (Nat.shiftLeft
                          5316911983139663491903458617273090048
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            649037107316853453566312041152512
                            332956036130917074134854344292433920)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            649037107316853453566312041152512
                            128)
                          (Code.joinWords 128
                            5317561020246980345357024929314242560
                            649037107316853453566312041152512)))
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
                            324518553658426726783156020576256)))))))))))))

/-- The block word is computed from the verified profile data. -/
theorem word_eq :
    Code.profileWord 64 24 (fun i q => Data.profiles (768 + i) q) = word := by
  decide +kernel

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage012
