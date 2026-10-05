/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Cslib.Foundations.RelationAlgebra.FastCatalogueCoverage

/-!
# Profile coverage for models 1409–1472 of the ⟨1, 4, 0⟩ row

The balanced word contains exactly the cycle profiles of this block and its atom renamings.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage022

/-- The cycle profiles covered by this block of models. -/
def word : ℕ :=
  (Code.joinWords 524288
    (Code.joinWords 262144
      (Nat.shiftLeft
        (Code.joinWords 65536
          (Nat.shiftLeft
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            338496216801602482759160116694516498432
                            128)
                          256)
                        512)
                      1024)
                    2048)
                  4096)
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            170141183460469231731687303715884105728
                            338510749781908799313436204534048227328)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            170143779608898499145501568964048715776
                            40763678800558383326837793446256705536)
                          256)
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            170141183460469231731687303715884105728
                            46076442322638060378076870418876071936)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            170143779608898499145501568964048715776
                            882782370619437243529085665199259648)
                          256)
                        512))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            170143779608898499145501568964048715776
                            218087243281995192717064050783027200)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            170143779608898499145501568964048715776
                            218158231715607973563552264209039360)
                          256)
                        512)))))
              16384)
            32768)
          (Nat.shiftLeft
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          1298074214633706907132624082305024
                          1298074214633706907132624082305024)
                        256)
                      512)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        21267647932558653966460912964485513216
                        256)
                      512)
                    2048)
                  4096))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Code.joinWords 128
                          21267647932558653966460912964485513216
                          1298074214633706907132624082305024)
                        (Code.joinWords 128
                          21268946006773287673368045588567818240
                          1298074214633706907132624082305024))
                      512)
                    2048)
                  4096)
                (Code.joinWords 4096
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
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            317560875867990057760925155495101071360
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            332312069548629881143557751882907648
                            128)
                          256)
                        512)))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            21599954931504882934686864729555599360
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            332312069548629881143557751882907648
                            128)
                          256)
                        512))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          21267647932558653966460912964485513216
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            332388128584643574907647554075230208))
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            332312069548629881143557751882907648
                            128)
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
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            333511611817409048235770840218465206272
                            128)
                          256)
                        512)
                      1024)
                    2048)
                  4096)
                8192)
              16384)
            (Nat.shiftLeft
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170141183460469231731687303715884105728
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            333526068813226552818696702799252553728
                            128)
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170141183460469231731687303715884105728
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            56045652304071656867639255431030767616
                            128)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170143779608898499145501568964048715776
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            13344370893243597857586877864165244928
                            128)
                          256))))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170143779608898499145501568964048715776
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            35778997760501195419543426476787367936
                            128)
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170143779608898499145501568964048715776
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            2710541856361868781567779414170664960
                            128)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170143779608898499145501568964048715776
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            2710384667687441661713614540384501760
                            128)
                          256)))))
                8192)
              16384))
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            337623910929368631717566993311207522304
                            128)
                          (Code.joinWords 128
                            319845486485745381917478573879957913600
                            338509197543748819828231442935339548672))
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
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            319679332986272267433365597997422870528
                            338330063302129368275047140811981455360)
                          (Code.joinWords 128
                            319848082693750513721901764857642876928
                            72663598450065001162492014466886008832))
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            332306998946228968225951765070086144
                            332306998946228968225951765070086144)
                          256)
                        512))
                    2048)
                  4096))
              16384)
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          85070591730234615865843651857942052864
                          128)
                        256)
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85071889804449249572750784482024357888
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1298074214633706907132624082305024
                            128)
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          85071889804449249572750784482024357888
                          128)
                        256))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          85070591730234615865843651857942052864
                          128)
                        256)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          85070591730234615865843651857942052864
                          128)
                        256)
                      1024))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          85070591730234615865843651857942052864
                          85070591730234615865843651857942052864)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          85071889804449249572750784482024357888
                          85071889804449249572750784482024357888)
                        256))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85071889804449249572750784482024357888
                            85071889804449249572750784482024357888)
                          256)
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          256))
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          85071889804449249572750784482024357888
                          85071889804449249572750784482024357888)
                        256)))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170141183460469231731687303715884105728
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            298910145552132956919243612680542486528
                            317571260525083854583659536342556082176)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85071889804449249572750784482024357888
                            85071889824256290201316868880410345472)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            332312069548629881143557751882907648
                            5070602402093509226704224124928)
                          256)))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85071889804449249572750784482024357888
                            85071889824256290201316868880410345472)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1298074214633706907132624082305024
                            128)
                          (Code.joinWords 128
                            21601253005719516641593997353637904384
                            1298074214633706907132624082305024)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85071889804449249572750784482024357888
                            106339537756814944167777781844895858688)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            332312069548629881143557751882907648
                            5070602402093509226704224124928)
                          256)))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85071889804449249572750784482024357888
                            85071889824256290201316868880410345472)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            332312069626001133598894019064102912
                            5070602400912917605986812821504)
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            170141183460469231731687303715884105728
                            170141183460469231731687303715884105728)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            43033756373556228578226800176540942336
                            45370289960438499778252877394958352384)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85071889804449249572750784482024357888
                            85071889824256290201316868880410345472)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            332312069626001133598894019064102912
                            5070602402093509226704224124928)
                          256))))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85070591730234615865843651857942052864
                            85070591750041656494409736256328040448)
                          256)
                        (Nat.shiftLeft
                          332306999023600220681288032251281408
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85071889804449249572750784482024357888
                            1298094021674335473217022468292608)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            332312069626001133598894019064102912
                            5070602402093509226704224124928)
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85071889804449249572750784482024357888
                            1298094021674335473217022468292608)
                          256)
                        (Code.joinWords 256
                          21267647932558653966460912964485513216
                          21599954931582254187142200996736794624))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            106339537737007903539211697446509871104
                            21268946026580328301934129986953805824)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            332312069626001133598894019064102912
                            5070602402093509226704224124928)
                          256)))))))))
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          85071889804449249572750784482024357888
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            81129638414606681695789005144064
                            128)
                          256)
                        512)
                      1024))
                  4096)
                8192)
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            14164585830083009770631193986112421888
                            128)
                          (Nat.shiftLeft
                            14177566572229346839702520226935472128
                            128))
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5649218982085892459841180006191464448
                            128)
                          256)
                        512))
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85071889804449249577362470500451745792
                            81129638414606681700187051655168)
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            830767497365572420564879412675215360
                            872305872233851041593123383308976128)
                          (Code.joinWords 128
                            833363645949582339289817195202215936
                            220672616652144085680135661751894016))
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            332388128584643574907651952121741312)
                          256)
                        512)))
                  4096)))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          85071889804449249572750784482024357888
                          128)
                        256)
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5070602400912917605986812821504
                            128)
                          256)
                        512)
                      1024)
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85070591730234615865843651857942052864
                            85070591730234615865843651857942052864)
                          256)
                        (Nat.shiftLeft
                          85070591730234615865843651857942052864
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85071889804449249572750784482024357888
                            85071889804449249572750784482024357888)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            81129638414606681695789005144064
                            128)
                          256))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          85071889804449249572750784482024357888
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85071889804449249572750784482024357888
                            5070602400912917605986812821504)
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            86200240815519599301775817965568
                            128)
                          256)
                        512)
                      1024))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85071889824256290201316868880410345472
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5070602402093509226704224124928
                            128)
                          256))
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            13292279957849158729038070602803445760
                            128)
                          (Nat.shiftLeft
                            13294876106278426143428796603271479296
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            13333818332717437350066314573437206528
                            128)
                          (Nat.shiftLeft
                            2712975108584447436485896884134608896
                            128)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316917053742065585124454945345503232
                            128)
                          256)))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85071889804449249572750784482024357888
                            85071889824256290201316868880410345472)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85071889804449249577362470500451745792
                            86200240815519599301775817965568)
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            170141183460469231731687303715884105728
                            170141183460469231731687303715884105728)
                          256)
                        (Code.joinWords 256
                          (Code.joinWords 128
                            42535295865117307932921825928971026432
                            45193751856687139678729440049531715584)
                          (Code.joinWords 128
                            42701449374532628357545512144289660928
                            2834994095321191845331051465987325952)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85071889804449249572750784482024357888
                            1298094021674335473217022468292608)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            86200240816700190926891275780096
                            128)
                          256))))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            42535295865117307932921825928971026432
                            128)
                          (Code.joinWords 128
                            170141183460469231731687303715884105728
                            45193751856687139681179398246821265408))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            42701449364590422417034801811506069504
                            128)
                          (Code.joinWords 128
                            170141183460469231731687303715884105728
                            2834994084760015887636616392298463232)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          85071889804449249572750784482024357888
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1298074214633711518818642509692928
                            86200240816700190926891275780096)
                          256)))
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            21267647932558653966460912964485513216)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            1180591625115457814528)
                          256))
                      1024))))))
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            22098415429924226387025792377160728576
                            872305872233851041593123383308976128)
                          (Code.joinWords 128
                            22101011578353493800840057625325338624
                            885286614380188110664449624132026368))
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            332306998946228968225951765070086144
                            332306998946228968225951765070086144)
                          256)
                        512))
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          338496216801602482759160116694516498432
                          128)
                        256)
                      512)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            22098415429924226387025792377160728576
                            872305872233851041593123383308976128)
                          (Code.joinWords 128
                            21436397580615778369298826629547556864
                            220672616652144085680135661751894016))
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            332306998946228968225951765070086144
                            332306998946228968225951765070086144)
                          256)
                        512)))
                  4096))
              16384)
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          85071889804449249572750784482024357888
                          85071889804449249572750784482024357888)
                        256)
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1298074214633706907132624082305024
                            1298074214633706907132624082305024)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            333605073160862675133084389152391168
                            1298074214633706907132624082305024)
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            332312069548629881143557751882907648
                            5070602400912917605986812821504)
                          256)
                        512))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          85070591730234615865843651857942052864
                          85070591730234615865843651857942052864)
                        256)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          85071889804449249572750784482024357888
                          85071889804449249572750784482024357888)
                        256)
                      1024))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          332306998946228968225951765070086144
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            332312069548629881143557751882907648
                            5070602400912917605986812821504)
                          256)
                        512))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          21599954931504882934686864729555599360
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            332312069548629881143557751882907648
                            5070602400912917605986812821504)
                          256)
                        512)))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            170141183460469231731687303715884105728
                            170141183460469231731687303715884105728)
                          256)
                        (Code.joinWords 256
                          (Code.joinWords 128
                            297747071055821155530452781502797185024
                            316356262996809977751106080346722009088)
                          (Code.joinWords 128
                            298910145621689712876590916876437028864
                            51725661378623170336823856623129722880)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85071889804449249572750784482024357888
                            1298094021674335473217022468292608)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            332312069626001133598894019064102912
                            5070602402093509226704224124928)
                          256)))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1298074214633706907132624082305024
                            1298074214633706907132624082305024)
                          256)
                        (Code.joinWords 256
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            1298074214633706907132624082305024)
                          21601253005796887894049333620819099648))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            21267647932558653966460912964485513216)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            332312069626002314190514736475406336
                            1180591620717411303424)
                          256)))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85071889804449249572750784482024357888
                            90388801807395953692932097121531723776)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            332312069626001133598894019064102912
                            5070602400912917605986812821504)
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            170141183460469231731687303715884105728
                            170141183460469231731687303715884105728)
                          256)
                        (Code.joinWords 256
                          (Code.joinWords 128
                            42535295865117307932921825928971026432
                            45193751856687139678729440049531715584)
                          (Code.joinWords 128
                            498460508438920645304974247569915904
                            2834994095321191845331051465987325952)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85071889804449249572750784482024357888
                            5318291206799752433770141052594814976)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            332312069626001133598894019064102912
                            5070602402093509226704224124928)
                          256))))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316911983139663491615228241121378304
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            332306999023600220681288032251281408
                            21267647932558653966460912964485513216)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316993112778078098296924030126522368
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            5070679773345964562971405320192
                            5070602402093509226704224124928)
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316993112778078098296924030126522368
                            128)
                          256)
                        (Code.joinWords 256
                          21267647932558653966460912964485513216
                          (Code.joinWords 128
                            77371252455336267181195264
                            81129638414606681695789005144064)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            26584641045336732064757836994612035584)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            5070679773345964562971405320192
                            1180591620717411303424)
                          256)))))))))))
    (Code.joinWords 262144
      (Nat.shiftLeft
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          85070591730234615865843651857942052864
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85071889804449249572750784482024357888
                            1298074214633706907132624082305024)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          85071889804449249572750784482024357888
                          256)
                        512)))
                  4096)
                8192)
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            332306998946228968225951765070086144000
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            320177793484691610885704525645027999744
                            128)
                          (Nat.shiftLeft
                            333524592559555385304842166459288256512
                            128)))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316911983139663491615228241121378304
                            128)
                          256)
                        512))
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            316356262996809977751106080346722009088
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            170141183460469231731687303715884105728
                            317571260461707127430938260666838941696)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85071889804449249572750784482024357888
                            5316993112778078098296924030126522368)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85071889804449249577362470500451745792
                            81129638414606681700187051655168)
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85071889804449249572750784482024357888
                            26585857989912951164983273829689196544)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1298074214633706907132624082305024
                            128)
                          (Code.joinWords 128
                            85071889804449249577362470500451745792
                            1298074214633706907132624082305024)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85071889804449249572750784482024357888
                            5316993112778078098296924030126522368)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            106339537737007903543823383464937259008
                            81129638414606681700187051655168)
                          256))))
                  4096)))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          85070591730234615865843651857942052864
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          85070591730234615865843651857942052864
                          256)
                        (Nat.shiftLeft
                          85070591730234615865843651857942052864
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          85071889804449249572750784482024357888
                          256)
                        (Nat.shiftLeft
                          85071889804449249572750784482024357888
                          256))))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          85070591730234615865843651857942052864
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85071889804449249572750784482024357888
                            21267647932558653966460912964485513216)
                          256)
                        (Nat.shiftLeft
                          85071889804449249572750784482024357888
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          85071889804449249572750784482024357888
                          256)
                        (Nat.shiftLeft
                          85071889804449249572750784482024357888
                          256)))))
                8192)
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            329648542954659136480144150949525454848
                            128)
                          (Nat.shiftLeft
                            332309595094658235654177549125836341248
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            330853155825839216489963226097904517120
                            128)
                          (Nat.shiftLeft
                            77648203370959079785327121158249644032
                            128)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316911983139663491615228241121378304
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316911983139663491615228241121378304
                            128)
                          256)))
                    2048)
                  4096)
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85071889804449249572750784482024357888
                            5316993112778078098585154406278234112)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85071889804449249577362470500451745792
                            81129638414606681695789005144064)
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85070591730234615865843651857942052864
                            5316911983139663491903458617273090048)
                          256)
                        (Nat.shiftLeft
                          85070591730234615870455337876369440768
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85071889804449249572750784482024357888
                            5316993112778078098585154406278234112)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1298074214633711518818642509692928
                            81129638414606681700187051655168)
                          256))))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            170141183460469231731687303715884105728
                            50510663839826803173082856864094355456)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            170141183460469231731687303715884105728
                            45370289949877323820558442321269489664)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85071889804449249572750784482024357888
                            5316993112778078098585154406278234112)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85071889804449249577362470500451745792
                            81129638414606681700187051655168)
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Code.joinWords 128
                            85071889804449249572750784482024357888
                            26584559915698317458364371581758603264))
                        (Nat.shiftLeft
                          1298074214633711518818642509692928
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            106339537737007903539211697446509871104
                            5316993112778078098585154406278234112)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            21268946006773287677979731606995206144
                            81129638414606681700187051655168)
                          256))))))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1298074214633706907132624082305024
                          128)
                        256)
                      512)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          1298074214633706907132624082305024
                          1298074214633706907132624082305024)
                        256)
                      512)
                    2048)
                  4096))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          21268946006773287673368045588567818240
                          21268946006773287673368045588567818240)
                        256)
                      (Code.joinWords 256
                        (Code.joinWords 128
                          21267647932558653966460912964485513216
                          1298074214633706907132624082305024)
                        (Code.joinWords 128
                          21268946006773287673368045588567818240
                          1298074214633706907132624082305024)))
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          128)
                        256)
                      512)
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          21268946006773287673368045588567818240
                          21268946006773287673368045588567818240)
                        256)
                      (Code.joinWords 256
                        (Code.joinWords 128
                          21267647932558653966460912964485513216
                          1298074214633706907132624082305024)
                        (Code.joinWords 128
                          21268946006773287673368045588567818240
                          1379203853048313588828413087449088))))
                  4096)))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          1298074214633706907132624082305024
                          1298074214633706907132624082305024)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          1298074214633706907132624082305024
                          1298074214633706907132624082305024)
                        256))
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          21267647932558653966460912964485513216
                          21267647932558653966460912964485513216)
                        256)
                      (Nat.shiftLeft
                        21267647932558653966460912964485513216
                        256))
                    2048)
                  4096))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          128)
                        (Code.joinWords 128
                          21268946006773287673368045588567818240
                          21268946006773287673368045588567818240))
                      (Code.joinWords 256
                        (Code.joinWords 128
                          21267647932558653966460912964485513216
                          1298074214633706907132624082305024)
                        21268946006773287673368045588567818240))
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          128)
                        256))
                    (Code.joinWords 512
                      (Code.joinWords 256
                        (Code.joinWords 128
                          21267647932558653966460912964485513216
                          21267647932558653966460912964485513216)
                        (Code.joinWords 128
                          21267647932558653966460912964485513216
                          21267729062197068573142608753490657280))
                      (Code.joinWords 256
                        21267647932558653966460912964485513216
                        (Nat.shiftLeft
                          81129638414606681695789005144064
                          128))))
                  4096)))))
        131072)
      (Code.joinWords 131072
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1298074214633706907132624082305024
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1298074214633706907132624082305024
                          128)
                        256))
                    2048)
                  4096)
                8192)
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          128)
                        (Nat.shiftLeft
                          21268946006773287673368045588567818240
                          128))
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          1298074214633706907132624082305024
                          128)
                        (Nat.shiftLeft
                          1298074214633706907132624082305024
                          128)))
                    2048)
                  4096)
                8192))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        21267647932558653966460912964485513216
                        128)
                      256)
                    2048)
                  4096)
                8192)
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316911983139663491615228241121378304
                            128)
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            26584559915698317458076141205606891520
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316993112778078098296924030126522368
                            128)
                          256)
                        512)))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            317560875867990057760925155495101071360
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316993112778078098296924030126522368
                            128)
                          256)
                        512))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128))
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316917053742064404532834227934199808
                            128)
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316993112778078098296924030126522368
                            128)
                          256)
                        512))))
                8192)))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1298074214633706907132624082305024
                          128)
                        256)
                      512)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          1298074214633706907132624082305024
                          1298074214633706907132624082305024)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          1298074214633706907132624082305024
                          1298074214633706907132624082305024)
                        256))
                    2048)
                  4096))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          128)
                        (Code.joinWords 128
                          21268946006773287673368045588567818240
                          21268946006773287673368045588567818240))
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          1298074214633706907132624082305024
                          128)
                        (Code.joinWords 128
                          21268946006773287673368045588567818240
                          1298074214633706907132624082305024)))
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          128)
                        (Code.joinWords 128
                          21268946006773287673368045588567818240
                          21268946006773287673368045588567818240))
                      (Code.joinWords 256
                        (Code.joinWords 128
                          21267647932558653966460912964485513216
                          1298074214633706907132624082305024)
                        21268946006773287673368045588567818240))
                    2048)
                  4096)))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1298074214633706907132624082305024
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1298074214633706907132624082305024
                          128)
                        256))
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          21267647932558653966460912964485513216
                          21267647932558653966460912964485513216)
                        256)
                      (Nat.shiftLeft
                        21267647932558653966460912964485513216
                        256))
                    2048)
                  4096))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          128)
                        256)
                      512)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          128)
                        (Code.joinWords 128
                          21268946006773287673368045588567818240
                          21268946006773287673368045588567818240))
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          1298074214633706907132624082305024
                          128)
                        (Code.joinWords 128
                          21268946006773287673368045588567818240
                          1303144817034619824738610895126528)))
                    2048))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          21267647932558653966460912964485513216
                          21267647932558653966460912964485513216)
                        256)
                      512)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Code.joinWords 256
                        (Code.joinWords 128
                          21267647932558653966460912964485513216
                          21267647932558653966460912964485513216)
                        21267647932558653966460912964485513216)
                      (Code.joinWords 256
                        21267647932558653966460912964485513216
                        (Code.joinWords 128
                          21267653003161054879378518951298334720
                          5070602400912917605986812821504)))
                    2048))))))
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          85071889804449249572750784482024357888
                          256)
                        (Nat.shiftLeft
                          85071889804449249572750784482024357888
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1298074214633706907132624082305024
                            5318210057354297198522360865203683328)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1298074214633706907132624082305024
                            1298074214633706907132624082305024)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316993112778078098296924030126522368
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            81129638414606681695789005144064
                            128)
                          256))))
                  4096)
                8192)
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            34559927890407812695498983567288958976
                            128)
                          (Nat.shiftLeft
                            34562524038837080109313248815453569024
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            13333818332717437350066314573437206528
                            128)
                          (Nat.shiftLeft
                            13346799074863774419137640814260256768
                            128)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316911983139663491615228241121378304
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316911983139663491615228241121378304
                            128)
                          256)))
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            297747071055821155530452781502797185024
                            128)
                          (Code.joinWords 128
                            170141183460469231731687303715884105728
                            316356262996809977768111672539673001984))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            298910145552132956919243612680542486528
                            128)
                          (Code.joinWords 128
                            170141183460469231731687303715884105728
                            61694871273110821899270251771341045760)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85071889804449249572750784482024357888
                            5316993112778078098585154406278234112)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1298074214633711518818642509692928
                            81129638414606681700187051655168)
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Code.joinWords 128
                            1298074214633706907132624082305024
                            26585857989912951165271504205840908288))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1298074214633706907132624082305024
                            128)
                          1298074214633706907132624082305024))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            5316993112778078098585158804324745216)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            4398046511104)
                          256))))
                  4096)))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          85070591730234615865843651857942052864
                          256)
                        (Nat.shiftLeft
                          85070591730234615865843651857942052864
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5316911983139663491615228241121378304
                          128)
                        256)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316993112778078098296924030126522368
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            81129638414606681695789005144064
                            128)
                          256))))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          85071889804449249572750784482024357888
                          256)
                        (Nat.shiftLeft
                          85071889804449249572750784482024357888
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          26584559915698317458076141205606891520
                          128)
                        256)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316993112778078098296924030126522368
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            81129638414606681695789005144064
                            128)
                          256)))))
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          333511611817409048235770840218465206272
                          128)
                        256)
                      512)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            34559927890407812695498983567288958976
                            128)
                          (Nat.shiftLeft
                            23928700072557753126659253085514235904
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            13333818332717437350066314573437206528
                            128)
                          (Nat.shiftLeft
                            2712975108584447436485896884134608896
                            128)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316911983139663491615228241121378304
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316911983139663491615228241121378304
                            128)
                          256)))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85071889804449249572750784482024357888
                            5316993112778078098585154406278234112)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85404196803395478545588422265521831936
                            81129638414606681695789005144064)
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316911983139663491903458617273090048
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            332306998946228968225951765070086144
                            21267647932558653966460912964485513216)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            81129638414606969930563203366912
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            332312069548629881143557751882907648
                            81129638414606681700187051655168)
                          256))))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            42535295865117307932921825928971026432
                            128)
                          (Code.joinWords 128
                            170141183460469231731687303715884105728
                            7975367974709495240161030935123329024))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            42701449364590422417034801811506069504
                            128)
                          (Code.joinWords 128
                            170141183460469231731687303715884105728
                            2834994084760015887636616392298463232)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85071889804449249572750784482024357888
                            5316993112778078098585154406278234112)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            333610143763263592662376394392600576
                            81129638414606681700187051655168)
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Nat.shiftLeft
                            288230376151711744
                            128))
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            332312069548629881143557751882907648
                            5070602400912917605986812821504)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            81129638414606969930563203366912)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            21599960002107283847604470716368420864
                            4398046511104)
                          256))))))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1298074214633706907132624082305024
                          128)
                        256)
                      512)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          1298074214633706907132624082305024
                          1298074214633706907132624082305024)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          1298074214633706907132624082305024
                          1298074214633706907132624082305024)
                        256))
                    2048)
                  4096))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          128)
                        (Code.joinWords 128
                          21268946006773287673368045588567818240
                          21268946006773287673368045588567818240))
                      (Code.joinWords 256
                        (Code.joinWords 128
                          21267647932558653966460912964485513216
                          1298074214633706907132624082305024)
                        (Code.joinWords 128
                          21268946006773287673368045588567818240
                          1298074214633706907132624082305024)))
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          128)
                        256))
                    (Code.joinWords 512
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          128)
                        (Code.joinWords 128
                          21268946006773287673368045588567818240
                          21269027136411702280049741377572962304))
                      (Code.joinWords 256
                        (Code.joinWords 128
                          21267647932558653966460912964485513216
                          1298074214633706907132624082305024)
                        (Code.joinWords 128
                          21268946006773287673368045588567818240
                          81129638414606681695789005144064))))
                  4096)))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          1298074214633706907132624082305024
                          1298074214633706907132624082305024)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          1298074214633706907132624082305024
                          1298074214633706907132624082305024)
                        256))
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          21267647932558653966460912964485513216
                          21267647932558653966460912964485513216)
                        256)
                      (Nat.shiftLeft
                        21267647932558653966460912964485513216
                        256))
                    2048)
                  4096))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          21267647932558653966460912964485513216
                          21267647932558653966460912964485513216)
                        256)
                      512)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          128)
                        (Code.joinWords 128
                          21268946006773287673368045588567818240
                          21268946006773287673368045588567818240))
                      (Code.joinWords 256
                        (Code.joinWords 128
                          21267647932558653966460912964485513216
                          1298074214633706907132624082305024)
                        (Code.joinWords 128
                          21268951077375688586285651575380639744
                          5070602400912917605986812821504)))
                    2048))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          21267647932558653966460912964485513216
                          21267647932558653966460912964485513216)
                        256)
                      512)
                    2048)
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          128)
                        256))
                    (Code.joinWords 512
                      (Code.joinWords 256
                        (Code.joinWords 128
                          21267647932558653966460912964485513216
                          21267647932558653966460912964485513216)
                        (Code.joinWords 128
                          21267647932558653966460912964485513216
                          81129638414606681695789005144064))
                      (Code.joinWords 256
                        21267647932558653966460912964485513216
                        (Code.joinWords 128
                          5070602400912917605986812821504
                          86200240815519599301775817965568))))))))))))

/-- The block word is computed from the verified profile data. -/
theorem word_eq :
    Code.profileWord 64 24 (fun i q => Data.profiles (1408 + i) q) = word := by
  decide +kernel

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage022
