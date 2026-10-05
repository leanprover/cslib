/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Cslib.Foundations.RelationAlgebra.FastCatalogueCoverage

/-!
# Profile coverage for models 2369–2432 of the ⟨1, 4, 0⟩ row

The balanced word contains exactly the cycle profiles of this block and its atom renamings.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage037

/-- The cycle profiles covered by this block of models. -/
def word : ℕ :=
  (Code.joinWords 524288
    (Nat.shiftLeft
      (Code.joinWords 131072
        (Nat.shiftLeft
          (Nat.shiftLeft
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            308380895022100482513683237985039941632
                            128)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            311874874736087942996770147148702416896
                            311926798400560652013505620469310554112)
                          256)
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            311873579197174509760733477063100465152
                            3545906010155634372886061396967555072)
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            53999887328762207337293622576192421888
                            2710378960155180022092919083852890112)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            14124561030031403656228913019485159424
                            51926296177845429518353515212177408)
                          256)
                        512))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            311874874785798972699323698812620374016
                            311926798408016661718289788922650165248)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            14123909457816314476734308441611304960
                            218776845063448398684386965835481088)
                          256)
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            3532275438813783425165041175829151744
                            51926296168173875387483892138115072)
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            3530761863958425292887870790535479296
                            51922968595019682842221996689850368)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            3530815739147620619009217722088161280
                            51926296177845429518353515212177408)
                          256)
                        512)))))
              16384)
            32768)
          65536)
        (Code.joinWords 65536
          (Nat.shiftLeft
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            43258576732788328326074996883456
                            128)
                          256)
                        512)
                      1024)
                    2048)
                  4096)
                8192)
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            649037107316853453566312041152512
                            128)
                          (Nat.shiftLeft
                            2835816156174263891944521607782858752
                            128))
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            649037107316853453566312041152512
                            128)
                          (Nat.shiftLeft
                            176591968379381826530510053492916224
                            128))
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            649037107316853453566312041152512
                            128)
                          (Nat.shiftLeft
                            2669046578509438488486542311658881024
                            128))
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            158456325028528675187087900672
                            128)
                          256)
                        512)
                      1024)))
                8192))
            32768)
          (Nat.shiftLeft
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          53221676625282097307138335726108672
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
                          (Code.joinWords 128
                            1300609515834163365935617488715776
                            2693757525484987478180494311424)
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          2710378960155180022092919083852890112
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            51926296168173875387483892138115072
                            2693757525484987478180494311424)
                          256)
                        512)))
                  4096))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            212679075474015807078423394893019742208
                            297751614315572373504627745687085252608)
                          (Code.joinWords 128
                            311925500264283957680263020236263915520
                            3545903316398108873486914875306278912))
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            689601926524156794414206543724544
                            128)
                          (Code.joinWords 128
                            220074919229722564049740398430519296
                            176591968340696347876794509578731520))
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1298074214633706907132624082305024
                            128)
                          (Code.joinWords 128
                            53224370382807586906302534647808000
                            2693757525484987478180494311424))
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            42535295865117307932921825928971026432
                            2658455991569831745807614120560689152)
                          (Code.joinWords 128
                            45401443731028532784447120655003942912
                            2668840585286901401064675113219129344))
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            53224370382807582294616516220420096
                            158456325028528675187087900672)
                          256)
                        512))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            689601926524156794414206543724544
                            128)
                          (Code.joinWords 128
                            220074919268408190277408532021116928
                            177238470185495862342031937305051136))
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            689601926524156794414206543724544
                            128)
                          (Code.joinWords 128
                            218130343247658086375512589304070144
                            176591968379381974104462643169329152))
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            11685995514528961266372545586659328
                            2693757525484987478180494311424)
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10384593717069655257060992658440192
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            10384752173394683785736179746340864
                            158456325028528675187087900672)
                          256)
                        512))))))
            32768)))
      262144)
    (Code.joinWords 262144
      (Code.joinWords 131072
        (Nat.shiftLeft
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85070591730234615865843651857942052864
                            1298074214633706907132624082305024)
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85071889804449249572750784482024357888
                            1298074214633706907132624082305024)
                          256))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85071889804449249572750784482024357888
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85070591730234615865843651857942052864
                            1298074214633706907132624082305024)
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            266510213154875632517213315586209087488
                            128)
                          256)
                        512)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85071889824256290201316868880410345472
                            128)
                          256)
                        (Nat.shiftLeft
                          85071889804449249577362470500451745792
                          256)))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85071889804449249572750784482024357888
                            1298074214633706907132624082305024)
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85070591750041656494409736256328040448
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85071889804449249572750784482024357888
                            1298074214633706907132624082305024)
                          256))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85071889804449249572750784482024357888
                            128)
                          256)
                        (Nat.shiftLeft
                          85071889804449249577362470500451745792
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            226674911695810516208259516545204486144
                            311745503446006915207579925335894917120)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            311922041519390058718383877812702412800
                            45411828384321466829736646624879312896)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85071889824256290201316868880410345472
                            128)
                          256)
                        (Nat.shiftLeft
                          85071889804449249577362470500451745792
                          256))))))
              16384)
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85071889804449249572750784482024357888
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85070591730234615865843651857942052864
                            1298074214633706907132624082305024)
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85071889824256290201316868880410345472
                            128)
                          256)
                        (Nat.shiftLeft
                          85071889804449249572750784482024357888
                          256))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85071889804449249572750784482024357888
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85070591730234615870455337876369440768
                            1298074214633706907132624082305024)
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            224182609164099717698656081547261640704
                            311922041479621234966140869270726246400)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            309253200894334333569687880175934504960
                            45411828324745602453539239702944546816)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85071889824256290201316868880410345472
                            128)
                          256)
                        (Nat.shiftLeft
                          85071889804449249577362470500451745792
                          256)))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85071889804449249572750784482024357888
                            128)
                          256)
                        (Nat.shiftLeft
                          85071889804449249572750784482024357888
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85070591730234615865843651857942052864
                            1298094021674335473217022468292608)
                          256)
                        (Nat.shiftLeft
                          1298074214633706907132624082305024
                          256))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85070591730234615865843651857942052864
                            1298074214633706907132624082305024)
                          256)
                        (Nat.shiftLeft
                          1298074214633711518818642509692928
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            87905585814994631751021302853696225280
                            176538112997224767936121273579470848)
                          256)
                        (Nat.shiftLeft
                          2668840585286901405676361131646517248
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85070591730234615865843651857942052864
                            1298094021674335473217022468292608)
                          256)
                        (Nat.shiftLeft
                          1298074214633711518818642509692928
                          256))))))
              16384))
          65536)
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            298411685053713613466904685032937357312
                            128)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            311873579256750978599840550562134228992
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            13515116038118974619954920486833487872
                            128)
                          256))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            311874836706569936149888102247606255616
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            311926760308980584554738057481365225472
                            128)
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            56492189821013667103322472596277035008
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            218076468058462760398280845827244032
                            128)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            14124561030224831786646677747058868224
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            51964325686180722271780627407699968
                            128)
                          256)))))
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
                            311874836706569936162137893234054004736
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            311926760308980584557149584964125196288
                            128)
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            13501485407200652471943594127931736064
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            51964325686180722269528793234276352
                            128)
                          256))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            14123871428104879499434498812941434880
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            2711193425665826659629756534004645888
                            128)
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            13499971832345294339666423742638063616
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            51922968585348276287556763105886208
                            128)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            13500177825606517053315950278575390720
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            51964325686180722271780627407699968
                            128)
                          256)))))
                8192)
              16384))
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Code.joinWords 8192
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
                          (Code.joinWords 128
                            85070591730234615865843651857942052864
                            1298074214633706907132624082305024)
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85070591730234615865843651857942052864
                            85070591730234615865843651857942052864)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1298074214633706907132624082305024
                            128)
                          (Code.joinWords 128
                            1298074214633706907132624082305024
                            1298074214633706907132624082305024)))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85070591730234615865843651857942052864
                            1298074214633706907132624082305024)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85070591730234615865843651857942052864
                            1298074214633706907132624082305024)
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            309087047394861219071163385485813874688
                            311745503386431050816970999606374563840)
                          256)
                        (Code.joinWords 256
                          (Code.joinWords 128
                            213507246822952112085174009057530347520
                            298577838553186727951017660915472400384)
                          (Code.joinWords 128
                            309253200894334333555276361368348917760
                            311922041479621234956341036481568047104)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85071889804449249572750784482024357888
                            1298074214633706907132624082305024)
                          256)
                        (Nat.shiftLeft
                          1298074214633706907132624082305024
                          256)))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85070591730234615865843651857942052864
                            85070591750041656494409736256328040448)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1298074214633706907132624082305024
                            128)
                          (Code.joinWords 128
                            1298074214633706907132624082305024
                            1298074214633706907132624082305024)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85070591730234615865843651857942052864
                            85070591750041656494409736256328040448)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1298074214633706907132624082305024
                            128)
                          (Code.joinWords 128
                            1298074214633706907132624082305024
                            1298074214633706907132624082305024)))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85071889804449249572750784482024357888
                            1298074214633706907132624082305024)
                          256)
                        (Nat.shiftLeft
                          1298074214633706907132624082305024
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            130970495959682492102053239408247701504
                            45899904229612290147677177118065688576)
                          256)
                        (Code.joinWords 256
                          (Code.joinWords 128
                            166153499473114484112975882535043072
                            166153499473114484112975882535043072)
                          (Code.joinWords 128
                            2834994084760015885177650995754172416
                            176538093190184139370036875193483264)))
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          85071889804449249572750784482024357888
                          1298074214633706907132624082305024)
                        256)))))
              16384)
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85071889804449249572750784482024357888
                            1298074214633706907132624082305024)
                          256)
                        (Nat.shiftLeft
                          1298074214633706907132624082305024
                          256))
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          85071889804449249572750784482024357888
                          256)
                        (Nat.shiftLeft
                          1298074214633706907132624082305024
                          256))
                      1024)
                    2048))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          85071889804449249572750784482024357888
                          1298074214633706907132624082305024)
                        256)
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          85236745229707730349956627740477095936
                          176538093190184139370036875193483264)
                        256)
                      (Nat.shiftLeft
                        85071889804449249572750784482024357888
                        256))
                    2048)))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85070591730234615865843651857942052864
                            1298074214633706907132624082305024)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85070591730234615870455337876369440768
                            1298074214633706907132624082305024)
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85071889804449249572750784482024357888
                            1298074214633706907132624082305024)
                          256)
                        (Nat.shiftLeft
                          1298074214633706907132624082305024
                          256))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85070591730234615865843651857942052864
                            1298074214633706907132624082305024)
                          256)
                        (Nat.shiftLeft
                          1298074214633711518818642509692928
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            138447403435972643887137154122324639744
                            2834994084760015885177650995754172416)
                          256)
                        (Code.joinWords 256
                          42701449364590422417034801811506069504
                          (Code.joinWords 128
                            45401443731028532784449372454817628160
                            2668840585286901401064675113219129344)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          85071889804449249572750784482024357888
                          256)
                        (Nat.shiftLeft
                          1298074214633706907132624082305024
                          256)))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85071889804449249572750784482024357888
                            1298074214633706907132624082305024)
                          256)
                        (Nat.shiftLeft
                          1298074214633706907132624082305024
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          85071889804449249572750784482024357888
                          1298074214633706907132624082305024)
                        256)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          85071889804449249572750784482024357888
                          256)
                        (Nat.shiftLeft
                          1298074214633706907132624082305024
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            87905585814994631751021302853696225280
                            176538093190184139370036875193483264)
                          256)
                        (Nat.shiftLeft
                          10384593717069655257060992658440192
                          256))
                      (Nat.shiftLeft
                        85071889804449249572750784482024357888
                        256)))))))))
      (Code.joinWords 131072
        (Nat.shiftLeft
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85071889804449249572750784482024357888
                            1298074214633706907132624082305024)
                          256)
                        (Nat.shiftLeft
                          1298074214633706907132624082305024
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          85071889804449249572750784482024357888
                          1298074214633706907132624082305024)
                        256)
                      1024))
                  4096)
                8192)
              (Code.joinWords 8192
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
                          (Code.joinWords 128
                            85070591730234615865843651857942052864
                            1298074214633706907132624082305024)
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85070591730234615865843651857942052864
                            85070591730234615865843651857942052864)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1298074214633706907132624082305024
                            1298074214633706907132624082305024)
                          256))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85070591730234615865843651857942052864
                            1298074214633706907132624082305024)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1298074214633706907132624082305024
                            128)
                          (Code.joinWords 128
                            85070591730234615865843651857942052864
                            1298074214633706907132624082305024)))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            225968759283435698393647200247658577920
                            128)
                          (Code.joinWords 128
                            309087047394861219071163385485813874688
                            311745503386431050816970999606374563840))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            311039351013670314259490852105600630784
                            128)
                          (Code.joinWords 128
                            309253200894334333555276361368348917760
                            311922041479621234956341036481568047104)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85071889804449249572750784482024357888
                            1298074214633706907132624082305024)
                          256)
                        (Nat.shiftLeft
                          1298074214633706907132624082305024
                          256)))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85070591730234615865843651857942052864
                            85070591750041656494409736256328040448)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1298074214633706907132624082305024
                            1298074214633706907132624082305024)
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85070591730234615865843651857942052864
                            1298094021674335473217022468292608)
                          256)
                        (Nat.shiftLeft
                          1298074214633706907132624082305024
                          256))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85071889804449249572750784482024357888
                            1298074214633706907132624082305024)
                          256)
                        (Nat.shiftLeft
                          1298074214633706907132624082305024
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            45193751856687139678729440049531715584
                            128)
                          (Code.joinWords 128
                            130970495959682492102053239408247701504
                            45401443731192946695338249470460559360))
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2834994084760015885177650995754172416
                            176538093190184139370036875193483264)
                          256))
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          85071889804449249572750784482024357888
                          1298074214633706907132624082305024)
                        256))))))
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
                          1298074214633706907132624082305024
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          87729047721804447611651265978502742016
                          256)
                        (Nat.shiftLeft
                          2668840585286901401064675113219129344
                          256))
                      (Nat.shiftLeft
                        85071889804449249572750784482024357888
                        256)))
                  4096)
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85070591730234615865843651857942052864
                            1298074214633706907132624082305024)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1298074214633706907132624082305024
                            128)
                          (Code.joinWords 128
                            85070591730234615870455337876369440768
                            1298074214633706907132624082305024)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85071889804449249572750784482024357888
                            1298074214633706907132624082305024)
                          256)
                        (Nat.shiftLeft
                          1298074214633706907132624082305024
                          256))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85070591730234615865843651857942052864
                            1298074214633706907132624082305024)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1298074214633706907132624082305024
                            128)
                          (Code.joinWords 128
                            85070591730234615870455337876369440768
                            1298074214633706907132624082305024)))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            2658455991569831745807614120560689152
                            128)
                          (Code.joinWords 128
                            138447403435972643887137154122324639744
                            2834994084760015885177650995754172416))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            2658455991569831745807614120560689152
                            128)
                          (Code.joinWords 128
                            53376811705738028021872214816499695616
                            2668840585286901401064675113219129344)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          85071889804449249572750784482024357888
                          256)
                        (Nat.shiftLeft
                          1298074214633706907132624082305024
                          256)))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85071889804449249572750784482024357888
                            1298074214633706907132624082305024)
                          256)
                        (Nat.shiftLeft
                          1298074214633706907132624082305024
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          85071889804449249572750784482024357888
                          1298074214633706907132624082305024)
                        256)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          85071889804449249572750784482024357888
                          256)
                        (Nat.shiftLeft
                          1298074214633706907132624082305024
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            87905585814994631751021302853696225280
                            10384593717069655257060992658440192)
                          256)
                        (Nat.shiftLeft
                          2668840585286901401064675113219129344
                          256))
                      (Nat.shiftLeft
                        85071889804449249572750784482024357888
                        256)))))))
          65536)
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          53221676625282097307138335726108672
                          128)
                        256)
                      1024)
                    2048)
                  4096)
                8192)
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            212679075474015807078423394893019742208
                            128)
                          (Nat.shiftLeft
                            311925462234765950833380975335167754240
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            297751614315572373504627745687085252608
                            128)
                          (Nat.shiftLeft
                            13515075255266971073383422926312701952
                            128)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            53262419707855057742745815702568960
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1298074214633706907132624082305024
                            128)
                          (Nat.shiftLeft
                            40723275532331869523081590472704
                            128)))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            2712491499880460366390513339744649216
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            651572408517309912369305447563264
                            128)
                          (Nat.shiftLeft
                            2669046578509438488342427157942763520
                            128)))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            42535295865117307932921825928971026432
                            128)
                          (Nat.shiftLeft
                            45401443731183275288781332437062909952
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            166153499473114484112975882535043072
                            128)
                          (Nat.shiftLeft
                            176538093190184139370036875193483264
                            128)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            53262399900814429176661417316581376
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            158456325028528675187087900672
                            128)
                          256)))))
                8192))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1338639033841010247980518584877056
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            40723275532331869523081590472704
                            128)
                          256))
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          218076468058462760398280845827244032
                          128)
                        256)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            51964325686180722269528793234276352
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            40723275532331869523081590472704
                            128)
                          256)))
                    2048))
                8192)
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            2712491499880460366534628527820505088
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            651572408517309912369305447563264
                            128)
                          (Nat.shiftLeft
                            2669655050797548038599251933104439296
                            128)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            11724025032535808148417446682820608
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            40723275532331869523081590472704
                            128)
                          256))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            2710584953377717109514777486199619584
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            651572408517309912369305447563264
                            128)
                          (Nat.shiftLeft
                            2669046578509438488486542346018619392
                            128)))
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10384593717069655257060992658440192
                          128)
                        256)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            10384752173394683785736179746340864
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            158456325028528675187087900672
                            128)
                          256)))))
                8192)))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1298074214633706907132624082305024
                            1298074214633706907132624082305024)
                          256)
                        (Nat.shiftLeft
                          1298074214633706907132624082305024
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          1298074214633706907132624082305024
                          1298074214633706907132624082305024)
                        256)
                      1024))
                  4096)
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85070591730234615865843651857942052864
                            85070591730234615865843651857942052864)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1298074214633706907132624082305024
                            128)
                          (Code.joinWords 128
                            85070591730234615865843651857942052864
                            1298074214633706907132624082305024)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85070591730234615865843651857942052864
                            1298074214633706907132624082305024)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1298074214633706907132624082305024
                            128)
                          1298074214633706907132624082305024))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85070591730234615865843651857942052864
                            1298074214633706907132624082305024)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1298074214633706907132624082305024
                            128)
                          1298074214633706907132624082305024))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            45193751856687139678729440049531715584
                            128)
                          (Code.joinWords 128
                            53875272204157371473632429911987716096
                            45899904229447876236209587550305648640))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            42701449364590422417034801811506069504
                            2824609491042946229920590003095732224)
                          (Code.joinWords 128
                            53376811705738028021293502264382586880
                            2834994084760015885177650995754172416)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1298074214633706907132624082305024
                            1298074214633706907132624082305024)
                          256)
                        (Nat.shiftLeft
                          1298074214633706907132624082305024
                          256)))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85070591730234615865843651857942052864
                            85070591750041656494409736256328040448)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1298074214633706907132624082305024
                            128)
                          (Code.joinWords 128
                            1298074214633706907132624082305024
                            1298074214633706907132624082305024)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85070591730234615865843651857942052864
                            1298094021674335473217022468292608)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1298074214633706907132624082305024
                            128)
                          1298074214633706907132624082305024))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1298074214633706907132624082305024
                            1298074214633706907132624082305024)
                          256)
                        (Nat.shiftLeft
                          1298074214633706907132624082305024
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            45193751856687139678729440049531715584
                            128)
                          (Code.joinWords 128
                            45401443731028532783870659902700519424
                            45401443731192946695338249470460559360))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            166153499473114484112975882535043072
                            166153499473114484112975882535043072)
                          (Code.joinWords 128
                            2834994084760015885177650995754172416
                            176538093190184139370036875193483264)))
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          1298074214633706907132624082305024
                          1298074214633706907132624082305024)
                        256))))))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1298074214633706907132624082305024
                            1298074214633706907132624082305024)
                          256)
                        (Nat.shiftLeft
                          1298074214633706907132624082305024
                          256))
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          1298074214633706907132624082305024
                          256)
                        (Nat.shiftLeft
                          1298074214633706907132624082305024
                          256))
                      1024)
                    2048))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          1298074214633706907132624082305024
                          1298074214633706907132624082305024)
                        256)
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          1298074214633706907132624082305024
                          256)
                        (Nat.shiftLeft
                          1298074214633706907132624082305024
                          256))
                      1024)
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          2834994084760015885177650995754172416
                          176538093190184139370036875193483264)
                        256)
                      (Nat.shiftLeft
                        2668840585286901401064675113219129344
                        256)))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85070591730234615865843651857942052864
                            1298074214633706907132624082305024)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1298074214633706907132624082305024
                            128)
                          (Code.joinWords 128
                            85070591730234615870455337876369440768
                            1298074214633706907132624082305024)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1298074214633706907132624082305024
                            1298074214633706907132624082305024)
                          256)
                        (Nat.shiftLeft
                          1298074214633706907132624082305024
                          256))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85070591730234615865843651857942052864
                            1298074214633706907132624082305024)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1298074214633706907132624082305024
                            128)
                          1298074214633711518818642509692928))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            2658455991569831745807614120560689152
                            128)
                          (Code.joinWords 128
                            45401443731028532783870659902700519424
                            2834994084760015885177650995754172416))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            42701449364590422417034801811506069504
                            2658455991569831745807614120560689152)
                          (Code.joinWords 128
                            45401443731028532784449372454817628160
                            2668840585286901401064675113219129344)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          1298074214633706907132624082305024
                          256)
                        (Nat.shiftLeft
                          1298074214633706907132624082305024
                          256)))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1298074214633706907132624082305024
                            1298074214633706907132624082305024)
                          256)
                        (Nat.shiftLeft
                          1298074214633706907132624082305024
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          1298074214633706907132624082305024
                          1298074214633706907132624082305024)
                        256)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          1298074214633706907132624082305024
                          256)
                        (Nat.shiftLeft
                          1298074214633706907132624082305024
                          256))
                      1024)
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          10384593717069655257060992658440192
                          10384593717069655257060992658440192)
                        256)
                      (Nat.shiftLeft
                        10384593717069655257060992658440192
                        256)))))))))))

/-- The block word is computed from the verified profile data. -/
theorem word_eq :
    Code.profileWord 64 24 (fun i q => Data.profiles (2368 + i) q) = word := by
  decide +kernel

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage037
