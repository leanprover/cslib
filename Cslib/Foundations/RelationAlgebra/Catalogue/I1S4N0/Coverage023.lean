/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Cslib.Foundations.RelationAlgebra.FastCatalogueCoverage

/-!
# Profile coverage for models 1473–1536 of the ⟨1, 4, 0⟩ row

The balanced word contains exactly the cycle profiles of this block and its atom renamings.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage023

/-- The cycle profiles covered by this block of models. -/
def word : ℕ :=
  (Code.joinWords 524288
    (Code.joinWords 262144
      (Nat.shiftLeft
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
                            297747071055821155530452781502797185024
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
                            271162511140122838087076389480927592448
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            337627967411289362069954631549423976448
                            128)
                          256)
                        512))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            338292581478507066668144645918372659200
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            338292591624663930883729274522239500288
                            128)
                          256)
                        512))))
                8192)
              16384)
            32768)
          (Code.joinWords 32768
            (Code.joinWords 8192
              (Nat.shiftLeft
                (Code.joinWords 2048
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Code.joinWords 128
                        9223512774343131136
                        9223512774343131136)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          128)
                        256))
                    1024)
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Code.joinWords 128
                        12249931726620491776
                        12249940520599552000)
                      (Nat.shiftLeft
                        16908288
                        128))
                    1024))
                4096)
              (Nat.shiftLeft
                (Code.joinWords 2048
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Code.joinWords 128
                        11529355783556857856
                        12249977903592278016)
                      (Nat.shiftLeft
                        16908288
                        128))
                    1024)
                  (Nat.shiftLeft
                    (Code.joinWords 128
                      12249931723936137216
                      3026605866603249664)
                    1024))
                4096))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 128
                      32768
                      2048)
                    1024)
                  (Code.joinWords 2048
                    (Code.joinWords 128
                      32768
                      2048)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          1298074214633706907132624082305024
                          21268946006773287673368045588567818240)
                        256)
                      512)))
                8192)
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          128)
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          128))
                      512)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21268946006773287673368045588567818240
                            128)
                          (Code.joinWords 128
                            1298074214633706907132624082305024
                            21268946006773287673368045588567818240))
                        512)
                      10633823966279326983230456482242756608)
                    2048)
                  4096)))))
        131072)
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
                            256208696247195770145273072865737965568
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            320181697923088424628525581326685831168
                            128)
                          256)
                        512))
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            297747071055821155530452781502797185024
                            128)
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            330815521884415689239300654857243852800
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            330815684148644580842413463065495339008
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
                  (Nat.shiftLeft
                    536903680
                    1024)
                  2048)
                4096)
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          265845599156983174580761412056068915200
                          128)
                        256)
                      512)
                    2048)
                  4096)
                8192))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          1298074214633706907132624082305024
                          21268946006773287673368045588567818240)
                        256)
                      512)
                    2048)
                  4096)
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            332306999023600220681288032251281408
                            128)
                          256)
                        512)
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Nat.shiftLeft
                            21599954931582254187142200996736794624
                            128))
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            332306999023600220681288032251281408
                            128)
                          256)
                        512))
                    2048))
                (Code.joinWords 4096
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
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            255876389248172169924591784833486684160
                            272200970575206530765560059417830883328)
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
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            332306999023600220681288032251281408
                            128)
                          256)
                        512)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            332306999023600220681288032251281408
                            128)
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21268946006773287673368045588567818240
                            128)
                          (Code.joinWords 128
                            1298074214633706907132624082305024
                            21601253005796887894049333620819099648)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            332306999023600220681288032251281408
                            128)
                          256)))))))))
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      536903680
                      1024)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85071889804449249572750784482024357888
                            5316911983139663491615228241121378304)
                          256)
                        512)
                      1024)
                    2048)
                  4096))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          319014718988379809496913694467282698240
                          128)
                        (Nat.shiftLeft
                          319014718988379809496913694467282698240
                          128))
                      512)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316911983139663491903458617273090048
                            128)
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            212676479325586539664609129644855132160
                            332306999005650090111650018265244106752)
                          (Code.joinWords 128
                            297747071095435236787584950299569160192
                            338288524989158091618287910586303905792))
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85071889804449249577362470500451745792
                            5316911983139663491903458617273090048)
                          256)
                        512)))
                  4096)))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85071889804449249572750784482024357888
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            332306998946228968225951765070086144
                            128)
                          256))
                      1024)
                    2048)
                  4096)
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85071889804449249572750784482024357888
                            5316911983139663491615228241121378304)
                          256)
                        512)
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85071889804449249572750784482024357888
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            332306998946228968225951765070086144
                            128)
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85071889804449249572750784482024357888
                            85071889824256290201316868880410345472)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21268946006773287673368045588567818240
                            128)
                          (Code.joinWords 128
                            85071889804449249577362470500451745792
                            26918164988936551385952792238092189696)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85071889804449249572750784482024357888
                            85071889824256290201316868880410345472)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85071889804449249577362470500451745792
                            5649218982163263712584746649524371456)
                          256))))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            332306999023600220681288032251281408
                            128)
                          256)
                        512)
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            212676479325586539664609129644855132160
                            128)
                          (Nat.shiftLeft
                            297747071055821155539676153539651960832
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            319845486485745381931313631935240077312
                            128)
                          (Nat.shiftLeft
                            330811617450970937882806068979571884032
                            128)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85071889824256290201316868880410345472
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            332306999023600220681288032251281408
                            128)
                          256)))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5649218982163263712584746649524371456
                            128)
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            170141183460469231731687303715884105728
                            265845599216404296466459665251226877952)
                          (Code.joinWords 128
                            255876389228365129296025700435100696576
                            314736266439085898659196505071902785536))
                        512)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85071889804449249577362470500451745792
                            5649218982163263712584746649524371456)
                          256))))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            170141183460469231731687303715884105728
                            128)
                          (Nat.shiftLeft
                            265845599156983174590561244845227114496
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            255876389188596305547817917159248494592
                            128)
                          (Nat.shiftLeft
                            314736266376947111545742595272575287296
                            128)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85071889824256290201316868880410345472
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85070591730234615865843651857942052864
                            5649218982163263712584746649524371456)
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85071889804449249572750784482024357888
                            85071889824256290201316868880410345472)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21268946006773287673368045588567818240
                            128)
                          (Code.joinWords 128
                            85071889804449249577362470500451745792
                            26918164988936551385952792238092189696)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85071889804449249572750784482024357888
                            85071889824256290201316868880410345472)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85071889804449249577362470500451745792
                            5649305182404079232184048425342337024)
                          256))))))))
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Code.joinWords 128
                          297747071055821155530452781502797185024
                          337623910929368631717566993311207522304)
                        (Code.joinWords 128
                          297747071055821155530452781502797185024
                          337623910929368631717566993311207522304))
                      512)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            297747071055821155530452781502797185024
                            337623910988789753603265246506365485056)
                          (Code.joinWords 128
                            298411685113134735352602938228095320064
                            338288524990396031657573290861203030016))
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          35184372088832
                          128)
                        256))
                    2048)
                  4096))
              16384)
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85070591730234615865843651857942052864
                            85070591730234615865843651857942052864)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            332306998946228968225951765070086144
                            128)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85071889804449249572750784482024357888
                            85071889804449249572750784482024357888)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            332306998946228968225951765070086144
                            128)
                          256)))
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85070591730234615865843651857942052864
                            85070591730234615865843651857942052864)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            332306998946228968225951765070086144
                            128)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85071889804449249572750784482024357888
                            85071889804449249572750784482024357888)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            332306998946228968225951765070086144
                            128)
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85071889804449249572750784482024357888
                            85071889824256290201316868880410345472)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21268946006773287673368045588567818240
                            128)
                          (Code.joinWords 128
                            1298074214633706907132624082305024
                            21601253005796887894049333620819099648)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85071889804449249572750784482024357888
                            85071889824256290201316868880410345472)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            332306999023600220681288032251281408
                            128)
                          256))))
                  4096))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            265845599156983174580761412056068915200
                            128)
                          256)
                        512)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            332306999023600220681288032251281408
                            128)
                          256)))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85070591730234615865843651857942052864
                            85070591750041656494409736256328040448)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Nat.shiftLeft
                            21601253005796887894049333620819099648
                            128)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85071889804449249572750784482024357888
                            85071889824256290201316868880410345472)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            332312069626001133598894019064102912
                            128)
                          256)))
                    2048))
                (Code.joinWords 4096
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
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            255211775190703847597530955573826158592
                            271162511199543959958074893492348256256)
                          (Code.joinWords 128
                            298411685113289477857513610762457710592
                            314736266440323838698481885346801909760))
                        512)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            332306999023600220681288032251281408
                            128)
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
                          (Nat.shiftLeft
                            332306999023600220681288032251281408
                            128)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85071889804449249572750784482024357888
                            85071889824256290201316868880410345472)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            332306998946228968225951765070086144
                            332306999023600220681288032251281408)
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85071889804449249572750784482024357888
                            85071889824256290201316868880410345472)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21268946006773287673368045588567818240
                            128)
                          (Code.joinWords 128
                            21601253005719516641593997353637904384
                            21601253005796887894049333620819099648)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85071889804449249572750784482024357888
                            85071889824256290201316868880410345472)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            332306998946228968225951765070086144
                            332312069626001133598894019064102912)
                          256)))))))))))
    (Code.joinWords 262144
      (Code.joinWords 131072
        (Nat.shiftLeft
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          65536
                          128)
                        512)
                      1024)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          65536
                          128)
                        512)
                      1024)
                    2048)
                  4096))
              16384)
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 512
                  (Nat.shiftLeft
                    (Code.joinWords 128
                      32768
                      32768)
                    256)
                  (Nat.shiftLeft
                    (Code.joinWords 128
                      32768
                      170141183460469231731687303715884138496)
                    256))
                8192)
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          65536
                          128)
                        512)
                      1024)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          20769187434139310514121985316945920
                          128)
                        512)
                      1024)
                    2048)
                  4096))))
          65536)
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    536903680
                    1024)
                  2048)
                4096)
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316911983139663491903458617273090048
                            128)
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Nat.shiftLeft
                            26584559915698317458364371581758603264
                            128))
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316911983139663491903458617273090048
                            128)
                          256)
                        512)))
                  4096)
                8192))
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
                          21268946006773287673368045588567818240
                          128)
                        256))
                    2048)
                  4096)
                8192)
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          255876389188596305533982859103966330880
                          128)
                        256)
                      512)
                    2048)
                  4096)
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316911983139663491903458617273090048
                            128)
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316911983139663491903458617273090048
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85070591730234615865843651857942052864
                            5316911983139663491903458617273090048)
                          256)
                        512)))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            265845599156983174595172930863654502400
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            272200970511829803612838783742113742848
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
                            1298074214633706907132624082305024
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21268946006773287673368045588567818240
                            128)
                          (Code.joinWords 128
                            85070591730234615865843651857942052864
                            26585857989912951165271504205840908288)))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85070591730234615865843651857942052864
                            5316911983139663491903458617273090048)
                          256)
                        512)))))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          16777216
                          128)
                        (Nat.shiftLeft
                          65536
                          128))
                      1024)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 128
                        32768
                        2048)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          16777216
                          128)
                        (Nat.shiftLeft
                          65536
                          128)))
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          65536
                          128)
                        512)
                      1024))
                  4096))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128))
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          65536
                          128)
                        512))
                    2048)
                  4096)
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          65536
                          128)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          65536
                          128)
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          65536
                          128)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128))
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          65536
                          128)
                        512))))))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Code.joinWords 1024
                    (Code.joinWords 512
                      (Code.joinWords 256
                        (Code.joinWords 128
                          32768
                          34816)
                        (Code.joinWords 128
                          32768
                          34952))
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          395272
                          128)
                        (Code.joinWords 128
                          32896
                          34952)))
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        65540
                        128)
                      512))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          65536
                          128)
                        512)
                      1024)
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          1298074214633706907132624082305024
                          1298074214633706907132624082305024)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          1298074214633706907132624082305024
                          21268946006773287673368045588567818240)
                        256))))
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          65536
                          128)
                        512)
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Nat.shiftLeft
                            21268946006773287673368045588567818240
                            128))
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          65536
                          128)
                        512))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          65536
                          128)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          65536
                          128)
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          65536
                          128)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1298074214633706907132624082305024
                            1298074214633706907132624082305024)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21268946006773287673368045588567818240
                            128)
                          (Code.joinWords 128
                            21268946006773287673368045588567818240
                            21268946006773287673368045588567818240)))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          65536
                          128)
                        512)))))))))
      (Code.joinWords 131072
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 4096
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      39614685720041976111359328256
                      (Code.joinWords 256
                        39614685720041976111359328256
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          128)))
                    1024)
                  2048)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      49711634165463358981189697536
                      (Code.joinWords 128
                        49711636526646600413866885120
                        1179648))
                    1024)
                  2048))
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          128)
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          128))
                      512)
                    2048)
                  4096)
                8192))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        49518206034325018310552354816
                        (Code.joinWords 128
                          49711788232669862600690925696
                          1179648))
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        49711634165463358978505342976
                        10097706975537693803910529024)
                      1024)
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        32768
                        128)
                      1024)
                    (Code.joinWords 512
                      32768
                      128))
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1298074214633706907132624082305024
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          21268946006773287673368045588567818240
                          128)
                        256))
                    2048)))
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1298074214633706907132624082305024
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21268946006773287673368045588567818240
                            128)
                          (Nat.shiftLeft
                            21268946006773287673368045588567818240
                            128)))
                      664613997892457936451903530140172288)
                    2048)
                  4096)
                8192)))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        1048576
                        65536)
                      512)
                    1024)
                  2048)
                4096)
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128))
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          65536
                          128)
                        512))
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          65536
                          128)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Nat.shiftLeft
                            21268946006773287673368045588567818240
                            128))
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          65536
                          128)
                        512)))
                  4096)))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        32768
                        128)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          1048576
                          65536)
                        512))
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          65536
                          128)
                        512)
                      1024)
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          32768
                          (Code.joinWords 128
                            32768
                            34816))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            32896
                            393352)
                          (Code.joinWords 128
                            34952
                            34952)))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          65540
                          128)
                        512))
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          65536
                          128)
                        512)
                      1024))
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
                          21268946006773287673368045588567818240)
                        256))
                    2048)))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          65536
                          128)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          65536
                          128)
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          65536
                          128)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128))
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          65536
                          128)
                        512))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          65536
                          128)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          65536
                          128)
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          65536
                          128)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1298074214633706907132624082305024
                            21268946006773287673368045588567818240)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21268946006773287673368045588567818240
                            128)
                          (Code.joinWords 128
                            1298074214633706907132624082305024
                            21268946006773287673368045588567818240)))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          65536
                          128)
                        512))))))))
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          85070591730234615865843651857942052864
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85070591730234615865843651857942052864
                            5316911983139663491615228241121378304)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          85071889804449249572750784482024357888
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85071889804449249572750784482024357888
                            5316911983139663491615228241121378304)
                          256)))
                    2048)
                  4096)
                8192)
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          297747071055821155530452781502797185024
                          128)
                        (Nat.shiftLeft
                          297747071055821155530452781502797185024
                          128))
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          320177793484691610885704525645027999744
                          128)
                        (Nat.shiftLeft
                          320177793484691610885704525645027999744
                          128)))
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            255876389188596305533982859103966330880
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85070591730234615865843651857942052864
                            5316911983139663491903458617273090048)
                          256)
                        512))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          85070591730234615865843651857942052864
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Code.joinWords 128
                            85070591730234615870455337876369440768
                            26585857989912951165271504205840908288)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          85071889804449249572750784482024357888
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85071889804449249577362470500451745792
                            5316993112778078098585154406278234112)
                          256))))
                  4096)))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          85070591730234615865843651857942052864
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85070591730234615865843651857942052864
                            5316911983139663491615228241121378304)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          85071889804449249572750784482024357888
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85071889804449249572750784482024357888
                            5316911983139663491615228241121378304)
                          256)))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85071889804449249572750784482024357888
                            1298074214633706907132624082305024)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21268946006773287673368045588567818240
                            128)
                          (Code.joinWords 128
                            85071889804449249577362470500451745792
                            26585857989912951165271504205840908288)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          85071889804449249572750784482024357888
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85071889804449249577362470500451745792
                            5316911983139663491903458617273090048)
                          256)))
                    2048))
                8192)
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            297747071055821155530452781502797185024
                            128)
                          (Nat.shiftLeft
                            308380895022100482527518296040322105344
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            320177793484691610899539583700310163456
                            128)
                          (Nat.shiftLeft
                            330811617450970937882824083378081366016
                            128)))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          151115727451828646838272
                          256)
                        512))
                    2048)
                  4096)
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316911983139663491903458617273090048
                            128)
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          85070591730234615865843651857942052864
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85070591730234615870455337876369440768
                            5316911983139663491903458617273090048)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85071889804449249572750784482024357888
                            5316911983139663491615228241121378304)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85071889804449249577362470500451745792
                            5316911983139663491903458617273090048)
                          256))))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            255211775190703847597530955573826158592
                            128)
                          (Nat.shiftLeft
                            308380895022100482528094756792625528832
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            256208696187542534516043868924318580736
                            128)
                          (Nat.shiftLeft
                            314736266376947111545760609671084769280
                            128)))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85070591730234615865843651857942052864
                            5316911983139663491903458617273090048)
                          256)
                        512))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85071889804449249572750784482024357888
                            26585857989912951164983273829689196544)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21268946006773287673368045588567818240
                            128)
                          (Code.joinWords 128
                            85071889804449249577362470500451745792
                            26585857989912951165271504205840908288)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85071889804449249572750784482024357888
                            5316911983139663491615228241121378304)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85071889804449249577362470500451745792
                            5316993112778078098585154406278234112)
                          256))))))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        65536
                        128)
                      512)
                    1024)
                  2048)
                4096)
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128))
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          65536
                          128)
                        512))
                    2048)
                  4096)
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          65536
                          128)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            65536
                            128)
                          (Nat.shiftLeft
                            4503599627370496
                            128))
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          65536
                          128)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Nat.shiftLeft
                            21268946006773287673368045588567818240
                            128))
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          65536
                          128)
                        512))))))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Code.joinWords 1024
                    (Code.joinWords 512
                      (Code.joinWords 256
                        32768
                        (Code.joinWords 128
                          32768
                          34952))
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          8
                          128)
                        (Code.joinWords 128
                          34952
                          2184)))
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        65536
                        128)
                      512))
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          1298074214633706907132624082305024
                          1298074214633706907132624082305024)
                        256)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          21268946006773287673368045588567818240
                          128)
                        (Code.joinWords 128
                          1298074214633706907132624082305024
                          21268946006773287673368045588567818240)))
                    2048))
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          65536
                          128)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          65536
                          128)
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            65536
                            128)
                          (Nat.shiftLeft
                            309485009821345068724781056
                            128))
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Nat.shiftLeft
                            21268946006773287673368045588567818240
                            128))
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          65536
                          128)
                        512))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          65536
                          128)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          549755813888
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          65536
                          128)
                        512)))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          37778931862957161709568
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          65536
                          128)
                        512))
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          1298074214633706907132624082305024
                          21268946006773287673368045588567818240)
                        256)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          21268946006773287673368045588567818240
                          128)
                        (Code.joinWords 128
                          21268946006773287673368045588567818240
                          21268946006773287673368045588567818240))))))))))))

/-- The block word is computed from the verified profile data. -/
theorem word_eq :
    Code.profileWord 64 24 (fun i q => Data.profiles (1472 + i) q) = word := by
  decide +kernel

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage023
