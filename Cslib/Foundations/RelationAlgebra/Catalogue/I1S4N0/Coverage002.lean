/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Cslib.Foundations.RelationAlgebra.FastCatalogueCoverage

/-!
# Profile coverage for models 129–192 of the ⟨1, 4, 0⟩ row

The balanced word contains exactly the cycle profiles of this block and its atom renamings.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage002

/-- The cycle profiles covered by this block of models. -/
def word : ℕ :=
  (Code.joinWords 524288
    (Code.joinWords 262144
      (Code.joinWords 131072
        (Code.joinWords 32768
          (Nat.shiftLeft
            (Nat.shiftLeft
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          256212605621993638375518295863236493312
                          128)
                        256)
                      512)
                    1024)
                  2048)
                4096)
              8192)
            16384)
          (Code.joinWords 16384
            (Nat.shiftLeft
              (Code.joinWords 4096
                (Code.joinWords 2048
                  (Code.joinWords 1024
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170141183460469231731687303715884138504
                          128)
                        256)
                      512)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170141183460469231731687303715884138504
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
                      512))))
              8192)
            (Code.joinWords 8192
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          271166648811104011593206089703491633152
                          128)
                        256)
                      512)
                    1024)
                  2048)
                4096)
              (Code.joinWords 4096
                (Code.joinWords 2048
                  (Code.joinWords 1024
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          297747071055821155530452781502798102528
                          128)
                        256)
                      512)
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          196608
                          128)
                        (Nat.shiftLeft
                          317575413918898775209816220435812892684
                          128))
                      512))
                  (Code.joinWords 1024
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          212676479325586539664609129644855132160
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          317571260531302568999757188817244651520
                          128)
                        256))
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          212676479325586539664609129644855132160
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5701228794912586303856779752095350784
                          128)
                        256))))
                (Code.joinWords 2048
                  (Code.joinWords 1024
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          212676479325586539664609129644855132160
                          317571260461707127433331923868786360320)
                        256)
                      512)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          212676479325586539664609129644855132160
                          5701228784737356373155361119769985024)
                        256)
                      512))
                  (Code.joinWords 1024
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          212676479325586539676138344690923601920
                          128)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          212676479375104141236024340640820101120
                          5721911138221436925755956919800037376)
                        256))
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          212676479325586539676138344690923601920
                          128)
                        256)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          272221739699263942908596861548351389696
                          128)
                        (Code.joinWords 128
                          212676479375104141236024340640820101120
                          5721998289200206158302185164518850560)))))))))
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Code.joinWords 512
                    (Nat.shiftLeft
                      9367487224930631680
                      128)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        170141183460469231731687303715884105728
                        128)
                      256))
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      4398046511104
                      1024)
                    (Nat.shiftLeft
                      288230376151711744
                      1024))
                  4096))
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 256
                    (Nat.shiftLeft
                      216735732067205120
                      128)
                    (Nat.shiftLeft
                      255876389188596305533982859103966330880
                      128))
                  512)
                4096))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        170141183460469231731687303715884105728
                        128)
                      256)
                    512)
                  4096)
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      4398046511104
                      256)
                    1024)
                  (Code.joinWords 1024
                    (Nat.shiftLeft
                      4398046511104
                      256)
                    (Nat.shiftLeft
                      4398046511104
                      256))))
              (Code.joinWords 8192
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
                        (Code.joinWords 128
                          170805797458361689668139207246024278016
                          338506601395319552429155207467744886784)
                        256)
                      512)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5316911983139663491615228241121378304
                          256)
                        512)
                      1024)))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5316993112778078098585154406278234112
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          5316911983139663491615228241121378304
                          256)
                        (Nat.shiftLeft
                          5316993112778078098585154406278234112
                          256))
                      1024))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5316911983139663491903458617273090048
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5316993112778078098585154406278234112
                          256)
                        512))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          5316911983139663491615228241121378304
                          256)
                        (Nat.shiftLeft
                          5316993112778078098585154406278234112
                          256))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          5316911983139663491615228241121378304
                          5316911983139663491615228241121378304)
                        (Code.joinWords 256
                          5316911983139663491615228241121378304
                          5316993112778078098585154406278234112))))))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    17592186044416
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      17592186044416
                      128)
                    2048)
                  4096))
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 256
                      (Code.joinWords 128
                        255211775190703847597530955573826158592
                        255211775190703847597530955573826158592)
                      (Code.joinWords 128
                        256208696187542534502208810869036417024
                        256208696187542534502208810869036417024))
                    512)
                  2048)
                8192))
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
                  4096))
              (Code.joinWords 8192
                (Code.joinWords 4096
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
                (Code.joinWords 4096
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
                    2048)))))))
      (Code.joinWords 131072
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 256
                      39652766883359836930362572800
                      (Nat.shiftLeft
                        170141183460469231731687303715884105728
                        128))
                    512)
                  2048)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        170141183460469231731687303715884105728
                        128)
                      256)
                    512)
                  2048))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 256
                      (Nat.shiftLeft
                        60446290980731458735308800
                        128)
                      (Nat.shiftLeft
                        265845599156983174580761412056068915200
                        128))
                    512)
                  2048)
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          180775007426748558714917760198126862336
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          333521996473264905019219840791021092864
                          128)
                        256))
                    2048)
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
                      1024)))))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      1180591620717411303424
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      77371252455336267181195264
                      1024)
                    2048))
                (Code.joinWords 2048
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      1180591620717411303424
                      256)
                    1024)
                  (Code.joinWords 1024
                    (Nat.shiftLeft
                      1180591620717411303424
                      256)
                    (Nat.shiftLeft
                      1180591620717411303424
                      256))))
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          332312069626001133598894019064102912
                          128)
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          332306999023600220681288032251281408
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          332312069626001133598894019064102912
                          128)
                        256)))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          332306998946228968225951765070086144
                          332312069626001133598894019064102912)
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          332306998946228968225951765070086144
                          332312069626001133598894019064102912)
                        256)
                      (Code.joinWords 256
                        (Code.joinWords 128
                          332306998946228968225951765070086144
                          332306998946228968225951765070086144)
                        (Code.joinWords 128
                          332306998946228968225951765070086144
                          332312069626001133598894019064102912)))))
                8192)))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        39652766883359836930362572800
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          128))
                      512)
                    2048)
                  (Nat.shiftLeft
                    324518553658426726783156020576256
                    2048))
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        170141183460469231731687303715884105728
                        128)
                      256)
                    512)
                  2048))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Code.joinWords 128
                          59479150325039755395543859200
                          60446290980731458735505408)
                        (Code.joinWords 128
                          320177793484691610885704525645027999744
                          333521996411126117891027901211123646464))
                      512)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          128)
                        (Code.joinWords 128
                          324518553658426726783156020576256
                          324518553658426726783156020576256))
                      512)
                    2048))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          180775007426748558714917760198126862336
                          128)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          21766108490631233061864102608792190976
                          21776493027412732316550587989488566272)
                        256))
                    2048)
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          332306998946228968225951765070086144
                          128)
                        256))
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
                            324518553658426726783156020576256
                            324518553658426726783156020576256)))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          332306998946228968225951765070086144
                          128)
                        256))))))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        1180591620717411303424
                        256)
                      (Code.joinWords 256
                        1180591620717411303424
                        1180591620717411303424))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          77371252455336267181195264
                          256)
                        324518553658426726783156020576256)
                      (Code.joinWords 256
                        77371252455336267181195264
                        77371252455336267181195264))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        64
                        256)
                      (Nat.shiftLeft
                        1180591620717411303488
                        256))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        1180591620717411303424
                        256)
                      (Nat.shiftLeft
                        1180591620717411303424
                        256)))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          128)
                        256)
                      512)
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          324518553658426726783156020576256
                          324518553658426726783156020576256)
                        256)
                      (Nat.shiftLeft
                        324518553658426726783156020576256
                        256)))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          332306998946228968225951765070086144
                          332306999023600220681288032251281408)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          332312069548629881143557751882907648
                          5070679772165372942253994016768)
                        256))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            332636588102288307870340907903483904
                            329589233430592099725410014593024)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          324518553658426726783156020576256))
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          332312069548629881143557751882907648
                          77371252455336267181195264)
                        256))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          332312069548629881143557751882907648
                          5070679772165372942253994016768)
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          332306998946228968225951765070086144
                          332306999023600220681288032251281408)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          332312069548629881143557751882907648
                          5070679772165372942253994016768)
                        256)))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          332312069548629881143557751882907648
                          77371252455336267181195264)
                        256))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            332636588102288307870340907903483904
                            349871565662991314813090084683776)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            20282409603651670423947251286016
                            128)
                          (Nat.shiftLeft
                            20282409603651670423947251286016
                            128)))
                      (Code.joinWords 256
                        (Code.joinWords 128
                          332306998946228968225951765070086144
                          332306998946228968225951765070086144)
                        332312069548629881143557751882907648))))))))
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
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          128)
                        256)
                      512)
                    324518553658426726783156020576256))
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
                      1024))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          332306998946228968225951765070086144000
                          128)
                        (Nat.shiftLeft
                          333524754818832214518205558037298544640
                          128))
                      512)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          319845486485745381917478573879957913600
                          128)
                        (Nat.shiftLeft
                          338509207684953621654066654908965191680
                          128))
                      512)
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          128)
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          128))
                      512)))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          180775007426748558714917760198126862336
                          128)
                        (Nat.shiftLeft
                          180775007426748558714917760198126862336
                          128))
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          23926103924130903563907756343395614720
                          128)
                        (Nat.shiftLeft
                          21862328182225405844144969944519409664
                          128)))
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
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          332306998946228968225951765070086144
                          128)
                        256))))))
            (Code.joinWords 16384
              (Code.joinWords 8192
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
                          170141183460469231731687303715884105728
                          128)
                        256)
                      512)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5316911983139663491615228241121378304
                          256)
                        512)
                      1024)))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1180591620717411303424
                            128)
                          256)
                        (Nat.shiftLeft
                          4398046511104
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          5316993112778078098296924030126522368
                          256)
                        (Nat.shiftLeft
                          81129638414606681695789005144064
                          256))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          332312069548629881143557751882907648
                          5070602400912917605986812821504)
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            5649629700880366406167264938030006272
                            329589156059339644389142833397760)
                          256)
                        (Nat.shiftLeft
                          405648192073033408478945025720320
                          256))
                      (Nat.shiftLeft
                        5649305182326707979440481782009430016
                        256)))))
              (Code.joinWords 8192
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
                      (Code.joinWords 256
                        (Code.joinWords 128
                          170805797458361689668139207246024278016
                          21433801432031768450574451796973977600)
                        (Code.joinWords 128
                          170805797458361689668139207246024278016
                          30585234786404203971984724064106184704))
                      512)
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
                            324518553658426726783156020576256
                            324518553658426726783156020576256)))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5316911983139663491615228241121378304
                          256)
                        512))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            5649305182326707979440481782009430016
                            5070679772165372942253994016768)
                          256)
                        (Nat.shiftLeft
                          81129638414606969926165156855808
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          332306998946228968225951765070086144
                          332312069626001133598894019064102912)
                        256)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            6978533178111623852344288842289774592
                            5070602400912917605986812821504)
                          256)
                        (Nat.shiftLeft
                          1329227995784915872975864654318272512
                          256))))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          5316911983139663491615228241121378304
                          256)
                        (Nat.shiftLeft
                          5316993112778078098585154406278234112
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            5732381932063265221496969723276951552
                            83076749755900055170322008062820352)
                          256)
                        (Nat.shiftLeft
                          81129638414606681695789005144064
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            5649629700880366406167264938030006272
                            329589156059339644389142833397760)
                          256)
                        (Nat.shiftLeft
                          405648192073033408478945025720320
                          256))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            5649218982085892459841180006191464448
                            332306998946228968225951765070086144)
                          (Code.joinWords 128
                            7061609927848181094400776783557296128
                            83076749755900055170322008062820352))
                        (Code.joinWords 256
                          5316911983139663491615228241121378304
                          1329227995784915872975864654318272512))))))))
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
                    2048)
                  (Nat.shiftLeft
                    324518553658426726783156020576256
                    2048))
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
                      1024))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Code.joinWords 128
                          319014718988379809496913694467282698240
                          77095223755525120628420809496259985408)
                        (Code.joinWords 128
                          21766108430977997418799840612090642432
                          21779251432401163701234558430923980800))
                      512)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          128)
                        (Code.joinWords 128
                          324518553658426726783156020576256
                          324518553658426726783156020576256))
                      512)
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          319014719047800931382611947662440660992
                          319014719047800931382611947662440660992)
                        256)
                      512)
                    (Code.joinWords 512
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          180775007426748558714917760198126862336
                          128)
                        (Nat.shiftLeft
                          180775007426748558714917760198126862336
                          128))
                      (Code.joinWords 256
                        (Code.joinWords 128
                          63802943797675961899382738893456539648
                          23926103924130903563907756343395811328)
                        (Code.joinWords 128
                          21849185180946668418222337354901749760
                          21862328182225405861506346508032671744))))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          332306998946228968225951765070086144
                          128)
                        256))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            324518553658426726800748206620672
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          (Code.joinWords 128
                            324518553658426726783156020576256
                            324518553658426726800748206620672)))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          332306998946228968225951765070086144
                          128)
                        256))))))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          332312069548629881143557751882907648
                          5070602400912917605986812821504)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          332312069548629881143557751882907648
                          5070602400912917605986812821504)
                        256))
                    2048)
                  4096)
                (Code.joinWords 4096
                  (Code.joinWords 1024
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        64
                        128)
                      256)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        1180591620717411303488
                        128)
                      256))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          332312069548629881143557751882907648
                          5070602400912917605986812821504)
                        256))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          329589156059339644389142833397760
                          329589156059339644389142833397760)
                        256)
                      (Nat.shiftLeft
                        5070602400912917605986812821504
                        256)))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          332306998946228968225951765070086144
                          332312069626001133598894019064102912)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          5070602400912917605986812821504
                          5070679772165372942253994016768)
                        256))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            329589156059339644389142833397760
                            21099093507684410494320019024904192)
                          256)
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          20769504351625070849930876191506432
                          128)
                        256))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          5070602400912917605986812821504
                          5070679772165372942253994016768)
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          332306998946228968225951765070086144
                          332312069626001133616908692451491840)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          5070602400912917605986812821504
                          5070602400912935620660200210432)
                        256)))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          83076749736557242056487941267521536
                          83076749755900055170322008062820352)
                        256))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            329589156059339644389142833397760
                            21119375917288062182776231849623552)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            20282409603651670423947251286016
                            128)
                          (Nat.shiftLeft
                            20282409603651670441539437330432
                            128)))
                      (Code.joinWords 256
                        (Code.joinWords 128
                          332306998946228968225951765070086144
                          332306998946228968225951765070086144)
                        (Code.joinWords 128
                          83076749736557242056487941267521536
                          103846254107525126038267557641715712)))))))))))
    (Code.joinWords 262144
      (Nat.shiftLeft
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        9367487224930631680
                        128)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          128)
                        256))
                    324518553658426726783156020576256)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        4398046511104
                        256)
                      (Code.joinWords 256
                        4398046511104
                        4398046511104))
                    (Code.joinWords 1024
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          128)
                        288230376151711744)
                      (Code.joinWords 256
                        288230376151711744
                        288230376151711744)))
                  4096))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          14051230837395947520
                          128)
                        (Nat.shiftLeft
                          337623910929368631717566993311207522304
                          128))
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          216735732067401728
                          128)
                        (Nat.shiftLeft
                          338506601395319552414417177687174938624
                          128)))
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
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          128))))
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          5316911983139663491615228241121378304
                          256)
                        (Nat.shiftLeft
                          5316911983139663491903458617273090048
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          5316993112778078098296924030126522368
                          256)
                        (Nat.shiftLeft
                          81129638414606969926165156855808
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            5317317631331736525023707186147098624
                            324518553658426726783156020576256)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          405648192073033696709321177432064))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          5316993112778078098296924030126522368
                          256)
                        (Nat.shiftLeft
                          288230376151711744
                          256))))
                  4096)))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        170141183460469231731687303715884105728
                        128)
                      256)
                    512)
                  4096)
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        1024
                        256)
                      (Nat.shiftLeft
                        4398046512128
                        256))
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          128)
                        256)
                      512))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        4398046511104
                        256)
                      (Nat.shiftLeft
                        4398046511104
                        256))
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          324518553658426726783156020576256
                          324518553658426726783156020576256)
                        256)
                      (Nat.shiftLeft
                        324518553658426726783156020576256
                        256)))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5316911983139663491615228241121378304
                          256)
                        512))
                    2048)
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          29243015907268149218583504509904879616
                          128)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          170805797458361689668139207246024278016
                          29253400500985218860043788044113805312)
                        256))
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
                            324518553658426726783156020576256
                            324518553658426726783156020576256)))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5316911983139663491615228241121378304
                          256)
                        512))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          5316993112778078098296924030126522368
                          256)
                        (Nat.shiftLeft
                          81129638414606969926165156855808
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          256)
                        512)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          5316993112778078098296924030126522368
                          256)
                        (Nat.shiftLeft
                          288230376151711744
                          256))))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          5316911983139663491615228241121378304
                          256)
                        (Nat.shiftLeft
                          5316911983139663491903458617273090048
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          5316993112778078098296924030126522368
                          256)
                        (Nat.shiftLeft
                          81129638414606969926165156855808
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          5317317631331736525023707186147098624
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1267650600228229401496703205376
                            128)
                          (Code.joinWords 128
                            406915842673261637880441728925696
                            1267650600228229401496703205376)))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          5316911983139663491615228241121378304
                          5316993112778078098296924030126522368)
                        5316911983139663491615228241121378304)))))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    324518553658426726800748206620672
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      324518553658426726800748206620672
                      128)
                    2048)
                  4096))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
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
                        324518553658426726783156020576256))
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          324518553658426726783156020576256
                          324518553658426726783156020576256)
                        256)
                      (Nat.shiftLeft
                        324518553658426726783156020576256
                        128))
                    2048)
                  4096)))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          128)
                        256)
                      512)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          324518553658426726783156020576256
                          324518553658426726783156020576256)
                        256)
                      (Nat.shiftLeft
                        324518553658426726783156020576256
                        256))
                    2048))
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          128)
                        256)
                      512)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        324518553658426726783156020576256
                        256)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          128)
                        324518553658426726783156020576256))
                    2048))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          128)
                        256)
                      512)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          1267650600228229401496703205376
                          128)
                        (Code.joinWords 128
                          1267650600228229401496703205376
                          1267650600228229401496703205376))
                      512)
                    2048))))))
        131072)
      (Code.joinWords 131072
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    75557863725914323419136
                    2048)
                  4096)
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
                  4096))
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 2048
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
                        512)))
                  4096)
                8192))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      75557863725914323419136
                      512)
                    2048)
                  4096)
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
                  4096))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Code.joinWords 512
                    (Code.joinWords 256
                      (Nat.shiftLeft
                        255211775190703847597530955573826158592
                        128)
                      (Nat.shiftLeft
                        271162511140122838072376640297190293504
                        128))
                    (Code.joinWords 256
                      (Nat.shiftLeft
                        255211775190703847597530955573826158592
                        128)
                      (Nat.shiftLeft
                        271162511140122838072376640297190293504
                        128)))
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
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
                        512)))
                  4096))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  324518553733984590509070343995392
                  2048)
                4096)
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
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
                        324518553658426726783156020576256))
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          128)
                        256)
                      512)
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          324518553658426726783156020576256
                          324518553658426726783156020576256)
                        256)
                      (Nat.shiftLeft
                        324518553658426726783156020576256
                        128)))
                  4096)))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      324518553733984590509070343995392
                      512)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          128)
                        256)
                      512)
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          324518553658426726783156020576256
                          324518553658426726783156020576256)
                        256)
                      (Nat.shiftLeft
                        324518553658426726783156020576256
                        256)))
                  4096))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        324518553658426726783156020576256
                        256)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          128)
                        324518553658426726783156020576256))
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          324518553658426726783156020576256
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
                  4096)))))
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          128)
                        256)
                      512)
                    324518553658426726783156020576256)
                  4096)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          5316993112778078098296924030126522368
                          256)
                        (Nat.shiftLeft
                          81129638414606681695789005144064
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          5316993112778078098296924030126522368
                          256)
                        (Nat.shiftLeft
                          81129638414606681695789005144064
                          256)))
                    2048)
                  4096))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          319014718988379809496913694467282698240
                          128)
                        (Nat.shiftLeft
                          29243015907268149203883755326167580672
                          128))
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          64633711295041534319947618306131755008
                          128)
                        (Nat.shiftLeft
                          29256006790619288098790293540616273920
                          128)))
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
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          128))))
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          5316911983139663491615228241121378304
                          256)
                        (Nat.shiftLeft
                          5316993112778078098585154406278234112
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          81129638414606681695789005144064
                          256)
                        (Nat.shiftLeft
                          81129638414606969926165156855808
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            405648192073033408478945025720320
                            324518553658426726783156020576256)
                          256)
                        (Nat.shiftLeft
                          21175152538862400981077204425244672
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          20769504346789367572598259399524352
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
                          5316911983139663491615228241121378304
                          256)
                        512)
                      1024)
                    2048)
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
                          5316911983139663491615228241121378304
                          256)
                        512)
                      1024)))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1024
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          4398046512128
                          256)
                        512))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          256)
                        512)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          5316993112778078098296924030126522368
                          256)
                        (Nat.shiftLeft
                          81129638414606681695789005144064
                          256))))
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          405648192073033408478945025720320
                          256)
                        (Nat.shiftLeft
                          405648192073033408478945025720320
                          256))
                      (Nat.shiftLeft
                        81129638414606681695789005144064
                        256))
                    2048)))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          319014718988379809510748752522564861952
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          319014718988379809510748752522564861952
                          128)
                        256))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5316911983139663491615228241121378304
                          256)
                        512)))
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          63802943797675961899382738893456539648
                          128)
                        (Nat.shiftLeft
                          30572243903053065077652253514903060480
                          128))
                      (Code.joinWords 256
                        (Code.joinWords 128
                          170805797458361689668139207246024278016
                          21433801432031768450574451796974174208)
                        (Code.joinWords 128
                          170805797458361689668139207246024278016
                          30585234865322881476427716588925353984)))
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
                            324518553733984590509070343995392
                            324518553733984590509070343995392)))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5316911983139663491615228241121378304
                          256)
                        512))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          81129638414606681695789005144064
                          256)
                        (Nat.shiftLeft
                          81129638414606969926165156855808
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          256)
                        512)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          1329227995784915872903807060280344576
                          256)
                        (Nat.shiftLeft
                          1329227995784915872975864654318272512
                          256))))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          5316911983139663491615228241121378304
                          256)
                        (Nat.shiftLeft
                          5316993114016037027336466159758213120
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          81129638414606681695789005144064
                          256)
                        (Nat.shiftLeft
                          81130876373535433007542485123072
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          405648192073033408478945025720320
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1267650600228229401496703205376
                            128)
                          (Code.joinWords 128
                            21176421427497115825516368931848192
                            1267650675786093127411026624512)))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          5316911983139663491615228241121378304
                          1329227995784915872903807060280344576)
                        (Code.joinWords 256
                          5316911983139663491615228241121378304
                          1349997501369664169299774667197775872))))))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  324518553658426726783156020576256
                  2048)
                4096)
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
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
                        324518553658426726783156020576256))
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          128)
                        256)
                      512)
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          324518553658426726783156020576256
                          324518553658426726800748206620672)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          17592186044416
                          128)
                        256)))
                  4096)))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          128)
                        256)
                      512)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          128)
                        256)
                      512)
                    (Nat.shiftLeft
                      324518553658426726783156020576256
                      256)))
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          128)
                        256)
                      512)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        324518553658426726783156020576256
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          324518553733984590509070343995392
                          75557863725914323419136)
                        256))
                    2048))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          128)
                        256)
                      512)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          128)
                        256)
                      512)
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          20282409603651670441539437330432
                          128)
                        256)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          21550060203879899825443954491392
                          128)
                        (Code.joinWords 128
                          1267650675786093127411026624512
                          21550060279437763568950463954944))))))))))))

/-- The block word is computed from the verified profile data. -/
theorem word_eq :
    Code.profileWord 64 24 (fun i q => Data.profiles (128 + i) q) = word := by
  decide +kernel

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage002
