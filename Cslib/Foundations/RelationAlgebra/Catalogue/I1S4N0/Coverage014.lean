/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Cslib.Foundations.RelationAlgebra.FastCatalogueCoverage

/-!
# Profile coverage for models 897–960 of the ⟨1, 4, 0⟩ row

The balanced word contains exactly the cycle profiles of this block and its atom renamings.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage014

/-- The cycle profiles covered by this block of models. -/
def word : ℕ :=
  (Code.joinWords 524288
    (Code.joinWords 262144
      (Nat.shiftLeft
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            255876389188596305533982859103966330880
                            256212600551391237448765420714908975104)
                          256)
                        512)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          11529355785704308736
                          128)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            50462720
                            128)
                          (Code.joinWords 128
                            256212605621993638361683026701721796608
                            256212605621993638361683026701721796608))))
                    2048)
                  4096)
                8192)
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            256212605621993638361683026701721796608
                            128)
                          (Nat.shiftLeft
                            256212605621993638361683026701721796608
                            128))
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            256212605621993638361683026701721796608
                            128)
                          (Nat.shiftLeft
                            256212605621993638361683026701721796608
                            128))
                        512))
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 1024
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          256208696187542534516097912119847026688
                          256208696187542534516097912119847026688)
                        256)
                      512)
                    (Nat.shiftLeft
                      1313286021836445659950584520769536
                      512))
                  4096)))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            2658455991569831745807614120560689152
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            166153499473114484112975882535043072
                            633825300114114700748351602688)
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          2658455991569831745807614120560689152
                          128)
                        256))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          2658455991569831745807614120560689152
                          128)
                        256)
                      (Nat.shiftLeft
                        3909434451103859474215832685379584
                        256))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        32768
                        128)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          319014718988379809496913694467282698240
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            633825300114114700748351602688
                            128)
                          256))
                      (Nat.shiftLeft
                        319014718988379809496913694467282698240
                        256)))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        32768
                        128)
                      (Nat.shiftLeft
                        32768
                        128))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        319014718988379809496913694467282698240
                        256)
                      (Nat.shiftLeft
                        319014718988379809496913694467282698240
                        256)))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            212676479325586539664609129644855132160
                            128)
                          (Nat.shiftLeft
                            5316911983139663491903458617273090048
                            128))
                        (Code.joinWords 256
                          21267647932558653966460912964485513216
                          (Code.joinWords 128
                            21267647972327477728503754295619878912
                            5070602402093509376237805502464)))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            297747071055821155530452781502797185024
                            128)
                          (Nat.shiftLeft
                            5316911983139663491903458617273090048
                            128))
                        (Code.joinWords 256
                          21267653003161054879378518951298334720
                          21267647952443065847482333630052696064)))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            297747071055821155530452781502797185024
                            128)
                          (Nat.shiftLeft
                            5316911983139663491903458617273090048
                            128))
                        (Code.joinWords 256
                          21267647932558653966460912964485513216
                          (Code.joinWords 128
                            21271557426585622216544054526691246080
                            20769504346789367572598276579393536)))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            297747071055821155530452781502797185024
                            128)
                          (Nat.shiftLeft
                            5316911983139663491903458617273090048
                            128))
                        (Code.joinWords 256
                          21267647932558653966460912964485513216
                          (Code.joinWords 128
                            21267647952443065847482333630052696064
                            20769504346789367572598276579393536))))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            319014718988379809514207517036385402880
                            319014718988379809514207517036385402880)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          83076749736557242056487941267521536
                          83076749736557242056487941267521536)
                        512))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            297747071055821155530452781502797185024
                            128)
                          (Code.joinWords 128
                            319014718988379809496913694467282698240
                            5316911983139663491903458617273090048))
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            83076749755900055170322008062820352
                            83081820358302148679768614612500480)
                          256))
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          319014718988379809496913694467282698240
                          128)
                        (Code.joinWords 128
                          319014718988379809496913694467282698240
                          5316911983139663491903458617273090048))))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            4503599627370496
                            4503599627370496)
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            319014718988379809496913694467282698240
                            128)
                          (Code.joinWords 128
                            319014718988379809496913694467282698240
                            5316911983139663491903458617273090048))
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            20769504346789367577101876206764032
                            128)
                          256))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            319014718988379809496913694467282698240
                            128)
                          (Code.joinWords 128
                            319014718988379809496913694467282698240
                            5316911983139663491903458617273090048))
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            4503599627370496
                            20769504346789367577101876206764032)
                          256))))))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        4611686018427387904
                        128)
                      1024)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        4611686018427387904
                        128)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 128
                          9223372036854775808
                          9799832791305682944)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            50462720
                            128)
                          (Code.joinWords 128
                            256212605621993638361683026701721796608
                            256212605621993638361683026701721796608)))
                      (Nat.shiftLeft
                        4611686019501129728
                        128)))
                  4096))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        71193377898496
                        256)
                      512)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        256208696187542534516097912119847026688
                        256208696187542534516097912119847026688)
                      256)
                    512)
                  4096)))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        633825300114114700748351602688
                        128)
                      256)
                    512)
                  2048)
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      16384
                      128)
                    1024)
                  (Code.joinWords 1024
                    (Nat.shiftLeft
                      16384
                      128)
                    (Nat.shiftLeft
                      16384
                      128))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            106338239662793269832304564822427566080
                            128)
                          (Code.joinWords 128
                            1152921504606846976
                            5316911983139663491903458617273090048))
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5070602402093509446606549680128
                            128)
                          256))
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          106338239662793269832304564822427566080
                          128)
                        (Code.joinWords 128
                          1152921504606846976
                          5316911983139663491903458617273090048)))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            106338239662793269832304564822427566080
                            128)
                          (Code.joinWords 128
                            1152921504606846976
                            5316911983139663491903458617273090048))
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            20769504346789367572598276579393536
                            128)
                          256))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            106338239662793269832304564822427566080
                            128)
                          (Nat.shiftLeft
                            5316911983139663491903458617273090048
                            128))
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            20769504346789367572598276579393536
                            128)
                          256)))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            319014718988379809514207517036385402880
                            319014718988379809514207517036385402880)
                          256)
                        512)
                      (Nat.shiftLeft
                        83076749736557242056487941267521536
                        512))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            106338239662793269832304564822427566080
                            128)
                          (Nat.shiftLeft
                            5316911983139663491903458617273090048
                            128))
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            83076749755900055170322008062820352
                            83081820358302148679768614612500480)
                          256))
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          106338239662793269832304564822427566080
                          128)
                        (Nat.shiftLeft
                          5316911983139663491903458617273090048
                          128))))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            4503599627370496
                            4503599627370496)
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            106338239662793269832304564822427566080
                            128)
                          (Nat.shiftLeft
                            5316911983139663491903458617273090048
                            128))
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            4503599627370496
                            20769504346789367577101876206764032)
                          256))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            106338239662793269832304564822427566080
                            128)
                          (Nat.shiftLeft
                            5316911983139663491903458617273090048
                            128))
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            4503599627370496
                            20769504346789367577101876206764032)
                          256)))))))))
        131072)
      (Code.joinWords 131072
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            2658455991569831745807614120560689152
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            166153499473114484112975882535043072
                            633825300114114700748351602688)
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          166153499473114484112975882535043072
                          256)
                        512))
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          4137611559144940766485239262347264
                          128)
                        256)
                      (Nat.shiftLeft
                        166153499473114484112975882535043072
                        256)))
                  4096)
                8192)
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            271166648751681983013143125536452640768
                            128)
                          (Nat.shiftLeft
                            271166648751681983013143125536452640768
                            128))
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            271166648751681983013143125536452640768
                            128)
                          (Nat.shiftLeft
                            271166648751681983013143125536452640768
                            128))
                        512))
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Nat.shiftLeft
                            21267647932558653976260745753643712512
                            128))
                        (Code.joinWords 256
                          212676479325586539664609129644855132160
                          (Code.joinWords 128
                            332306999023600220681288032251281408
                            81129639021430774748936461615104)))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267729062197068573142608753490657280
                            128)
                          (Nat.shiftLeft
                            21267647932558653971360829359064612864
                            128))
                        (Code.joinWords 256
                          297747071055821155530452781502797185024
                          332306999023600220681288032251281408)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Nat.shiftLeft
                            21271785544117798921638917011333447680
                            128))
                        (Code.joinWords 256
                          297747071055821155530452781502797185024
                          (Code.joinWords 128
                            332306999023600220681288032251281408
                            20769504351625144636907171029712896)))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Nat.shiftLeft
                            21267647932558653971360829359064612864
                            128))
                        (Code.joinWords 256
                          297747071055821155530452781502797185024
                          (Code.joinWords 128
                            332306999023600220681288032251281408
                            20769504351625144636907171029712896)))))
                  4096)))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            265845599156983174580761412056068915200
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            271166567622043568406461429747447496704
                            128)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            271166648751681983013143125536452640768
                            128)
                          256)
                        (Code.joinWords 256
                          (Code.joinWords 128
                            49518206034325018312699805696
                            3276800)
                          (Nat.shiftLeft
                            271166648751681983013143125536452640768
                            128))))
                    2048)
                  4096)
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        32768
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        32768
                        512)
                      (Nat.shiftLeft
                        32768
                        512)))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          319014718988379809496913694467282698240
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            633825300114114700748351602688
                            128)
                          256))
                      (Nat.shiftLeft
                        319014718988379809496913694467282698240
                        256))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        319014718988379809496913694467282698240
                        256)
                      (Nat.shiftLeft
                        319014718988379809496913694467282698240
                        256)))))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Code.joinWords 1024
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          271162511203257780075931034317045628928
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          271162511203257780075931034317045628928
                          128)
                        256))
                    (Nat.shiftLeft
                      1541463129877526952219991097737216
                      128))
                  2048)
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            319014719062656211854036510961230151680
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            319014719062656211854036510961230151680
                            128)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          1329227995784915872903807060280344576
                          128)
                        (Nat.shiftLeft
                          1329227995784915872903807060280344576
                          128)))
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            309485009821345068724781056
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            309485009821345068724781056
                            128)
                          256))
                      1024))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            319014718988379809496913694467282698240
                            1329227995784915872975864654318272512)
                          256)
                        (Code.joinWords 256
                          297747071055821155530452781502797185024
                          (Code.joinWords 128
                            332306999023600220681288032251281408
                            1329309125424239535205517248073564160)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          319014718988379809496913694467282698240
                          256)
                        (Code.joinWords 256
                          319014718988379809496913694467282698240
                          332306999023600220681288032251281408)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          319014718988379809496913694467282698240
                          256)
                        (Code.joinWords 256
                          319014718988379809496913694467282698240
                          (Code.joinWords 128
                            332306999023600220681288032251281408
                            20769504661110154458252239754493952)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            319014718988379809496913694467282698240
                            309485009821345068724781056)
                          256)
                        (Code.joinWords 256
                          319014718988379809496913694467282698240
                          (Code.joinWords 128
                            332306999023600220681288032251281408
                            20769504661110154458252239754493952)))))))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      2147483648
                      1073741824)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        2658455991569831745807614120560689152
                        128)
                      256)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        4137611559144940766485239262347264
                        128)
                      256))
                  4096))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1125917086711808
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            17179869184
                            128)
                          256)
                        512))
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Nat.shiftLeft
                            21267647932558653980872431772071100416
                            128))
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            274877906944
                            81129638718018728224561756635136)
                          256))
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          21267729062197068573142608753490657280
                          128)
                        (Nat.shiftLeft
                          21267647932558653971360829359064612864
                          128)))
                    (Code.joinWords 1024
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          128)
                        (Nat.shiftLeft
                          21271785544117798921927147387485159424
                          128))
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          128)
                        (Nat.shiftLeft
                          21267647932558653971360829359064612864
                          128))))
                  4096)))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      32768
                      512)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          1048576
                          1048576)
                        512)
                      1024)
                    2048))
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    32768
                    512)
                  2048))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Code.joinWords 512
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        72057594037927936
                        128)
                      256)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        72057594037927936
                        128)
                      256))
                  2048)
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      8070450532247928832
                      256)
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          309485009821345068724781056
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          309485009821345068724781056
                          128)
                        256)))
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1329227995784915872975864654318272512
                          128)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          274877906944
                          1329309125423633891704089216074907648)
                        256))
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          309485009821345068724781056
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          309485009821345068724781056
                          128)
                        256))))))))
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      2147483648
                      1073741824)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          2658455991569831745807614120560689152
                          128)
                        256)
                      (Nat.shiftLeft
                        3909434451103859474215832685379584
                        256))
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        4137611559144940766485239262347264
                        128)
                      256))
                  4096))
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Nat.shiftLeft
                            21267647932558653980872431772071100416
                            128))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            83076749736557242056487941267521536
                            83076749736557242056487941267521536)
                          (Code.joinWords 128
                            86986184187661101530703773952901120
                            83157879375880904286140535022813184)))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267729062197068573142608753490657280
                            128)
                          (Nat.shiftLeft
                            21267647932558653971360829359064612864
                            128))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            83076749736557242056487941267521536
                            83076749736557242056487941267521536)
                          (Code.joinWords 128
                            83076749736557242056487941267521536
                            83076749736557242056487941267521536))))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Nat.shiftLeft
                            21271785544117798921927147387485159424
                            128))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            83076749736557242056487941267521536
                            103845937170696552570609926584401920)
                          (Code.joinWords 128
                            83076749736557242056487941267521536
                            83076749736557242056487941267521536)))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Nat.shiftLeft
                            21267647932558653971360829359064612864
                            128))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            83076749736557242056487941267521536
                            103846254083346609627960300760203264)
                          (Code.joinWords 128
                            83076749736557242056487941267521536
                            83076749736557242056487941267521536)))))
                  4096)
                8192))
            (Code.joinWords 16384
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
                        166153499473114484112975882535043072
                        256))
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        3909434451103859474215832685379584
                        256)
                      512)
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          297747071055821155530452781502797185024
                          128)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          297747071055821155530452781502797185024
                          319014718988379809496913694467282698240)
                        256))
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        4137611559144940766485239262347264
                        128)
                      256))
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      3909434451103859474215832685379584
                      256)
                    512)))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1329227995784915872903807060280344576
                            128)
                          (Nat.shiftLeft
                            1333365607344060813670292299542691840
                            128))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            1329227995784915872903807060280344576)
                          (Code.joinWords 128
                            21267647992134518357069838694005866496
                            1329233066387317966413253666830024704)))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1329227995784915872903807060280344576
                            128)
                          (Nat.shiftLeft
                            1329227995784915872903807060280344576
                            128))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            21267653003161054879378518951298334720
                            1329227995784915872903807060280344576)
                          (Code.joinWords 128
                            21267647952443065847482333630052696064
                            1329227995784915872903807060280344576))))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1329227995784915872903807060280344576
                            128)
                          (Nat.shiftLeft
                            1329227995784915872903807060280344576
                            128))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            1349997183219055183417929045597224960)
                          (Code.joinWords 128
                            21271557426662993468999390793872441344
                            1329227995784915872903807060280344576)))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1329227995784915872903807060280344576
                            128)
                          (Nat.shiftLeft
                            1329227995784915872903807060280344576
                            128))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            1349997500131705240475279419773026304)
                          (Code.joinWords 128
                            21267647952443065847482333630052696064
                            1329227995784915872903807060280344576))))
                    2048))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            4137611559144940766485239262347264
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            83076749755900055170322008062820352
                            83081820667787158501118081383792640)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            309485009821345068724781056
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            309485009821345068724781056
                            128)
                          256)))
                    2048)
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1329227995784915872975864654318272512
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            3909434451103859474215832685379584
                            1329309125424240715801641565112238080)
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            4503599627370496
                            4503599627370496)
                          256)
                        512))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            309485009821345068724781056
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            20769504346789367571472359492681728
                            128)
                          (Code.joinWords 128
                            4503599627370496
                            309485009825848668352151552)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            309485009821345068724781056
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            20769504346789367571472359492681728
                            128)
                          (Code.joinWords 128
                            4503599627370496
                            309485009825848668352151552)))))))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      2147483648
                      1073741824)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        4137611559144940766485239262347264
                        128)
                      256)
                    2048)
                  4096))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          20769504346789367571472359492681728
                          128)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          20769504346789367571472359492681728
                          128)
                        512))
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Nat.shiftLeft
                            21267647932558653980872431772071100416
                            128))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            83076749736557242056487941267521536
                            83076749736557242056487941267521536)
                          (Code.joinWords 128
                            83076749736557242056487941267521536
                            83157879375275260784712503024156672)))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Nat.shiftLeft
                            21267647932558653971360829359064612864
                            128))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            83076749736557242056487941267521536
                            83076749736557242056487941267521536)
                          (Code.joinWords 128
                            83076749736557242056487941267521536
                            83076749736557242056487941267521536))))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Nat.shiftLeft
                            21271785544117798921927147387485159424
                            128))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            83076749736557242056487941267521536
                            103846254083346609627960300760203264)
                          (Code.joinWords 128
                            83076749736557242056487941267521536
                            83076749736557242056487941267521536)))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Nat.shiftLeft
                            21267647932558653971360829359064612864
                            128))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            83076749736557242056487941267521536
                            103846254083346609627960300760203264)
                          (Code.joinWords 128
                            83076749736557242056487941267521536
                            83076749736557242056487941267521536)))))
                  4096)))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      4137611559144940766485239262347264
                      128)
                    256)
                  2048)
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            319014718988379809496913694467282698240
                            319014718988379809496913694467282698240)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            950272
                            128)
                          (Code.joinWords 128
                            319014718988379809496913694467282731008
                            319014718988379809496913694467282733056)))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          262148
                          128)
                        512))
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        4137611559144940766485239262347264
                        128)
                      256))
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          65536
                          128)
                        512)
                      1024)
                    2048)))
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
                          5070602402093509451004596191232
                          128)
                        256))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          20769504346789367571472359492681728
                          128)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          20769504346789367571472359492747264
                          128)
                        512))
                    2048))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          4137611868629950587830307987128320
                          128)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          83076749755900055170322008062820352
                          83081820667787158501118081383792640)
                        256))
                    2048)
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1329227995784915872975864654318272512
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            4503599627370496
                            1329309125423633891708592815702278144)
                          256))
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            65536
                            128)
                          (Code.joinWords 128
                            4503599627370496
                            4503599627370496))
                        512))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            309485009821345068724781056
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            20769504346789367571472359492681728
                            128)
                          (Code.joinWords 128
                            4503599627370496
                            309485009825848668352151552)))
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            20769504346789367571472359492747264
                            128)
                          (Code.joinWords 128
                            4503599627370496
                            4503599627370496))
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
                      2147483648
                      1073741824)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      32768
                      128)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          16777216
                          128)
                        (Nat.shiftLeft
                          16777216
                          128))
                      1024))
                  4096))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            4835777065434811537031168
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            73786976294838206464
                            128)
                          256)
                        512))
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        19342813113834066795298816
                        19342813113834066795298816)
                      256)
                    512)
                  4096)))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        166153499473114484112975882535043072
                        256)
                      512)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        3909434451103859474215832685379584
                        256)
                      512)
                    2048))
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    32768
                    128)
                  4096))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            18889465931478580854784
                            128)
                          256)
                        (Code.joinWords 256
                          21267647932558653966460912964485513216
                          (Code.joinWords 128
                            21267647992134518357069838694005866496
                            5070602402093509301471014813696)))
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          21267653003161054879378518951298334720
                          21267647952443065847482333630052696064)
                        512))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          21267647932558653966460912964485513216
                          21271557426662993468999390793872441344)
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          21267647932558653966460912964485513216
                          21267647952443065847482333630052696064)
                        512))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      34662321099990647697175478272
                      256)
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          18889465931478580854784
                          128)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          83076749755900055170322008062820352
                          83081820358302148679623479077634048)
                        256)))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          4503599627370496
                          4503599627370496)
                        256)
                      512)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          4503599627370496
                          4503599627370496)
                        256)
                      512))))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      16384
                      128)
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        16777216
                        128)
                      (Nat.shiftLeft
                        16777216
                        128)))
                  4096)
                8192)
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      19342813113834066795298816
                      256)
                    512)
                  4096)
                8192))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        16384
                        128)
                      256)
                    512)
                  (Nat.shiftLeft
                    16384
                    128))
                8192)
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Code.joinWords 512
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        18889465931478580854784
                        128)
                      256)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        5070602402093509301471014813696
                        128)
                      256))
                  2048)
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          83076749755900055170322008062820352
                          83081820358302148679623479077634048)
                        256)
                      512)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          4503599627370496
                          4503599627370496)
                        256)
                      512)
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          65536
                          128)
                        (Code.joinWords 128
                          4503599627370496
                          4503599627370496))
                      512)))))))
        131072)
      (Code.joinWords 131072
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        19807040628566084398385987584
                        512)
                      1024)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        633825300114114700748351602688
                        128)
                      256)
                    512)
                  4096))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        358899852698093036240896
                        128)
                      256)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          4951760157141521099596496896
                          256)
                        (Code.joinWords 256
                          106338239662793269832304564822427566080
                          (Code.joinWords 128
                            332306999023600220681288032251281408
                            81129639323662229652593755291648)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          4951760157141521099596496896
                          256)
                        (Code.joinWords 256
                          106338239662793269832304564822427566080
                          332306999023600220681288032251281408)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          4951760157141521099596496896
                          256)
                        (Code.joinWords 256
                          106338239662793269832304564822427566080
                          (Code.joinWords 128
                            332306999023600220681288032251281408
                            20769504351625144636907171029712896)))
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          106338239662793269832304564822427566080
                          (Code.joinWords 128
                            332306999023600220681288032251281408
                            20769504351625144636907171029712896))
                        512)))
                  4096)))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        19807040628566084398385987584
                        512)
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          39614081257132168796771975168
                          (Nat.shiftLeft
                            271166648751681983013143125536452640768
                            128))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            39768823762042841333281849344
                            3276800)
                          (Nat.shiftLeft
                            271166648751681983013143125536452640768
                            128)))
                      (Nat.shiftLeft
                        19807040628566084399459729408
                        512))
                    2048))
                (Code.joinWords 2048
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      16384
                      512)
                    1024)
                  (Code.joinWords 1024
                    (Nat.shiftLeft
                      16384
                      512)
                    (Nat.shiftLeft
                      16384
                      512))))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Code.joinWords 512
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        271162511203257780075931034317045628928
                        128)
                      256)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        271162511203257780075931034317045628928
                        128)
                      256))
                  2048)
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            319014719062656211854036510961230151680
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            319014719062656211854036510961230151680
                            128)
                          256))
                      (Nat.shiftLeft
                        1329227995784915872903807060280344576
                        128))
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            309485009821345068724781056
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            309485009821345068724781056
                            128)
                          256))
                      1024))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1329227995784915872975864654318272512
                            128)
                          256)
                        (Code.joinWords 256
                          106338239662793269832304564822427566080
                          (Code.joinWords 128
                            332306999023600220681288032251281408
                            1329309125424239535205517248073564160)))
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          106338239662793269832304564822427566080
                          332306999023600220681288032251281408)
                        512))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            309485009821345068724781056
                            128)
                          256)
                        (Code.joinWords 256
                          106338239662793269832304564822427566080
                          (Code.joinWords 128
                            332306999023600220681288032251281408
                            20769504661110154458252239754493952)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            309485009821345068724781056
                            128)
                          256)
                        (Code.joinWords 256
                          106338239662793269832304564822427566080
                          (Code.joinWords 128
                            332306999023600220681288032251281408
                            20769504661110154458252239754493952)))))))))
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        274877906944
                        81129638718018728224561756635136)
                      256)
                    512)
                  4096)
                8192)
              16384)
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      16384
                      512)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        1048576
                        1048576)
                      512)
                    2048))
                (Code.joinWords 2048
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        16384
                        128)
                      256)
                    512)
                  (Nat.shiftLeft
                    16384
                    512)))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      72057594037927936
                      128)
                    256)
                  2048)
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          309485009821345068724781056
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          309485009821345068724781056
                          128)
                        256))
                    2048)
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1329227995784915872975864654318272512
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1329309125423633891704089216074907648
                          128)
                        256))
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          309485009821345068724781056
                          128)
                        256)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          65536
                          128)
                        (Nat.shiftLeft
                          309485009821345068724781056
                          128)))))))))
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      2147483648
                      1073741824)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      3909434451103859474215832685379584
                      256)
                    512)
                  4096))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          20769504346789367571472359492681728
                          128)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          20769504346789367571472359492681728
                          128)
                        512))
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          3909434451103859474215832685379584
                          81129639324842821273311166595072)
                        256)
                      512)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          20769504346789367571472359492681728
                          128)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          20769504346789367571472359492747264
                          128)
                        512)))
                  4096)))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        3909434451103859474215832685379584
                        256)
                      512)
                    2048)
                  4096)
                (Code.joinWords 4096
                  (Code.joinWords 1024
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          319014718988379809496913694467282698240
                          319014718988379809496913694467282731008)
                        256)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          950272
                          128)
                        (Code.joinWords 128
                          319014718988379809496913694467282698240
                          319014718988379809496913694467282731136)))
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        262148
                        128)
                      512))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        3909434451103859474215832685379584
                        256)
                      512)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          65536
                          128)
                        512)
                      1024))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1329227995784915872903807060280344576
                            128)
                          (Nat.shiftLeft
                            1329227995784915872903807060280344576
                            128))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            1329227995784915872903807060280344576)
                          (Code.joinWords 128
                            21267647992134518357069838694005866496
                            1329233066387317966413108531295158272)))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1329227995784915872903807060280344576
                            128)
                          (Nat.shiftLeft
                            1329227995784915872903807060280344576
                            128))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            1329227995784915872903807060280344576)
                          (Code.joinWords 128
                            21267647952443065847482333630052696064
                            1329227995784915872903807060280344576))))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1329227995784915872903807060280344576
                            128)
                          (Nat.shiftLeft
                            1329227995784915872903807060280344576
                            128))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            1349997500131705240475279419773026304)
                          (Code.joinWords 128
                            21271557426662993468999390793872441344
                            1329227995784915872903807060280344576)))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1329227995784915872903807060280344576
                            128)
                          (Nat.shiftLeft
                            1329227995784915872903807060280344576
                            128))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            1349997500131705240475279419773026304)
                          (Code.joinWords 128
                            21267647952443065847482333630052696064
                            1329227995784915872903807060280344576))))
                    2048))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            309485009821345068724781056
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            83076749755900055170322008062820352
                            83081820667787158500968547802415104)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            309485009821345068724781056
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            65536
                            128)
                          (Nat.shiftLeft
                            309485009821345068724781056
                            128))))
                    2048)
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1329227995784915872975864654318272512
                          128)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          3909434451103859478719432312750080
                          1329309125424240715801641565112238080)
                        256))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            309485009821345068724781056
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            20769504346789367571472359492681728
                            128)
                          (Code.joinWords 128
                            4503599627370496
                            309485009825848668352151552)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            309485009821345068724781056
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            20769504346789367571472359492747264
                            128)
                          (Nat.shiftLeft
                            309485009821345068724781056
                            128)))))))))
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        81129638718018728224561756635136
                        128)
                      256)
                    512)
                  4096)
                8192)
              16384)
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 256
                      (Nat.shiftLeft
                        16384
                        128)
                      (Nat.shiftLeft
                        16384
                        128))
                    512)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        65536
                        128)
                      512)
                    2048))
                8192)
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        5070602402093509301471014813696
                        128)
                      256)
                    512)
                  2048)
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          309485009821345068724781056
                          128)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          83076749755900055170322008062820352
                          83081820667787158500968547802415104)
                        256))
                    2048)
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1329227995784915872975864654318272512
                          128)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          4503599627370496
                          1329309125423633891708592815702278144)
                        256))
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          309485009821345068724781056
                          128)
                        256)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          65536
                          128)
                        (Code.joinWords 128
                          4503599627370496
                          309485009825848668352151552))))))))))))

/-- The block word is computed from the verified profile data. -/
theorem word_eq :
    Code.profileWord 64 24 (fun i q => Data.profiles (896 + i) q) = word := by
  decide +kernel

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage014
