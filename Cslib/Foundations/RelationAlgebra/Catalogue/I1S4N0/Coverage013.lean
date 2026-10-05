/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Cslib.Foundations.RelationAlgebra.FastCatalogueCoverage

/-!
# Profile coverage for models 833–896 of the ⟨1, 4, 0⟩ row

The balanced word contains exactly the cycle profiles of this block and its atom renamings.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage013

/-- The cycle profiles covered by this block of models. -/
def word : ℕ :=
  (Code.joinWords 524288
    (Code.joinWords 262144
      (Nat.shiftLeft
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 8192
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        14411738709911142400
                        128)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          50462720
                          128)
                        (Code.joinWords 128
                          808452096
                          256212605621993638361683026702530248704)))
                    1024)
                  2048)
                4096)
              (Nat.shiftLeft
                (Code.joinWords 2048
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Code.joinWords 128
                        11529215046068469760
                        18014618411975362560)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          3723548340384804883564462080
                          128)
                        (Code.joinWords 128
                          256208696187542534502208810869036417024
                          256208696187542534502208810869036417024)))
                    1024)
                  (Code.joinWords 1024
                    (Code.joinWords 512
                      (Code.joinWords 128
                        11529215046068469760
                        16861626541711294464)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          50462720
                          128)
                        (Code.joinWords 128
                          336216433397332827700167597755465728
                          5070602400912917605986812821504)))
                    (Code.joinWords 128
                      11529215046068469760
                      6485262629358010368)))
                4096))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Code.joinWords 128
                        32768
                        3094850098213450687247828992)
                      (Nat.shiftLeft
                        309485009821345068724781056
                        128))
                    1024)
                  (Code.joinWords 1024
                    (Code.joinWords 512
                      (Code.joinWords 128
                        32768
                        3094850098213450687247828992)
                      (Nat.shiftLeft
                        37926505815546838122496
                        128))
                    (Code.joinWords 512
                      (Code.joinWords 128
                        32768
                        3094850098213450687247828992)
                      (Nat.shiftLeft
                        309485009821345068724781056
                        128))))
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 128
                          32768
                          116972063629072596815535021304670322688)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            29787932195304462864760176640
                            75316546502656)
                          256))
                      (Code.joinWords 512
                        (Code.joinWords 128
                          32768
                          31901471898837980949691369446728269824)
                        (Nat.shiftLeft
                          4951760157141521099596496896
                          256)))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 128
                          32768
                          31901471898837980949691369446728269824)
                        (Nat.shiftLeft
                          9981498390831427215784148992
                          256))
                      (Code.joinWords 512
                        (Code.joinWords 128
                          32768
                          31901471898837980949691369446728269824)
                        (Nat.shiftLeft
                          4952063569188045474301476864
                          256)))
                    2048))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 128
                          212676479325586539664609129644855164928
                          31901471898837980949691369446728269824)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            4947802324992
                            128)
                          256))
                      (Code.joinWords 512
                        (Code.joinWords 128
                          212676479325586539664609129644855164928
                          10633823966279326983230456482242756608)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            4503599627370496
                            4503599627370496)
                          256)))
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          4503599627370496
                          4503599627370496)
                        256)
                      512)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 128
                          212676479325586539664609129644855164928
                          10633823966279326983230456482242756608)
                        (Nat.shiftLeft
                          4503599627370496
                          256))
                      (Code.joinWords 128
                        212676479325586539664609129644855164928
                        10633823966279326983230456482242756608)))))))
          (Code.joinWords 32768
            (Code.joinWords 8192
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 1024
                    (Code.joinWords 512
                      (Code.joinWords 128
                        16140901068253954048
                        17149856915178651648)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          50462720
                          128)
                        (Code.joinWords 128
                          807403520
                          256212605621993638361683026702529200128)))
                    (Code.joinWords 512
                      (Code.joinWords 128
                        4611756388245323776
                        288305142942400512)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          1048576
                          1048576)
                        256)))
                  2048)
                4096)
              (Nat.shiftLeft
                (Code.joinWords 2048
                  (Code.joinWords 1024
                    (Code.joinWords 512
                      (Code.joinWords 128
                        16140901064495857664
                        16140901064495857664)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          3728384117450239695101493248
                          128)
                        (Code.joinWords 128
                          256208696187542534502208810869036417024
                          256208696187542534502208810869036417024)))
                    (Code.joinWords 512
                      (Code.joinWords 128
                        5764677891778428928
                        1152991873351041024)
                      (Nat.shiftLeft
                        4835777065434811537031168
                        128)))
                  (Code.joinWords 1024
                    (Code.joinWords 128
                      6917529027641081856
                      7350024126557323264)
                    (Code.joinWords 128
                      5764677891778428928
                      1441226647549247488)))
                4096))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Code.joinWords 1024
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        4642275147320176030871715840
                        128)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          4642275147320176030872633344
                          128)
                        (Code.joinWords 128
                          319014718988379809496913694467282747520
                          319014718988379809496913694467282747520)))
                    (Code.joinWords 512
                      (Code.joinWords 128
                        16384
                        1547425049106725343623906304)
                      (Nat.shiftLeft
                        262148
                        128)))
                  (Code.joinWords 1024
                    (Code.joinWords 512
                      (Code.joinWords 128
                        16384
                        1547425049106725343623906304)
                      (Nat.shiftLeft
                        314339676352711358842667008
                        128))
                    (Code.joinWords 512
                      (Code.joinWords 128
                        16384
                        1547425049106725343623906304)
                      (Nat.shiftLeft
                        4835777065434811537031168
                        128))))
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 128
                          32768
                          5316911983139663491615228241121378304)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            4947802324992
                            128)
                          256))
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
                        (Nat.shiftLeft
                          20769504346789367571472359492747264
                          128))
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
                          106338239662793269832304564822427598848
                          5316911983139663491615228241121378304)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            4947802324992
                            128)
                          256))
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
                            4503599627370496))))
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          4503599627370496
                          4503599627370496)
                        256)
                      512)
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
                          128)))))))))
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
                          855638016
                          128)
                        256)
                      (Code.joinWords 256
                        (Code.joinWords 128
                          59576773446156878136223989760
                          3276800)
                        (Nat.shiftLeft
                          271166648751681983013143125537308278784
                          128)))
                    1024)
                  2048)
                4096)
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          32768
                          (Nat.shiftLeft
                            7205759403792793600
                            128))
                        (Code.joinWords 256
                          107002853660685727768756468352567738368
                          (Nat.shiftLeft
                            341190978387331866689536
                            128)))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          32768
                          (Nat.shiftLeft
                            1152921504606846976
                            128))
                        21932261930451111902912816494625685504))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          32768
                          (Nat.shiftLeft
                            2594222918946783232
                            128))
                        21932261930451111902912816494625685504)
                      (Code.joinWords 512
                        (Code.joinWords 256
                          32768
                          (Nat.shiftLeft
                            1152996271397535744
                            128))
                        21932261930451111902912816494625685504)))
                  4096)
                8192))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          49517601571415210995964968960
                          (Nat.shiftLeft
                            271162511140122838072376640297190293504
                            128))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            74470739543809109568614613120
                            56295854338867200)
                          (Nat.shiftLeft
                            271162511140122838072376640297190293504
                            128)))
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          49517601571415210995964968960
                          (Nat.shiftLeft
                            5321049594698808432381713480383725568
                            128))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            69518677155212684814937227264
                            3276800)
                          (Nat.shiftLeft
                            81129638414606681695789005144064
                            128)))
                      (Code.joinWords 512
                        49517601571415210995964968960
                        24952533509484091259127595008))
                    2048))
                (Code.joinWords 2048
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      32768
                      (Code.joinWords 128
                        45035996273721472
                        4503599627370496))
                    1024)
                  (Code.joinWords 1024
                    (Code.joinWords 512
                      32768
                      (Code.joinWords 128
                        45035996273721472
                        584115552256))
                    (Code.joinWords 512
                      32768
                      (Code.joinWords 128
                        45035996273721472
                        4503599627370496)))))
              (Nat.shiftLeft
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
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        212676479325586539664609129644855164928
                        (Code.joinWords 256
                          21932261930451111902912816494625685504
                          (Nat.shiftLeft
                            38959523483674573012992
                            128)))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          212676479325586539664609129644855164928
                          (Nat.shiftLeft
                            309485009821345068724781056
                            128))
                        (Code.joinWords 256
                          664613997892457936451903530140172288
                          (Nat.shiftLeft
                            309485009821345068724781056
                            128))))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          212676479325586539664609129644855164928
                          (Nat.shiftLeft
                            309485009821345068724781056
                            128))
                        664613997892457936451903530140172288)
                      (Code.joinWords 512
                        212676479325586539664609129644855164928
                        664613997892457936451903530140172288))))
                8192)))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 1024
                    (Code.joinWords 512
                      (Code.joinWords 256
                        1610645504
                        (Nat.shiftLeft
                          570425344
                          128))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          16777216
                          128)
                        256))
                    (Code.joinWords 512
                      (Code.joinWords 256
                        268451840
                        (Nat.shiftLeft
                          285212672
                          128))
                      (Code.joinWords 128
                        1048576
                        1048576)))
                  2048)
                4096)
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          32768
                          (Nat.shiftLeft
                            2594073385365405696
                            128))
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            18889465931478580854784
                            128)
                          256))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          16384
                          (Nat.shiftLeft
                            1152921504606846976
                            128))
                        (Nat.shiftLeft
                          65536
                          128)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          32768
                          (Nat.shiftLeft
                            2305992542795071488
                            128))
                        (Nat.shiftLeft
                          20769504346789367571472359492681728
                          128))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          16384
                          (Nat.shiftLeft
                            1152996271397535744
                            128))
                        (Nat.shiftLeft
                          20769504346789367571472359492747264
                          128))))
                  4096)
                8192))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        32768
                        (Code.joinWords 128
                          16512
                          1126484022394880))
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          1048576
                          1125917087825920)
                        512))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          1048576
                          1114112)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          65536
                          128)
                        512))
                    2048))
                (Code.joinWords 2048
                  (Code.joinWords 1024
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          319014718988379809496913694467282733056
                          128)
                        256)
                      (Code.joinWords 256
                        (Code.joinWords 128
                          63050394783236224
                          63050394784104584)
                        (Code.joinWords 128
                          49280
                          319014718988379809496913694467282750600)))
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        4503599627370496
                        4503599627698180)
                      512))
                  (Code.joinWords 1024
                    (Code.joinWords 512
                      32768
                      (Code.joinWords 128
                        16512
                        1126484022394880))
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        4503599627370496
                        5629516714147840)
                      512))))
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
                        (Nat.shiftLeft
                          65536
                          128)
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
                          (Nat.shiftLeft
                            309503899287276547305635840
                            128)))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          65536
                          128)
                        512))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          20769504346789367571472359492747264
                          128)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          20769504346789367571472359492747264
                          128)
                        512))))))))
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 1024
                    (Code.joinWords 512
                      (Code.joinWords 256
                        1610645504
                        (Nat.shiftLeft
                          570425344
                          128))
                      (Nat.shiftLeft
                        538968064
                        256))
                    (Code.joinWords 512
                      (Code.joinWords 256
                        268451840
                        (Nat.shiftLeft
                          285212672
                          128))
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          269484032
                          17825792)
                        256)))
                  2048)
                4096)
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
                          32768
                          (Nat.shiftLeft
                            2594073385365405696
                            128))
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            606824093048749409959936
                            38959523483674573012992)
                          256))
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
                            4503599627370496))))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          32768
                          (Nat.shiftLeft
                            2305992542795071488
                            128))
                        (Nat.shiftLeft
                          316912650057057350374175801344
                          128))
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
                  4096)))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Code.joinWords 1024
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          319014718988379809496913694467282698240
                          21267647932558653966460912964485548032)
                        256)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          966664
                          128)
                        (Code.joinWords 128
                          21267647932558653966460912964485546112
                          51336)))
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        327684
                        128)
                      512))
                  (Nat.shiftLeft
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
                        512))
                    2048))
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          32768
                          (Nat.shiftLeft
                            149533581377536
                            128))
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            9980891566738378466374189056
                            4947802324992)
                          256))
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
                            309485009821345068724781056))))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        32768
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            316912650057057350374175801344
                            128)
                          9904127138376090948602953728))
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
                            309485009821345068724781056))))
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
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          32768
                          (Nat.shiftLeft
                            309485009821494602306158592
                            128))
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            549755813888
                            128)
                          256))
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            65536
                            128)
                          (Code.joinWords 128
                            4503599627370496
                            4503599627370496))
                        512)))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        32768
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            606824097552349037330432
                            37778931862957161709568)
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
                        512)))))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 1024
                    (Code.joinWords 512
                      (Code.joinWords 256
                        1610645504
                        (Nat.shiftLeft
                          570425344
                          128))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          16777216
                          128)
                        256))
                    (Code.joinWords 512
                      (Code.joinWords 256
                        268451840
                        (Nat.shiftLeft
                          285212672
                          128))
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          1048576
                          1048576)
                        256)))
                  2048)
                4096)
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          32768
                          (Nat.shiftLeft
                            2594073385365405696
                            128))
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            303412046524374704979968
                            18889465931478580854784)
                          256))
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
                            4503599627370496))))
                    (Code.joinWords 1024
                      (Code.joinWords 256
                        32768
                        (Nat.shiftLeft
                          2305992542795071488
                          128))
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
                  4096)
                8192))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Code.joinWords 1024
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          34816
                          128)
                        256)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          16392
                          128)
                        (Code.joinWords 128
                          16512
                          17544)))
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        65536
                        128)
                      512))
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        65536
                        128)
                      512)
                    2048))
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          32768
                          (Nat.shiftLeft
                            309485009821494602306158592
                            128))
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            309485009821345618480594944
                            128)
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          65536
                          128)
                        512))
                    2048)
                  (Nat.shiftLeft
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
                          128)))
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
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          32768
                          (Nat.shiftLeft
                            149533581377536
                            128))
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            549755813888
                            128)
                          256))
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            65536
                            128)
                          (Code.joinWords 128
                            4503599627370496
                            4503599627370496))
                        512)))
                  (Code.joinWords 2048
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
                        65536
                        128)
                      512)))))))))
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
                        1610645504
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            538968064
                            1048576)
                          256))
                      (Code.joinWords 512
                        (Code.joinWords 128
                          268451840
                          16777216)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            16777216
                            128)
                          269484032)))
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 128
                          32768
                          18432)
                        (Nat.shiftLeft
                          4873629784274063536947200
                          128))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          16777216
                          128)
                        (Nat.shiftLeft
                          4835777065434811553873920
                          128)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          16777216
                          128)
                        (Nat.shiftLeft
                          16842752
                          128))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          65536
                          128)
                        512)))
                  4096))
              (Nat.shiftLeft
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
                        (Nat.shiftLeft
                          65536
                          128)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          65536
                          128)
                        512)))
                  4096)
                8192))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Code.joinWords 1024
                    (Code.joinWords 512
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          4332790137498830962146985984
                          128)
                        (Nat.shiftLeft
                          51200
                          128))
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          4332790137498830962147854344
                          128)
                        (Code.joinWords 128
                          319014718988379809496913694467282731136
                          319014718988379809496913694467282749640)))
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        309485009821345068724781056
                        128)
                      (Nat.shiftLeft
                        309485009821345068725108740
                        128)))
                  (Code.joinWords 1024
                    (Code.joinWords 512
                      (Code.joinWords 128
                        32768
                        18432)
                      (Nat.shiftLeft
                        4873629784274063536947200
                        128))
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        309485009821345068724781056
                        128)
                      (Nat.shiftLeft
                        314320786886779880261877760
                        128))))
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        32768
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            9980891566738378466374189056
                            274877906944)
                          256))
                      (Code.joinWords 512
                        16384
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            65536
                            128)
                          4951760157141521099596496896)))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        32768
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            20769504346789367571472359492681728
                            128)
                          9904127138376090948602953728))
                      (Code.joinWords 512
                        16384
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            20769504346789367571472359492747264
                            128)
                          4952063569188045474301476864)))
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
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        16384
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            65536
                            128)
                          (Code.joinWords 128
                            4503599627370496
                            4503874505277440)))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          65536
                          128)
                        512)))
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
                          20769504346789367571472359492747264
                          128)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          20769504346789367571472359492747264
                          128)
                        512)))))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        16777216
                        128)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          16842752
                          128)
                        (Code.joinWords 128
                          1048576
                          1048576)))
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      (Code.joinWords 128
                        16384
                        16778240)
                      (Nat.shiftLeft
                        18963252907773435838464
                        128))
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        65536
                        128)
                      512))
                  4096))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        65536
                        128)
                      512)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        65536
                        128)
                      512)
                    2048)
                  4096)))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Code.joinWords 512
                    (Code.joinWords 256
                      (Code.joinWords 128
                        16384
                        309485009821345068724797440)
                      (Code.joinWords 128
                        16384
                        16384))
                    (Code.joinWords 256
                      (Nat.shiftLeft
                        309485009821345068724781056
                        128)
                      (Code.joinWords 128
                        16448
                        64)))
                  (Code.joinWords 512
                    (Code.joinWords 128
                      16384
                      309485009821345068724782080)
                    (Nat.shiftLeft
                      309503973074252842143842304
                      128)))
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
                        (Nat.shiftLeft
                          274877906944
                          128)))
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        65536
                        128)
                      512)
                    2048))
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
                  2048)))))
        131072)
      (Code.joinWords 131072
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 1024
                    (Code.joinWords 512
                      (Code.joinWords 256
                        69324642199981295398109052928
                        (Nat.shiftLeft
                          838860800
                          128))
                      (Code.joinWords 256
                        (Code.joinWords 128
                          69596048407668021079434067968
                          3276800)
                        (Nat.shiftLeft
                          271166648751681983013143125537291501568
                          128)))
                    (Code.joinWords 512
                      (Code.joinWords 256
                        19807342860020988056753422336
                        (Nat.shiftLeft
                          16777216
                          128))
                      (Code.joinWords 256
                        77674664501860641886175232
                        (Nat.shiftLeft
                          16777216
                          128))))
                  2048)
                4096)
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        32768
                        (Code.joinWords 256
                          332306998946228968225951765070086144
                          (Nat.shiftLeft
                            38959523483674573012992
                            128)))
                      (Code.joinWords 512
                        16384
                        (Code.joinWords 128
                          332306998946228968225951765070086144
                          65536)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        16384
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
                          69324642199981295394350956544
                          (Nat.shiftLeft
                            271162511140122838072376640297190293504
                            128))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            69324642199981295394350956544
                            57421771425579008)
                          (Nat.shiftLeft
                            271162511140122838072376640297190293504
                            128)))
                      (Code.joinWords 512
                        24759103017162509155276177408
                        (Code.joinWords 128
                          4952062388596424756890189824
                          1125917086711808)))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        29710560942849126597578981376
                        29827224645625179748836573184)
                      (Code.joinWords 512
                        24759103017162509155276177408
                        5029434821643381741482672128))
                    2048))
                (Code.joinWords 2048
                  (Code.joinWords 1024
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          319014718988379809496913694467282749440
                          128)
                        256)
                      (Code.joinWords 256
                        (Code.joinWords 128
                          67553994410557440
                          67553994411474944)
                        (Nat.shiftLeft
                          319014718988379809496913694467282749440
                          128)))
                    (Code.joinWords 512
                      16384
                      (Code.joinWords 128
                        22517998136852544
                        262148)))
                  (Code.joinWords 1024
                    (Code.joinWords 512
                      16384
                      (Code.joinWords 128
                        22517998136852544
                        5629791591989248))
                    (Code.joinWords 512
                      16384
                      (Code.joinWords 128
                        22517998136852544
                        1125917086711808)))))
              (Nat.shiftLeft
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
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        106338239662793269832304564822427598848
                        (Code.joinWords 256
                          332306998946228968225951765070086144
                          (Nat.shiftLeft
                            38959523483674573012992
                            128)))
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
                            309485009821345068724781056
                            128))))
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
                          20769504346789367571472359492747264)))))
                8192)))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 512
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        16777216
                        128)
                      256)
                    (Code.joinWords 256
                      (Code.joinWords 128
                        1048576
                        1114112)
                      (Nat.shiftLeft
                        16777216
                        128)))
                  2048)
                4096)
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        65536
                        128)
                      512)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      16384
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          65536
                          128)
                        (Nat.shiftLeft
                          18889465931478580854784
                          128)))
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        65536
                        128)
                      512))
                  4096)))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      16384
                      (Code.joinWords 128
                        1048640
                        292058824704))
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        65536
                        128)
                      512)
                    2048))
                (Code.joinWords 2048
                  (Code.joinWords 512
                    (Code.joinWords 256
                      16384
                      (Code.joinWords 128
                        16384
                        17408))
                    (Code.joinWords 256
                      (Code.joinWords 128
                        4503599627386880
                        4503599627370496)
                      (Code.joinWords 128
                        16384
                        1024)))
                  (Code.joinWords 512
                    16384
                    (Code.joinWords 128
                      4503599627370560
                      4503891685146624))))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        65536
                        128)
                      512)
                    2048)
                  4096)
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
                  4096)))))
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 1024
                    (Code.joinWords 512
                      1610645504
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          538968064
                          1048576)
                        256))
                    (Code.joinWords 512
                      (Code.joinWords 256
                        268451840
                        (Nat.shiftLeft
                          16777216
                          128))
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          269484032
                          16777216)
                        256)))
                  2048)
                4096)
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        32768
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            606824097552349037330432
                            37778936366556789080064)
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          65536
                          128)
                        512))
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          65536
                          128)
                        (Code.joinWords 128
                          4503599627370496
                          4503599627370496))
                      512))
                  4096)
                8192))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Code.joinWords 1024
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          18432
                          128)
                        256)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          16392
                          128)
                        (Code.joinWords 128
                          32896
                          18504)))
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        65536
                        128)
                      512))
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        65536
                        128)
                      512)
                    2048))
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          32768
                          (Nat.shiftLeft
                            74766790688768
                            128))
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            9980891566738378466374189056
                            274877906944)
                          256))
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
                            309485009821345068724781056))))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        32768
                        (Nat.shiftLeft
                          9904127138376090948602953728
                          256))
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
                            309485009821345068724781056))))
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
                          4503874505277440))))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        32768
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            606824093048749409959936
                            37778931862957161709568)
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
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        65536
                        128)
                      512))))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 512
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        16777216
                        128)
                      256)
                    (Code.joinWords 256
                      (Nat.shiftLeft
                        65536
                        128)
                      (Code.joinWords 128
                        1048576
                        17825792)))
                  2048)
                4096)
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        65536
                        128)
                      512)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      16384
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          65536
                          128)
                        (Code.joinWords 128
                          303412051027974332350464
                          18889470435078208225280)))
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          65536
                          128)
                        (Code.joinWords 128
                          4503599627370496
                          4503599627370496))
                      512))
                  4096)))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 512
                  (Code.joinWords 256
                    16384
                    (Code.joinWords 128
                      16384
                      17408))
                  (Nat.shiftLeft
                    (Code.joinWords 128
                      16448
                      1088)
                    256))
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
                        (Nat.shiftLeft
                          309485009821345343602688000
                          128)))
                    2048)
                  (Nat.shiftLeft
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
                          128)))
                    2048))
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
                        (Code.joinWords 128
                          4503599627370496
                          4503874505277440)))
                    2048)
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
                        309503899287276547305635840)))))))))))

/-- The block word is computed from the verified profile data. -/
theorem word_eq :
    Code.profileWord 64 24 (fun i q => Data.profiles (832 + i) q) = word := by
  decide +kernel

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage013
